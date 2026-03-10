"""
Algebras: semantic models of schemas.

An algebra interprets a schema by providing:
- Carrier sets for each entity
- Interpretation functions for foreign keys, attributes, generators, Skolems
- A type algebra with equations
"""

"""
A CQL algebra parameterized by carrier types X (entity elements) and Y (type elements).

Fields:
- schema: the schema being modeled
- en: entity -> Set of carrier elements (X)
- gen: generator_name -> X
- fk: fk_name -> X -> X
- repr: X -> CQLTerm (reverse of gen/fk interpretation)
- ty: type_name -> Set of Y
- nf_y: Either{Symbol, Tuple{X, Symbol}} -> CQLTerm (Skolem/attr normalization)
- repr_y: Y -> CQLTerm (reverse of type interpretation)
- teqs: Set{Equation} (type algebra equations)
"""
struct Algebra{X, Y}
    schema::CQLSchema
    en::Dict{Symbol, Set{X}}           # entity -> carrier set
    gen::Dict{Symbol, X}               # generator -> element
    fk::Dict{Symbol, Dict{X, X}}       # fk -> (element -> element)
    repr_x::Dict{X, CQLTerm}           # element -> term representation
    ty::Dict{Symbol, Set{Y}}           # type -> type carrier set
    nf_y::Function                      # (Left(sk) | Right((x, att))) -> CQLTerm
    repr_y::Dict{Y, CQLTerm}           # type element -> term representation
    teqs::Set{Equation}                 # type algebra equations
end

"""Get the carrier set for an entity."""
carrier(alg::Algebra, en::Symbol) = alg.en[en]

"""Evaluate a generator."""
eval_gen(alg::Algebra, g::Symbol) = alg.gen[g]

"""Evaluate a foreign key on an element."""
eval_fk(alg::Algebra, f::Symbol, x) = alg.fk[f][x]

"""Get the representation term for a carrier element."""
repr_x(alg::Algebra, x) = alg.repr_x[x]

"""Evaluate an entity-side term to a carrier element."""
function nf_entity(alg::Algebra, t::CQLTerm)
    if t isa CQLGen
        return eval_gen(alg, t.gen)
    elseif t isa CQLFk
        return eval_fk(alg, t.fk, nf_entity(alg, t.arg))
    else
        error("Cannot evaluate entity-side term: $t")
    end
end

"""Evaluate a type-side term to a type algebra term."""
function nf_type(alg::Algebra, t::CQLTerm)::CQLTerm
    if t isa CQLSym
        normalized = CQLSym(t.sym, CQLTerm[nf_type(alg, a) for a in t.args])
        # Try typeside evaluation if external functions are available
        ts = alg.schema.typeside
        if !isempty(t.args) && !isempty(ts.java_fns)
            result = try_eval_typeside_sym(ts, normalized)
            result !== nothing && return result
        end
        return normalized
    elseif t isa CQLAtt
        x = nf_entity(alg, _down_entity(t.arg))
        alg.nf_y(Right((x, t.att)))
    elseif t isa CQLSk
        alg.nf_y(Left(t.sk))
    else
        error("Cannot evaluate type-side term: $t")
    end
end

"""Recursively evaluate typeside functions in a term using the schema's typeside."""
function eval_typeside_term(ts::Typeside, t::CQLTerm)::CQLTerm
    isempty(ts.java_fns) && return t
    if t isa CQLSym && !isempty(t.args)
        # First recursively evaluate arguments
        evaled_args = CQLTerm[eval_typeside_term(ts, a) for a in t.args]
        evaled = CQLSym(t.sym, evaled_args)
        result = try_eval_typeside_sym(ts, evaled)
        return result !== nothing ? result : evaled
    end
    t
end

"""Evaluate a schema entity-side term with a free variable, given a value."""
function eval_schema_term_entity(alg::Algebra, x, t::CQLTerm)
    if t isa CQLVar
        x
    elseif t isa CQLFk
        eval_fk(alg, t.fk, eval_schema_term_entity(alg, x, t.arg))
    else
        error("Bad entity-side schema term: $t")
    end
end

"""Evaluate a schema type-side term with a free variable, given a value."""
function eval_schema_term_type(alg::Algebra, x, t::CQLTerm)::CQLTerm
    if t isa CQLAtt
        x_inner = eval_schema_term_entity(alg, x, _down_entity(t.arg))
        eval_att(alg, t.att, x_inner)
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[eval_schema_term_type(alg, x, a) for a in t.args])
    else
        error("Bad type-side schema term: $t")
    end
end

"""Evaluate an attribute on a carrier element."""
function eval_att(alg::Algebra, att::Symbol, x)::CQLTerm
    alg.nf_y(Right((x, att)))
end

"""Reverse-evaluate a type algebra term back to an instance term."""
function repr_type(alg::Algebra, t::CQLTerm)::CQLTerm
    if t isa CQLSym
        CQLSym(t.sym, CQLTerm[repr_type(alg, a) for a in t.args])
    elseif t isa CQLSk
        alg.repr_y[t.sk]
    else
        error("Cannot repr type term: $t")
    end
end

"""Downcast a term to entity-side (strip type annotations)."""
function _down_entity(t::CQLTerm)::CQLTerm
    if t isa CQLVar
        t
    elseif t isa CQLGen
        t
    elseif t isa CQLFk
        CQLFk(t.fk, _down_entity(t.arg))
    else
        error("Cannot downcast to entity-side: $t")
    end
end

# ============================================================================
# Type algebra generators
# ============================================================================

"""A generator for the type algebra: either a Skolem or an (element, attribute) pair."""
struct TalgGen
    val::Any  # Left{Symbol} or Right{Tuple{<:Any, Symbol}}
end

Base.:(==)(a::TalgGen, b::TalgGen) = a.val == b.val
Base.hash(a::TalgGen, h::UInt) = hash(a.val, h)

function Base.show(io::IO, g::TalgGen)
    if is_left(g.val)
        print(io, get_left(g.val))
    else
        (t, att) = get_right(g.val)
        print(io, t, ".", att)
    end
end

# ============================================================================
# Algebra simplification
# ============================================================================

"""Check if a type algebra element should be removed after simplification."""
_is_removed_talg_elem(y::Symbol, removed_sks::Set{Symbol}) = y in removed_sks
function _is_removed_talg_elem(y::TalgGen, removed_sks::Set{Symbol})
    if is_left(y.val)
        return get_left(y.val) in removed_sks
    else
        # Right((carrier_elem, att)) → Skolem name is "carrier_elem.att"
        (x, att) = get_right(y.val)
        return Symbol(string(x, ".", att)) in removed_sks
    end
end
_is_removed_talg_elem(y, removed_sks::Set{Symbol}) = false

"""Simplify an algebra's type algebra by inlining equations of the form sk = term."""
function simplify_algebra(alg::Algebra{X,Y}) where {X,Y}
    # Convert teqs to theory for simplification
    theory = Set{Tuple{Ctx, Equation}}()
    for eq in alg.teqs
        push!(theory, (Ctx(), eq))
    end

    (simplified, replacements) = simplify_theory(theory)

    new_teqs = Set{Equation}(eq for (_, eq) in simplified)

    # Filter type carrier sets
    removed_sks = Set{Symbol}()
    for (h, _) in replacements
        if h.kind == H_SK
            push!(removed_sks, h.name)
        end
    end

    new_ty = Dict{Symbol, Set{Y}}()
    for (ty_name, ys) in alg.ty
        new_ty[ty_name] = Set{Y}(y for y in ys if !_is_removed_talg_elem(y, removed_sks))
    end

    # Build typeside rewrite rules from ground equations
    ts_rules = _build_typeside_rules(alg.schema.typeside)

    # Memoize nf_y to avoid recomputing through stacked closure chains
    # (each chase iteration adds a layer; memoization makes repeated lookups O(1))
    inner_nf_y = alg.nf_y
    nf_cache = Dict{Any, CQLTerm}()
    new_nf_y = function(e)
        get!(nf_cache, e) do
            _reduce_typeside(ts_rules, replace_repeatedly(replacements, inner_nf_y(e)))
        end
    end

    Algebra{X,Y}(alg.schema, alg.en, alg.gen, alg.fk, alg.repr_x,
                  new_ty, new_nf_y, alg.repr_y, new_teqs)
end

"""Build rewrite rules from ground typeside equations (lhs → rhs where lhs is larger)."""
function _build_typeside_rules(ts::Typeside)
    rules = Tuple{CQLTerm,CQLTerm}[]
    for (ctx, eq) in ts.eqs
        isempty(ctx) || continue
        # Orient: larger side → smaller side
        ls = term_size(eq.lhs)
        rs = term_size(eq.rhs)
        if ls > rs
            push!(rules, (eq.lhs, eq.rhs))
        elseif rs > ls
            push!(rules, (eq.rhs, eq.lhs))
        end
    end
    rules
end

"""Reduce a type-side term by applying typeside ground rewrite rules to fixed point."""
function _reduce_typeside(rules::Vector{Tuple{CQLTerm,CQLTerm}}, t::CQLTerm)::CQLTerm
    isempty(rules) && return t
    for _ in 1:100
        t2 = _rewrite_once_typeside(rules, t)
        t2 == t && return t
        t = t2
    end
    t
end

"""Try one rewrite step anywhere in a term using typeside rules."""
function _rewrite_once_typeside(rules::Vector{Tuple{CQLTerm,CQLTerm}}, t::CQLTerm)::CQLTerm
    # Try matching at root
    for (lhs, rhs) in rules
        if t == lhs
            return rhs
        end
    end
    # Recurse into subterms
    if t isa CQLSym && !isempty(t.args)
        for i in eachindex(t.args)
            new_arg = _rewrite_once_typeside(rules, t.args[i])
            if new_arg != t.args[i]
                new_args = copy(t.args)
                new_args[i] = new_arg
                return CQLSym(t.sym, new_args)
            end
        end
    end
    t
end
