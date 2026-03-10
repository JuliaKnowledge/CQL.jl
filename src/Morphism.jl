"""
Morphisms between collages: translating terms along mappings.
"""

"""A morphism between collages."""
struct Morphism
    m_src::Collage
    m_dst::Collage
    m_ens::Dict{Symbol, Symbol}                    # entity -> entity
    m_fks::Dict{Symbol, CQLTerm}                   # fk -> path term (Var/Fk chain)
    m_atts::Dict{Symbol, CQLTerm}                  # att -> type-side term
    m_gens::Dict{Symbol, CQLTerm}                  # gen -> entity-side term
    m_sks::Dict{Symbol, CQLTerm}                   # sk -> type-side term
end

"""Check that the morphism is total (all source symbols are mapped)."""
function check_morphism_doms(mor::Morphism)
    for en in mor.m_src.cens
        haskey(mor.m_ens, en) || throw(CQLException("No entity mapping for $en"))
    end
    for fk in keys(mor.m_src.cfks)
        haskey(mor.m_fks, fk) || throw(CQLException("No fk mapping for $fk"))
    end
    for att in keys(mor.m_src.catts)
        haskey(mor.m_atts, att) || throw(CQLException("No att mapping for $att"))
    end
    for gen in keys(mor.m_src.cgens)
        haskey(mor.m_gens, gen) || throw(CQLException("No gen mapping for $gen"))
    end
    for sk in keys(mor.m_src.csks)
        haskey(mor.m_sks, sk) || throw(CQLException("No sk mapping for $sk"))
    end
end

"""Translate a term along a morphism (full translation including type-side)."""
function translate_term(mor::Morphism, t::CQLTerm)::CQLTerm
    if t isa CQLVar
        t
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[translate_term(mor, a) for a in t.args])
    elseif t isa CQLGen
        mor.m_gens[t.gen]
    elseif t isa CQLSk
        mor.m_sks[t.sk]
    elseif t isa CQLAtt
        subst_term(mor.m_atts[t.att], translate_term(mor, t.arg))
    elseif t isa CQLFk
        subst_term(mor.m_fks[t.fk], translate_term(mor, t.arg))
    else
        error("Unknown term type in translate_term")
    end
end

"""Translate an entity-side term along a morphism (only Var/Fk/Gen)."""
function translate_entity_term(mor::Morphism, t::CQLTerm)::CQLTerm
    if t isa CQLVar
        t
    elseif t isa CQLFk
        x = translate_entity_term(mor, t.arg)
        subst_term(mor.m_fks[t.fk], x)
    elseif t isa CQLGen
        mor.m_gens[t.gen]
    else
        error("Cannot translate entity-side: $t")
    end
end

"""Typecheck a morphism: verify all mappings are well-typed."""
function typecheck_morphism(mor::Morphism)
    check_morphism_doms(mor)

    trans_en(en) = mor.m_ens[en]

    for (en, en2) in mor.m_ens
        en in mor.m_src.cens || throw(CQLException("Bad entity mapping: $en"))
        en2 in mor.m_dst.cens || throw(CQLException("Bad entity mapping target: $en2"))
    end

    for (fk, term) in mor.m_fks
        haskey(mor.m_src.cfks, fk) || throw(CQLException("Bad fk mapping: $fk"))
        (src, tgt) = mor.m_src.cfks[fk]
        src2 = trans_en(src)
        tgt2 = trans_en(tgt)
        ctx = Ctx(Symbol("_unit") => Right(src2))
        t = type_of_term(mor.m_dst, ctx, term)
        t == Right(tgt2) || throw(CQLException("Ill typed fk mapping $fk: expected $tgt2, got $t"))
    end

    for (att, term) in mor.m_atts
        haskey(mor.m_src.catts, att) || throw(CQLException("Bad att mapping: $att"))
        (src, tgt) = mor.m_src.catts[att]
        src2 = trans_en(src)
        ctx = Ctx(Symbol("_unit") => Right(src2))
        t = type_of_term(mor.m_dst, ctx, term)
        t == Left(tgt) || throw(CQLException("Ill typed att mapping $att: expected $tgt, got $t"))
    end

    for (gen, term) in mor.m_gens
        haskey(mor.m_src.cgens, gen) || throw(CQLException("Bad gen mapping: $gen"))
        en = mor.m_src.cgens[gen]
        en2 = trans_en(en)
        t = type_of_term(mor.m_dst, Ctx(), term)
        t == Right(en2) || throw(CQLException("Ill typed gen mapping $gen: expected $en2, got $t"))
    end

    for (sk, term) in mor.m_sks
        haskey(mor.m_src.csks, sk) || throw(CQLException("Bad sk mapping: $sk"))
        ty = mor.m_src.csks[sk]
        t = type_of_term(mor.m_dst, Ctx(), term)
        t == Left(ty) || throw(CQLException("Ill typed sk mapping $sk: expected $ty, got $t"))
    end
end
