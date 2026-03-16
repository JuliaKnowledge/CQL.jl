"""
CQL.jl - Categorical Query Language for Julia

A functional language for data integration that uses category theory
to guarantee correctness of data migrations.

Core pipeline: Parse -> Typecheck -> Evaluate with embedded theorem proving.
"""
module CQL

# External dependencies
using Catlab
using PrecompileTools
import CSV
import XML as XMLParser
import JSON as JSONParser
import Base: collect
import Random
import JavaCall
import JDBC
import ODBC
import ODBC: Tables

# Common utilities
include("Common.jl")
include("Options.jl")
include("Graph.jl")

# Core term AST
include("Term.jl")

# Theory infrastructure
include("Collage.jl")
include("Provers/FreeProver.jl")
include("Provers/CongruenceProver.jl")
include("Provers/OrthogonalProver.jl")
include("Provers/KBCompletionProver.jl")
include("Prover.jl")

# Core CQL types
include("Typeside.jl")
include("Schema.jl")
include("Presentation.jl")
include("Algebra.jl")
include("Instance.jl")
include("Morphism.jl")
include("Mapping.jl")
include("Transform.jl")
include("Query.jl")
include("DataMigration.jl")
include("SchemaColimit.jl")
include("Constraints.jl")

# Parser
include("Parser/Lexer.jl")
include("Parser/ParserCore.jl")
include("Parser/TypesideParser.jl")
include("Parser/SchemaParser.jl")
include("Parser/MappingParser.jl")
include("Parser/InstanceParser.jl")
include("Parser/QueryParser.jl")
include("Parser/TransformParser.jl")
include("Parser/SchemaColimitParser.jl")
include("Parser/ConstraintParser.jl")
include("Parser/ProgramParser.jl")

# Program evaluation
include("Program.jl")

# Catlab integration
include("CatlabInterop.jl")

# CSV import/export
include("CSVSupport.jl")

# JDBC support
include("JdbcSupport.jl")

# ODBC support
include("OdbcSupport.jl")

# RDF support
include("RdfSupport.jl")

# Julia-native DSL
include("DSL/DSL.jl")

# ============================================================================
# Public API
# ============================================================================

# Core types
export CQLTerm, CQLVar, CQLSym, CQLFk, CQLAtt, CQLGen, CQLSk, CQLAgg
export Equation, RawTerm
export Typeside, CQLSchema, CQLInstance, CQLMapping, CQLTransform, CQLQuery
export Presentation, Algebra, Collage, Morphism
export CQLOptions, CQLException

# Expression types
export TypesideExp, SchemaExp, InstanceExp, MappingExp, TransformExp, QueryExp

# Schema colimit
export SchemaColimitResult, CQLConstraints, EGD, chase, is_tgd

# Key functions
export run_program, parse_program
export initial_typeside, sql_typeside, rdf_typeside
export empty_instance, initial_instance, saturated_instance
export identity_mapping, compose_mapping
export identity_transform, compose_transform
export identity_query
export eval_delta_instance, eval_sigma_instance
export eval_delta_transform, eval_sigma_transform
export eval_query_instance, query_provenance
export default_options
export carrier, eval_fk, eval_att, repr_x, nf_entity, nf_type, eval_typeside_term

# Catlab interop
export cql_schema_to_catlab, cql_instance_to_acset

# CSV import/export
export import_csv_instance, export_csv_instance

# ============================================================================
# Macros
# ============================================================================

"""
    cql"..."
    cql\"\"\"...\"\"\"

String macro for inline CQL programs. Returns an `Env` with property access.

# Example
```julia
env = cql\"\"\"
typeside Ty = literal { types String }
schema S = literal : Ty { entities Person }
\"\"\"
env.S  # => CQLSchema
```
"""
macro cql_str(s)
    :(run_program($s))
end

"""
    @cql "..."
    @cql \"\"\"...\"\"\"

Macro for inline CQL programs. Returns an `Env` with property access.

# Example
```julia
env = @cql \"\"\"
typeside Ty = literal { types String }
schema S = literal : Ty { entities Person }
\"\"\"
env.Ty  # => Typeside
```
"""
macro cql(expr)
    :(run_program($(esc(expr))))
end

export @cql_str, @cql

# DSL macros
export @typeside, @schema, @instance, @mapping, @query
export @transform, @schema_colimit, @constraints

# Unicode operators and functional API
export Δ, Σ, ⊔
export coeval, coproduct, distinct, coequalize, to_query

# ============================================================================
# Precompilation workloads
# ============================================================================

@setup_workload begin
    # Workload 1: core constructs (typeside, schema, instance, mapping, query,
    # eval, sigma, delta, coproduct, transform, constraints)
    _pc_main = """
typeside Ty = literal {
  types String Integer
  constants "1" "2" : Integer "a" "b" : String
}
schema S = literal : Ty {
  entities A B
  foreign_keys f : A -> B
  attributes a1 : A -> String b1 : B -> Integer
  observation_equations forall x. a1(x) = a1(x)
}
schema T = literal : Ty {
  entities C
  attributes c1 : C -> String c2 : C -> Integer
}
instance I = literal : S {
  generators a1 a2 : A b1 b2 : B
  equations f(a1) = b1 f(a2) = b2 a1(a1) = "a" a1(a2) = "b" b1(b1) = "1" b1(b2) = "2"
}
mapping F = literal : S -> T {
  entity A -> C
  foreign_keys f -> identity
  entity B -> C
  attributes a1 -> c1 b1 -> c2
}
query Q = literal : S -> T {
  entity C -> {from a:A b:B where f(a) = b attributes c1 -> a1(a) c2 -> b1(b)}
}
instance J = eval Q I
instance K = sigma F I
instance L = delta F J
transform t1 = identity I
transform t2 = sigma F t1
instance N = coproduct I + I : S
constraints C = literal : S { forall a:A -> exists b:B where f(a) = b }
"""
    # Workload 2: coeval
    _pc_coeval = """
typeside Ty = literal { types String }
schema S = literal : Ty { entities A attributes a1 : A -> String }
instance I = literal : S { generators x y : A equations a1(x) = "hi" a1(y) = "lo" }
query Q = literal : S -> S { entity A -> {from a:A attributes a1 -> a1(a)} }
instance I2 = coeval Q I
"""
    # Workload 3: schema_colimit
    _pc_colimit = raw"""
typeside Ty = literal { types String }
schema S1 = literal : Ty { entities A attributes a1 : A -> String }
schema S2 = literal : Ty { entities B attributes b1 : B -> String }
schema_colimit SC = quotient S1 + S2 : Ty {
  entity_equations S1.A = S2.B
  options simplify_names = true
}
"""
    # Workload 4: FK chains, path equations, KB completion prover, coequalize,
    # frozen, chase, distinct, typesideOf, schemaOf, toQuery
    _pc_advanced = """
typeside Ty = literal {
  types String Nat
  constants zero : Nat
  functions succ : Nat -> Nat plus : Nat, Nat -> Nat
  equations forall x. plus(zero, x) = x forall x, y. plus(succ(x),y) = succ(plus(x,y))
  options prover = completion
}
schema S2 = literal : Ty {
  entities E D
  foreign_keys mgr : E -> E dep : E -> D sec : D -> E
  path_equations E.mgr.mgr = E.mgr E.mgr.dep = E.dep D.sec.dep = D
  attributes en : E -> String dn : D -> String
  observation_equations forall e. en(mgr(e)) = en(e)
}
typeside Ty2 = typesideOf S2
schema S3 = schemaOf (empty : S2)
instance I2 = literal : S2 {
  generators e1 : E d1 : D
  equations mgr(e1) = e1 dep(e1) = d1 sec(d1) = e1 en(e1) = "Al" dn(d1) = "Sales"
  options prover = completion
}
instance I3 = delta (identity S2) I2
instance I4 = sigma (identity S2) I2 { options prover = completion }
instance I5 = coeval (identity S2) I2
instance I6 = coequalize (identity I2) (identity I2) { options prover = completion }
constraints C2 = literal : S2 {
  forall e:E -> exists d:D where dep(e) = d
}
instance I7 = chase C2 I3
query Q2 = toQuery (identity S2)
instance I8 = eval Q2 I2
instance I9 = distinct I2
transform td = distinct (identity I2)
"""
    # Workload 5: query composition, counit_query, Bool typeside (covers Compose.cql paths)
    _pc_compose = """
typeside Ty = literal {
  types Bool String
  constants tru fal : Bool
  functions and : Bool, Bool -> Bool not : Bool -> Bool
  equations
    forall x. and(tru, x) = x
    forall x. and(fal, x) = fal
    forall x. and(x, x) = x
    not(tru) = fal not(fal) = tru
  options prover = completion
}
schema S = literal : Ty {
  entities E
  attributes att : E -> Bool
}
query Q1 = literal : S -> S {
  entity E -> {from x:E attributes att -> att(x)}
}
query Q2 = literal : S -> S {
  entity E -> {from x:E attributes att -> att(x)}
}
query Q3 = [Q1 ; Q2]
instance I = literal : S {
  generators e1 e2 : E
  equations att(e1) = tru att(e2) = fal
  options prover = completion
}
instance J = eval Q1 I
instance K = coeval Q1 I
transform t = counit_query Q1 I
transform t2 = coeval Q1 (identity I)
"""
    @compile_workload begin
        run_program(_pc_main)
        run_program(_pc_coeval)
        run_program(_pc_colimit)
        run_program(_pc_advanced)
        run_program(_pc_compose)
    end
end

end # module
