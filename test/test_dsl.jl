using CQL
using Test

@testset "CQL.jl DSL" begin

    # ─── Reference: all results computed via cql"..." string macro ────────────
    ref = cql"""
    typeside Ty = literal {
        types String Int
        constants Alice Bob : String  CS Math : String
        constants "100" "250" : Int
    }

    schema S = literal : Ty {
        entities Employee Department
        foreign_keys
            worksIn : Employee -> Department
            manager : Employee -> Employee
        attributes
            ename : Employee -> String
            dname : Department -> String
            budget : Department -> Int
        path_equations
            Employee.manager.manager = Employee.manager
    }

    instance I = literal : S {
        generators e1 e2 e3 : Employee  d1 d2 : Department
        equations
            worksIn(e1) = d1  worksIn(e2) = d1  worksIn(e3) = d2
            manager(e1) = e2  manager(e2) = e2  manager(e3) = e3
            ename(e1) = Alice  ename(e2) = Bob  ename(e3) = Alice
            dname(d1) = CS  dname(d2) = Math
            budget(d1) = "100"  budget(d2) = "250"
    }

    schema T = literal : Ty {
        entities EmpDept
        attributes
            emp_name : EmpDept -> String
            dept_name : EmpDept -> String
    }

    query Q = literal : S -> T {
        entity EmpDept -> {
            from e:Employee
            attributes
                emp_name -> ename(e)
                dept_name -> dname(worksIn(e))
        }
    }

    instance QI = eval Q I

    mapping F = literal : S -> S {
        entity Employee -> Employee
        entity Department -> Department
        foreign_keys
            worksIn -> worksIn
            manager -> manager
        attributes
            ename -> ename
            dname -> dname
            budget -> budget
    }

    instance DeltaI = delta F I
    instance SigmaI = sigma F I
    """

    # ─── @typeside ───────────────────────────────────────────────────────────
    @testset "@typeside" begin
        Ty = @typeside begin
            String::Ty
            Int::Ty
            Alice::String
            Bob::String
            CS::String
            Math::String
            "100"::Int
            "250"::Int
        end

        @test Ty.tys == ref.Ty.tys
        @test Ty.syms == ref.Ty.syms
    end

    @testset "@typeside multi-arg functions (vignette 12 regression)" begin
        Ty = @typeside begin
            Str::Ty
            Bool::Ty
            contains(::Str, ::Str)::Bool
            count_words(::Str)::Str
        end
        @test Ty.syms[:contains] == ([:Str, :Str], :Bool)
        @test Ty.syms[:count_words] == ([:Str], :Str)
    end

    # ─── @schema ─────────────────────────────────────────────────────────────
    @testset "@schema" begin
        Ty = ref.Ty

        S = @schema Ty begin
            @entities Employee, Department
            worksIn : Employee → Department
            manager : Employee → Employee
            ename : Employee ⇒ String
            dname : Department ⇒ String
            budget : Department ⇒ Int
            @path_eq Employee  manager.manager == manager
        end

        @test S.ens == ref.S.ens
        @test Set(keys(S.fks)) == Set(keys(ref.S.fks))
        @test Set(keys(S.atts)) == Set(keys(ref.S.atts))
        # Check FK types match
        for (k, v) in S.fks
            @test ref.S.fks[k] == v
        end
        for (k, v) in S.atts
            @test ref.S.atts[k] == v
        end
    end

    # ─── @instance ───────────────────────────────────────────────────────────
    @testset "@instance" begin
        S = ref.S

        I = @instance S begin
            e1::Employee; e2::Employee; e3::Employee
            d1::Department; d2::Department
            worksIn(e1) == d1; worksIn(e2) == d1; worksIn(e3) == d2
            manager(e1) == e2; manager(e2) == e2; manager(e3) == e3
            ename(e1) == Alice; ename(e2) == Bob; ename(e3) == Alice
            dname(d1) == CS; dname(d2) == Math
            budget(d1) == "100"; budget(d2) == "250"
        end

        # Compare carrier sizes
        for en in S.ens
            @test length(I.algebra.en[en]) == length(ref.I.algebra.en[en])
        end
        # Compare generator count
        @test length(I.pres.gens) == length(ref.I.pres.gens)
    end

    # ─── @query + Q(I) ───────────────────────────────────────────────────────
    @testset "@query and Q(I)" begin
        S = ref.S
        I = ref.I

        T = @schema ref.Ty begin
            @entities EmpDept
            emp_name : EmpDept ⇒ String
            dept_name : EmpDept ⇒ String
        end

        Q = @query S → T begin
            @entity EmpDept begin
                @from e::Employee
                @return emp_name => ename(e), dept_name => e.worksIn.dname
            end
        end

        QI = Q(I)

        # Same number of result rows
        @test length(QI.algebra.en[:EmpDept]) == length(ref.QI.algebra.en[:EmpDept])
    end

    # ─── Unicode operators: Δ, Σ ─────────────────────────────────────────────
    @testset "Δ and Σ operators" begin
        S = ref.S
        I = ref.I
        F = identity_mapping(S)

        deltaI = Δ(F)(I)
        sigmaI = Σ(F)(I)

        # Delta of identity should preserve carrier sizes
        for en in S.ens
            @test length(deltaI.algebra.en[en]) == length(I.algebra.en[en])
        end
        # Sigma of identity should preserve carrier sizes
        for en in S.ens
            @test length(sigmaI.algebra.en[en]) == length(I.algebra.en[en])
        end
    end

    # ─── ∘ composition ───────────────────────────────────────────────────────
    @testset "∘ composition" begin
        S = ref.S
        F = identity_mapping(S)

        # Mapping composition
        F2 = F ∘ F
        @test F2.ens == F.ens
    end

    # ─── @mapping ────────────────────────────────────────────────────────────
    @testset "@mapping" begin
        S = ref.S

        F = @mapping S → S begin
            Employee → Employee
            Department → Department
            worksIn → worksIn
            manager → manager
            ename → ename
            dname → dname
            budget → budget
        end

        @test F.ens == ref.F.ens
    end

    # ─── Coproduct (⊔) ──────────────────────────────────────────────────────
    @testset "⊔ coproduct" begin
        I = ref.I
        N = I ⊔ I
        for en in ref.S.ens
            @test length(N.algebra.en[en]) == 2 * length(I.algebra.en[en])
        end
        N3 = coproduct(I, I, I)
        for en in ref.S.ens
            @test length(N3.algebra.en[en]) == 3 * length(I.algebra.en[en])
        end
    end

    # ─── distinct ────────────────────────────────────────────────────────────
    @testset "distinct" begin
        # Use a simple schema without path equations for distinct test
        simple_env = cql"""
        typeside Ty = literal { types String constants A B : String }
        schema S = literal : Ty { entities E attributes name : E -> String }
        instance I = literal : S { generators e1 e2 : E equations name(e1) = A name(e2) = B }
        """
        I_simple = simple_env.I
        D = distinct(I_simple)
        @test length(D.algebra.en[:E]) == length(I_simple.algebra.en[:E])
    end

    # ─── coeval ──────────────────────────────────────────────────────────────
    @testset "coeval" begin
        I = ref.I
        Q_id = identity_query(ref.S)
        I_coeval = coeval(Q_id, I)
        for en in ref.S.ens
            @test length(I_coeval.algebra.en[en]) == length(I.algebra.en[en])
        end
    end

    # ─── to_query ────────────────────────────────────────────────────────────
    @testset "to_query" begin
        F = identity_mapping(ref.S)
        Q = to_query(F)
        @test Q isa CQLQuery
        J = Q(ref.I)
        for en in ref.S.ens
            @test length(J.algebra.en[en]) == length(ref.I.algebra.en[en])
        end
    end

    # ─── @constraints ────────────────────────────────────────────────────────
    @testset "@constraints" begin
        C = @constraints ref.S "forall e:Employee -> exists d:Department where worksIn(e) = d"
        @test C isa CQLConstraints
        @test length(C.egds) == 1
    end

    # ─── @schema_colimit ─────────────────────────────────────────────────────
    @testset "@schema_colimit" begin
        Ty = @typeside begin
            String::Ty
        end
        S1 = @schema Ty begin
            @entities A
            a1 : A ⇒ String
        end
        S2 = @schema Ty begin
            @entities B
            b1 : B ⇒ String
        end

        SC = @schema_colimit Ty begin
            @schemas S1, S2
            S1.A == S2.B
            @options simplify_names = true
        end
        @test SC isa SchemaColimitResult
        @test :A in SC.schema.ens
        @test length(SC.schema.ens) == 1  # A and B merged
    end

    # ─── Empty / minimal constructs ──────────────────────────────────────────
    @testset "Minimal constructs" begin
        Ty = @typeside begin
            String::Ty
        end
        @test :String in Ty.tys

        S = @schema Ty begin
            @entities Person
            name : Person ⇒ String
        end
        @test :Person in S.ens
        @test haskey(S.atts, :name)

        I = @instance S begin
            p1::Person
            name(p1) == "hello"
        end
        @test length(I.algebra.en[:Person]) == 1
    end

end
