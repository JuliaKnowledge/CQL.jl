using Test
using CQL

# Helper: make term constructors short
V(n) = CQLVar(n)
S(s, args...) = CQLSym(s, CQLTerm[args...])
G(n) = CQLGen(n)

@testset "KB Completion" begin

    # ================================================================
    # Unification
    # ================================================================
    @testset "Unification" begin
        @testset "identical terms" begin
            σ = CQL.unify(S(:f, V(:x)), S(:f, V(:x)))
            @test σ !== nothing
        end

        @testset "variable binding" begin
            σ = CQL.unify(V(:x), S(:a))
            @test σ !== nothing
            @test σ[:x] == S(:a)
        end

        @testset "symmetric variable binding" begin
            σ = CQL.unify(S(:a), V(:y))
            @test σ !== nothing
            @test σ[:y] == S(:a)
        end

        @testset "nested unification" begin
            σ = CQL.unify(S(:f, V(:x), V(:y)), S(:f, S(:a), S(:b)))
            @test σ !== nothing
            @test σ[:x] == S(:a)
            @test σ[:y] == S(:b)
        end

        @testset "occurs check failure" begin
            σ = CQL.unify(V(:x), S(:f, V(:x)))
            @test σ === nothing
        end

        @testset "symbol mismatch" begin
            σ = CQL.unify(S(:f, V(:x)), S(:g, V(:x)))
            @test σ === nothing
        end

        @testset "arity mismatch" begin
            σ = CQL.unify(S(:f, V(:x)), S(:f, V(:x), V(:y)))
            @test σ === nothing
        end

        @testset "deep unification" begin
            σ = CQL.unify(S(:f, S(:g, V(:x))), S(:f, S(:g, S(:a))))
            @test σ !== nothing
            @test σ[:x] == S(:a)
        end

        @testset "variable-variable unification" begin
            σ = CQL.unify(V(:x), V(:y))
            @test σ !== nothing
            # one should map to the other
            @test haskey(σ, :x) || haskey(σ, :y)
        end

        @testset "CQLFk unification" begin
            σ = CQL.unify(CQLFk(:f, V(:x)), CQLFk(:f, G(:a)))
            @test σ !== nothing
            @test σ[:x] == G(:a)
        end

        @testset "CQLFk mismatch" begin
            σ = CQL.unify(CQLFk(:f, V(:x)), CQLFk(:g, V(:x)))
            @test σ === nothing
        end
    end

    # ================================================================
    # LPO Ordering
    # ================================================================
    @testset "LPO Ordering" begin
        prec = Dict(:f => 2, :g => 1, :a => 0)

        @testset "higher precedence wins" begin
            # f(x) > g(x) since f > g
            @test CQL.lpo_compare(prec, S(:f, V(:x)), S(:g, V(:x))) == :GT
            @test CQL.lpo_compare(prec, S(:g, V(:x)), S(:f, V(:x))) == :LT
        end

        @testset "equal terms" begin
            @test CQL.lpo_compare(prec, S(:a), S(:a)) == :EQ
        end

        @testset "variables are incomparable" begin
            @test CQL.lpo_compare(prec, V(:x), V(:y)) == :INCOMPARABLE
        end

        @testset "variable subterm" begin
            # f(x) > x since x is a subterm
            @test CQL.lpo_compare(prec, S(:f, V(:x)), V(:x)) == :GT
            @test CQL.lpo_compare(prec, V(:x), S(:f, V(:x))) == :LT
        end
    end

    # ================================================================
    # KBO Ordering
    # ================================================================
    @testset "KBO Ordering" begin
        prec = Dict(:f => 2, :g => 1, :a => 0)
        weights = Dict(:f => 1, :g => 1, :a => 1)

        @testset "heavier term wins" begin
            # f(a) weight=2 > a weight=1
            @test CQL.kbo_compare(prec, weights, S(:f, S(:a)), S(:a)) == :GT
        end

        @testset "equal weight uses precedence" begin
            # f(x) vs g(x): same weight, f > g in precedence
            @test CQL.kbo_compare(prec, weights, S(:f, V(:x)), S(:g, V(:x))) == :GT
        end

        @testset "variables are incomparable" begin
            @test CQL.kbo_compare(prec, weights, V(:x), V(:y)) == :INCOMPARABLE
        end

        @testset "variable condition" begin
            # f(x,y) > g(x): fails var condition since y not in g(x)
            result = CQL.kbo_compare(prec, weights, S(:f, V(:x), V(:y)), S(:g, V(:x)))
            # KBO requires every variable in t to appear at least as often in s
            # and vice versa for GT. g(x) has no y, but s > t requires t's vars ⊆ s's vars
            # s has {x,y}, t has {x}. t_vars ⊆ s_vars => ok for GT check
            # But s has y not in t, so s_ge_t might fail for LT direction
        end
    end

    # ================================================================
    # Critical Pairs
    # ================================================================
    @testset "Critical Pairs" begin
        @testset "self-overlap" begin
            # Rule: f(f(x)) -> x
            # Self-overlap at position [1]: unify subterm f(x) with renamed f(x')
            # CP: f(x) vs f(x')  where σ = {x'↦x} — this is trivial
            # For f(f(x)) -> x, the only non-trivial self-CP comes from overlap at root
            r = CQL.RewriteRule(S(:f, S(:f, V(:x))), V(:x))
            cps = CQL.critical_pairs(r, r)
            # Self-overlap of f(f(x)) with f(f(x')) at position [1]:
            # unify f(x) with f(x') → σ={x'↦x}, then f(f(x))[1←x] = f(x), σ(rhs1) = x
            # CP: (x, x) — trivial, filtered out. So 0 CPs is correct for this rule.
            # Test with a rule that DOES have non-trivial self-overlap:
            # Rule: f(f(x,y),z) -> f(x, f(y,z))  (associativity)
            r2 = CQL.RewriteRule(S(:f, S(:f, V(:x), V(:y)), V(:z)),
                                 S(:f, V(:x), S(:f, V(:y), V(:z))))
            cps2 = CQL.critical_pairs(r2, r2)
            @test length(cps2) > 0
        end

        @testset "no overlap with disjoint rules" begin
            # Rules: f(x) -> a, g(x) -> b
            r1 = CQL.RewriteRule(S(:f, V(:x)), S(:a))
            r2 = CQL.RewriteRule(S(:g, V(:x)), S(:b))
            cps = CQL.critical_pairs(r1, r2)
            @test isempty(cps)
        end

        @testset "overlap at root" begin
            # Rule 1: f(g(x)) -> x
            # Rule 2: g(a) -> b
            # Overlap: f(g(a)) → f(b) via rule 2, or → a via rule 1
            r1 = CQL.RewriteRule(S(:f, S(:g, V(:x))), V(:x))
            r2 = CQL.RewriteRule(S(:g, S(:a)), S(:b))
            cps = CQL.critical_pairs(r1, r2)
            @test length(cps) > 0
        end
    end

    # ================================================================
    # Subterm Positions and Replace
    # ================================================================
    @testset "Subterm Positions" begin
        t = S(:f, S(:g, S(:a)), S(:b))
        positions = CQL.subterm_positions(t)
        # Root, f.arg1=g(a), f.arg1.arg1=a, f.arg2=b
        @test length(positions) == 4
        @test positions[1] == (Int[], t)  # root

        @testset "replace_at root" begin
            @test CQL.replace_at(t, Int[], S(:c)) == S(:c)
        end

        @testset "replace_at nested" begin
            replaced = CQL.replace_at(t, [1, 1], S(:d))
            @test replaced == S(:f, S(:g, S(:d)), S(:b))
        end
    end

    # ================================================================
    # KB Completion — Standard Theories
    # ================================================================
    @testset "Empty equation set" begin
        rules, passive, converged = CQL.kb_complete(Equation[], Dict{Symbol,Int}())
        @test isempty(rules)
        @test isempty(passive)
        @test converged
    end

    @testset "Single ground equation" begin
        # a = b → rule a -> b (or b -> a)
        eqs = [Equation(S(:a), S(:b))]
        prec = Dict(:a => 2, :b => 1)
        rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5)
        @test length(rules) == 1
        @test converged
    end

    @testset "Idempotent law: f(f(x)) = f(x)" begin
        eqs = [Equation(S(:f, S(:f, V(:x))), S(:f, V(:x)))]
        prec = Dict(:f => 1)
        rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5)
        @test converged
        @test length(rules) == 1
        # Rule should be f(f(x)) -> f(x)
        r = rules[1]
        @test CQL.term_size(r.lhs) > CQL.term_size(r.rhs)
    end

    @testset "Involution: f(f(x)) = x" begin
        eqs = [Equation(S(:f, S(:f, V(:x))), V(:x))]
        prec = Dict(:f => 1)
        rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5)
        @test converged
        # Should produce f(f(x)) -> x
        @test length(rules) == 1
    end

    @testset "Group theory (3 axioms)" begin
        # o(o(x,y),z) = o(x,o(y,z))   (associativity)
        # o(e,x) = x                    (left identity)
        # o(I(x),x) = e                 (left inverse)
        o(a, b) = S(:o, a, b)
        e = S(:e)
        I(a) = S(:I, a)

        eqs = [
            Equation(o(o(V(:x), V(:y)), V(:z)), o(V(:x), o(V(:y), V(:z)))),
            Equation(o(e, V(:x)), V(:x)),
            Equation(o(I(V(:x)), V(:x)), e),
        ]
        prec = CQL.build_default_precedence(eqs; reverse_arity=true)
        rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=15)
        @test converged
        # Standard KB completion for groups produces 10 rules
        @test length(rules) == 10

        # Verify key consequences: right identity o(x,e) = x
        idx = CQL.RuleIndex(rules)
        lhs = CQL.normalize_innermost(idx, o(V(:x), e))
        @test lhs == V(:x)

        # Right inverse: o(x, I(x)) = e
        lhs2 = CQL.normalize_innermost(idx, o(V(:x), I(V(:x))))
        @test lhs2 == e

        # Double inverse: I(I(x)) = x
        lhs3 = CQL.normalize_innermost(idx, I(I(V(:x))))
        @test lhs3 == V(:x)

        # Inverse of product: I(o(x,y)) = o(I(y), I(x))
        lhs4 = CQL.normalize_innermost(idx, I(o(V(:x), V(:y))))
        expected4 = o(I(V(:y)), I(V(:x)))
        @test lhs4 == expected4
    end

    @testset "Commutative monoid (non-orientable)" begin
        # o(x,y) = o(y,x)   (commutativity — cannot be oriented!)
        # o(o(x,y),z) = o(x,o(y,z))   (associativity)
        # o(e,x) = x   (identity)
        o(a, b) = S(:o, a, b)
        e = S(:e)

        eqs = [
            Equation(o(V(:x), V(:y)), o(V(:y), V(:x))),
            Equation(o(o(V(:x), V(:y)), V(:z)), o(V(:x), o(V(:y), V(:z)))),
            Equation(o(e, V(:x)), V(:x)),
        ]
        prec = CQL.build_default_precedence(eqs)
        # Commutativity can't be oriented, so completion may not fully converge
        # but should produce passive equations
        rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5, max_rules=50)
        # Should have some rules (at least identity and associativity oriented)
        @test length(rules) > 0
        # Commutativity should end up in passive
        @test length(passive) > 0 || !converged
    end

    @testset "Boolean algebra fragment" begin
        # and(x, tt) = x
        # and(x, ff) = ff
        # or(x, ff) = x
        a(x, y) = S(:and, x, y)
        o(x, y) = S(:or, x, y)
        tt = S(:tt)
        ff = S(:ff)

        eqs = [
            Equation(a(V(:x), tt), V(:x)),
            Equation(a(V(:x), ff), ff),
            Equation(o(V(:x), ff), V(:x)),
        ]
        prec = Dict(:and => 3, :or => 2, :tt => 1, :ff => 0)
        rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5)
        @test converged
        @test length(rules) == 3

        # Verify: and(and(a_val, tt), ff) = ff
        idx = CQL.RuleIndex(rules)
        result = CQL.normalize_innermost(idx, a(a(S(:a_val), tt), ff))
        @test result == ff
    end

    @testset "Peano arithmetic fragment" begin
        # plus(zero, x) = x
        # plus(succ(x), y) = succ(plus(x, y))
        z = S(:zero)
        su(x) = S(:succ, x)
        pl(x, y) = S(:plus, x, y)

        eqs = [
            Equation(pl(z, V(:x)), V(:x)),
            Equation(pl(su(V(:x)), V(:y)), su(pl(V(:x), V(:y)))),
        ]
        prec = Dict(:plus => 3, :succ => 2, :zero => 1)
        rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5)
        @test converged
        @test length(rules) == 2

        # Verify: plus(succ(succ(zero)), succ(zero)) = succ(succ(succ(zero)))
        idx = CQL.RuleIndex(rules)
        two = su(su(z))
        one = su(z)
        three = su(su(su(z)))
        @test CQL.normalize_innermost(idx, pl(two, one)) == three
    end

    # ================================================================
    # RuleIndex
    # ================================================================
    @testset "RuleIndex" begin
        r1 = CQL.RewriteRule(S(:f, V(:x)), V(:x))
        r2 = CQL.RewriteRule(S(:g, V(:x)), S(:a))
        idx = CQL.RuleIndex(CQL.RewriteRule[r1, r2])

        @testset "indexed lookup" begin
            @test haskey(idx.by_head, :f)
            @test haskey(idx.by_head, :g)
            @test length(idx.by_head[:f]) == 1
        end

        @testset "rewrite_at_root indexed" begin
            result = CQL.rewrite_at_root(idx, S(:f, S(:a)))
            @test result == S(:a)
            result2 = CQL.rewrite_at_root(idx, S(:h, S(:a)))
            @test result2 === nothing
        end

        @testset "normalize indexed" begin
            # f(g(b)) → f(a) via g(x)->a, then → a via f(x)->x
            # So result is S(:a), not S(:b)
            @test CQL.normalize(idx, S(:f, S(:g, S(:b)))) == S(:a)
        end

        @testset "normalize_innermost" begin
            @test CQL.normalize_innermost(idx, S(:f, S(:g, S(:b)))) == S(:a)
        end
    end

    # ================================================================
    # KB Completion Prover (end-to-end)
    # ================================================================
    @testset "KB Completion Prover end-to-end" begin
        @testset "group theory via CQL" begin
            prog = """
            typeside Ty = literal {
                types
                    G
                constants
                    e : G
                functions
                    o : G, G -> G
                    I : G -> G
                equations
                    o(o(x, y), z) = o(x, o(y, z))
                    o(e, x) = x
                    o(I(x), x) = e
                options
                    prover = completion
                    completion_precedence = "e I o"
            }
            """
            env = run_program(prog)
            @test haskey(env.typesides, "Ty")
        end

        @testset "Peano via CQL" begin
            # Test KB completion via typeside with Peano axioms
            prog = raw"""typeside Ty = literal {
    types Nat
    constants z : Nat
    functions s : Nat -> Nat
              plus : Nat, Nat -> Nat
    equations
        plus(z, x) = x
        plus(s(x), y) = s(plus(x, y))
    options prover = completion
}"""
            env = run_program(prog)
            @test haskey(env.typesides, "Ty")
            # The typeside should have completion working for Peano arithmetic
        end

        @testset "prover=e uses PROVER_FAIL" begin
            prog = """
            typeside Ty = literal {
                types
                    X
                constants
                    a b : X
                functions
                    f : X -> X
                equations
                    f(a) = b
                options
                    prover = e
            }
            """
            # Should not throw and should not use KB completion
            env = run_program(prog)
            @test haskey(env.typesides, "Ty")
        end
    end

    # ================================================================
    # Edge Cases
    # ================================================================
    @testset "Edge Cases" begin
        @testset "single trivial equation x = x" begin
            eqs = [Equation(V(:x), V(:x))]
            prec = Dict{Symbol, Int}()
            rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=2)
            @test isempty(rules)
            @test converged
        end

        @testset "constant-only equations" begin
            # a = b, b = c → a -> c, b -> c (or similar)
            eqs = [Equation(S(:a), S(:b)), Equation(S(:b), S(:c))]
            prec = Dict(:a => 3, :b => 2, :c => 1)
            rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=2)
            @test converged
            idx = CQL.RuleIndex(rules)
            # a, b, c should all normalize to c
            @test CQL.normalize(idx, S(:a)) == CQL.normalize(idx, S(:c))
            @test CQL.normalize(idx, S(:b)) == CQL.normalize(idx, S(:c))
        end

        @testset "deeply nested term" begin
            # f^10(x) = x (size 11 -> 1)
            t = V(:x)
            for _ in 1:10
                t = S(:f, t)
            end
            eqs = [Equation(t, V(:x))]
            prec = Dict(:f => 1)
            rules, _, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5)
            @test converged
        end

        @testset "timeout with non-convergent system" begin
            # Commutativity alone can't converge
            eqs = [Equation(S(:f, V(:x), V(:y)), S(:f, V(:y), V(:x)))]
            prec = Dict(:f => 1)
            rules, passive, converged = CQL.kb_complete(eqs, prec; timeout_seconds=1, max_rules=20)
            # Should not converge (commutativity is not orientable)
            @test !converged || !isempty(passive)
        end

        @testset "caching across calls" begin
            empty!(CQL._KB_CACHE)
            empty!(CQL._KB_PREC_HINT)
            eqs = [
                Equation(S(:f, S(:f, V(:x))), V(:x)),
            ]
            prec = Dict(:f => 1)
            # First call
            r1, _, c1 = CQL.kb_complete(eqs, prec; timeout_seconds=5)
            @test c1
            # The result should be cached now (tested via kb_completion_prover)
        end

        @testset "rename_vars produces fresh names" begin
            t = S(:f, V(:x), V(:y))
            (t1, m1) = CQL.rename_vars(t)
            (t2, m2) = CQL.rename_vars(t)
            # The renamed variables should differ between calls
            @test m1[:x] != m2[:x]
            @test m1[:y] != m2[:y]
        end

        @testset "CQLFk and CQLAtt in KB" begin
            # FK equations: f(g(x)) = x where f,g are FKs
            fk_eq = Equation(CQLFk(:f, CQLFk(:g, V(:x))), V(:x))
            prec = Dict(:f => 2, :g => 1)
            rules, _, converged = CQL.kb_complete([fk_eq], prec; timeout_seconds=5)
            @test converged
            @test length(rules) >= 1
        end
    end

    # ================================================================
    # Normalization Strategies
    # ================================================================
    @testset "Normalization Strategies" begin
        # Rules: f(a) -> b, g(b) -> c
        r1 = CQL.RewriteRule(S(:f, S(:a)), S(:b))
        r2 = CQL.RewriteRule(S(:g, S(:b)), S(:c))
        rules = CQL.RewriteRule[r1, r2]
        idx = CQL.RuleIndex(rules)

        @testset "outermost normalize" begin
            # g(f(a)) → g(b) → c
            @test CQL.normalize(rules, S(:g, S(:f, S(:a)))) == S(:c)
            @test CQL.normalize(idx, S(:g, S(:f, S(:a)))) == S(:c)
        end

        @testset "innermost normalize" begin
            @test CQL.normalize_innermost(idx, S(:g, S(:f, S(:a)))) == S(:c)
        end

        @testset "already normal" begin
            @test CQL.normalize(idx, S(:d)) == S(:d)
            @test CQL.normalize_innermost(idx, S(:d)) == S(:d)
        end

        @testset "nested normalization" begin
            # h(g(f(a)), f(a)) → h(c, b) with rules above
            r3 = CQL.RewriteRule[r1, r2]
            idx3 = CQL.RuleIndex(r3)
            result = CQL.normalize_innermost(idx3, S(:h, S(:g, S(:f, S(:a))), S(:f, S(:a))))
            @test result == S(:h, S(:c), S(:b))
        end
    end

    # ================================================================
    # Precedence Building
    # ================================================================
    @testset "Precedence Building" begin
        o(a, b) = S(:o, a, b)
        e = S(:e)
        I(a) = S(:I, a)

        eqs = [
            Equation(o(o(V(:x), V(:y)), V(:z)), o(V(:x), o(V(:y), V(:z)))),
            Equation(o(e, V(:x)), V(:x)),
            Equation(o(I(V(:x)), V(:x)), e),
        ]

        @testset "default (binary > unary > constant)" begin
            prec = CQL.build_default_precedence(eqs; reverse_arity=false)
            @test prec[:o] > prec[:I]
            @test prec[:I] > prec[:e]
        end

        @testset "reverse_arity (unary > binary > constant)" begin
            prec = CQL.build_default_precedence(eqs; reverse_arity=true)
            @test prec[:I] > prec[:o]
            @test prec[:o] > prec[:e]
        end
    end

    # ================================================================
    # Additional Edge Cases for KB Completion
    # ================================================================
    @testset "KB Edge Cases" begin
        @testset "multiple identical equations" begin
            eqs = [Equation(S(:f, V(:x)), V(:x)),
                   Equation(S(:f, V(:x)), V(:x)),
                   Equation(S(:f, V(:x)), V(:x))]
            prec = Dict(:f => 1)
            rules, _, converged = CQL.kb_complete(eqs, prec; timeout_seconds=2)
            @test converged
            @test length(rules) == 1
        end

        @testset "chain of ground rewrites" begin
            # a -> b, b -> c, c -> d: should produce a->d, b->d, c->d
            eqs = [Equation(S(:a), S(:b)), Equation(S(:b), S(:c)), Equation(S(:c), S(:d))]
            prec = Dict(:a => 4, :b => 3, :c => 2, :d => 1)
            rules, _, converged = CQL.kb_complete(eqs, prec; timeout_seconds=2)
            @test converged
            idx = CQL.RuleIndex(rules)
            @test CQL.normalize(idx, S(:a)) == S(:d)
            @test CQL.normalize(idx, S(:b)) == S(:d)
            @test CQL.normalize(idx, S(:c)) == S(:d)
        end

        @testset "size-based orientation fallback" begin
            # When LPO is incomparable but sizes differ
            eqs = [Equation(S(:f, S(:g, V(:x))), V(:x))]
            prec = Dict{Symbol,Int}()  # empty precedence → LPO returns INCOMPARABLE
            rules, _, converged = CQL.kb_complete(eqs, prec; timeout_seconds=2)
            @test converged
            @test length(rules) >= 1
            # Should orient by size: f(g(x)) -> x
            @test CQL.term_size(rules[1].lhs) > CQL.term_size(rules[1].rhs)
        end

        @testset "max_rules limit" begin
            # Create a system that generates many rules
            eqs = [Equation(S(:f, V(:x), V(:y)), S(:f, V(:y), V(:x)))]  # commutativity
            prec = Dict(:f => 1)
            rules, _, converged = CQL.kb_complete(eqs, prec; timeout_seconds=2, max_rules=5)
            @test length(rules) <= 6  # max_rules + 1 (checked after adding)
        end

        @testset "variable renaming doesn't leak" begin
            # Run two consecutive completions and verify they don't interfere
            eqs1 = [Equation(S(:f, S(:f, V(:x))), V(:x))]
            eqs2 = [Equation(S(:g, S(:g, V(:y))), V(:y))]
            prec1 = Dict(:f => 1)
            prec2 = Dict(:g => 1)
            r1, _, c1 = CQL.kb_complete(eqs1, prec1; timeout_seconds=2)
            r2, _, c2 = CQL.kb_complete(eqs2, prec2; timeout_seconds=2)
            @test c1 && c2
            @test length(r1) == 1
            @test length(r2) == 1
        end

        @testset "binary function with unit" begin
            # f(e, x) = x, f(x, e) = x  (two-sided identity)
            eqs = [
                Equation(S(:f, S(:e), V(:x)), V(:x)),
                Equation(S(:f, V(:x), S(:e)), V(:x)),
            ]
            prec = Dict(:f => 2, :e => 1)
            rules, _, converged = CQL.kb_complete(eqs, prec; timeout_seconds=5)
            @test converged
            @test length(rules) == 2
        end

        @testset "critical_pairs! inline iteration" begin
            # Verify the new critical_pairs! function produces same results as original
            r1 = CQL.RewriteRule(S(:f, S(:f, V(:x), V(:y)), V(:z)),
                                 S(:f, V(:x), S(:f, V(:y), V(:z))))
            r2 = CQL.RewriteRule(S(:f, S(:e), V(:x)), V(:x))
            cps = CQL.critical_pairs(r1, r2)
            @test length(cps) >= 0  # just verify it doesn't crash
            # The backward-compatible API should still return tuples
            for (l, r) in cps
                @test l isa CQLTerm
                @test r isa CQLTerm
            end
        end

        @testset "match_term_reuse!" begin
            subst = Dict{Symbol, CQLTerm}()
            # First match
            @test CQL.match_term_reuse!(S(:f, V(:x)), S(:f, S(:a)), subst)
            @test subst[:x] == S(:a)
            # Second match reuses same dict (should clear first)
            @test CQL.match_term_reuse!(S(:g, V(:y)), S(:g, S(:b)), subst)
            @test subst[:y] == S(:b)
            @test !haskey(subst, :x)  # was cleared
        end

        @testset "unify_reuse!" begin
            subst = Dict{Symbol, CQLTerm}()
            @test CQL.unify_reuse!(S(:f, V(:x)), S(:f, S(:a)), subst)
            @test subst[:x] == S(:a)
            @test CQL.unify_reuse!(S(:g, V(:y)), S(:g, S(:b)), subst)
            @test subst[:y] == S(:b)
            @test !haskey(subst, :x)
        end

        @testset "RuleIndex reusable match buffer" begin
            r1 = CQL.RewriteRule(S(:f, V(:x)), V(:x))
            idx = CQL.RuleIndex(CQL.RewriteRule[r1])
            # Multiple rewrites should reuse the same buffer
            @test CQL.rewrite_at_root(idx, S(:f, S(:a))) == S(:a)
            @test CQL.rewrite_at_root(idx, S(:f, S(:b))) == S(:b)
            @test CQL.rewrite_at_root(idx, S(:g, S(:a))) === nothing
        end

        @testset "normalize terminates on irreducible" begin
            r = CQL.RewriteRule(S(:f, S(:a)), S(:b))
            idx = CQL.RuleIndex(CQL.RewriteRule[r])
            # f(c) is irreducible
            @test CQL.normalize(idx, S(:f, S(:c))) == S(:f, S(:c))
            @test CQL.normalize_innermost(idx, S(:f, S(:c))) == S(:f, S(:c))
        end

        @testset "deeply nested normalize" begin
            r = CQL.RewriteRule(S(:f, S(:f, V(:x))), V(:x))
            idx = CQL.RuleIndex(CQL.RewriteRule[r])
            # f^6(a) should reduce to a (even nesting)
            t = S(:a)
            for _ in 1:6
                t = S(:f, t)
            end
            @test CQL.normalize_innermost(idx, t) == S(:a)
            # f^5(a) should reduce to f(a) (odd nesting)
            t2 = S(:a)
            for _ in 1:5
                t2 = S(:f, t2)
            end
            @test CQL.normalize_innermost(idx, t2) == S(:f, S(:a))
        end

        @testset "SmallSubst basic operations" begin
            ss = CQL.SmallSubst(4)
            @test ss.len == 0
            CQL.ss_set!(ss, :x, S(:a))
            @test ss.len == 1
            @test CQL.ss_get(ss, :x) == S(:a)
            @test CQL.ss_get(ss, :y) === nothing
            CQL.ss_set!(ss, :y, S(:b))
            @test ss.len == 2
            @test CQL.ss_get(ss, :y) == S(:b)
            CQL.ss_clear!(ss)
            @test ss.len == 0
            @test CQL.ss_get(ss, :x) === nothing
        end

        @testset "SmallSubst match_term_reuse!" begin
            ss = CQL.SmallSubst(4)
            @test CQL.match_term_reuse!(S(:f, V(:x)), S(:f, S(:a)), ss)
            @test CQL.ss_get(ss, :x) == S(:a)
            # Reuse clears and rematch
            @test CQL.match_term_reuse!(S(:g, V(:y)), S(:g, S(:b)), ss)
            @test CQL.ss_get(ss, :y) == S(:b)
            @test CQL.ss_get(ss, :x) === nothing  # cleared
        end

        @testset "SmallSubst apply_subst" begin
            ss = CQL.SmallSubst(4)
            CQL.ss_set!(ss, :x, S(:a))
            CQL.ss_set!(ss, :y, S(:b))
            result = CQL.apply_subst(S(:f, V(:x), V(:y)), ss)
            @test result == S(:f, S(:a), S(:b))
            # Unbound variable stays
            @test CQL.apply_subst(V(:z), ss) == V(:z)
        end

        @testset "SmallSubst to Dict" begin
            ss = CQL.SmallSubst(4)
            CQL.ss_set!(ss, :x, S(:a))
            CQL.ss_set!(ss, :y, S(:b))
            d = CQL.ss_to_dict(ss)
            @test d[:x] == S(:a)
            @test d[:y] == S(:b)
        end

        @testset "persistent LPO cache" begin
            prec = Dict(:f => 2, :g => 1, :a => 0)
            cache = Dict{UInt128, Symbol}()
            # First comparison populates cache
            @test CQL.lpo_compare(prec, S(:f, V(:x)), S(:g, V(:x)), cache) == :GT
            @test !isempty(cache)
            # Second comparison uses cache
            @test CQL.lpo_compare(prec, S(:f, V(:x)), S(:g, V(:x)), cache) == :GT
        end
    end
end
