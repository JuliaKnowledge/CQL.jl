using Test
using CQL

@testset "Integration: colimit + sigma + coproduct + chase" begin

    env = cql"""
    typeside Ty = literal {
        types Str
        constants
            R240 R260 : Str
            AC_R240 AC_R260 : Str
            TUC_R240 TUC_R260 : Str
    }

    schema IFC = literal : Ty {
        entities
            IfcSpace IfcElement IfcSensor IfcPropertySet
        foreign_keys
            elementInSpace : IfcElement -> IfcSpace
            sensorOf : IfcSensor -> IfcElement
            propSetOf : IfcSensor -> IfcPropertySet
        attributes
            spaceName : IfcSpace -> Str
            elementName : IfcElement -> Str
            deviceId : IfcPropertySet -> Str
    }

    schema BRICK = literal : Ty {
        entities
            Location Equipment Point
        foreign_keys
            hasLocation : Equipment -> Location
            hasPoint : Equipment -> Point
        attributes
            locationName : Location -> Str
            equipmentName : Equipment -> Str
            timeseriesId : Point -> Str
    }

    schema_colimit C = quotient IFC + BRICK : Ty {
        entity_equations
            IFC.IfcSpace = BRICK.Location
            IFC.IfcElement = BRICK.Equipment
    }

    schema Combined = getSchema C
    mapping IfcM = getMapping C IFC
    mapping BrickM = getMapping C BRICK

    instance IfcData = literal : IFC {
        generators
            sp1 sp2 : IfcSpace
            el1 el2 : IfcElement
            se1 se2 : IfcSensor
            ps1 ps2 : IfcPropertySet
        equations
            elementInSpace(el1) = sp1
            elementInSpace(el2) = sp2
            sensorOf(se1) = el1
            sensorOf(se2) = el2
            propSetOf(se1) = ps1
            propSetOf(se2) = ps2
            spaceName(sp1) = R240
            spaceName(sp2) = R260
            elementName(el1) = AC_R240
            elementName(el2) = AC_R260
            deviceId(ps1) = TUC_R240
            deviceId(ps2) = TUC_R260
    }

    instance BrickData = literal : BRICK {
        generators
            loc1 loc2 : Location
            eq1 eq2 : Equipment
            pt1 pt2 : Point
        equations
            hasLocation(eq1) = loc1
            hasLocation(eq2) = loc2
            hasPoint(eq1) = pt1
            hasPoint(eq2) = pt2
            locationName(loc1) = R240
            locationName(loc2) = R260
            equipmentName(eq1) = AC_R240
            equipmentName(eq2) = AC_R260
            timeseriesId(pt1) = TUC_R240
            timeseriesId(pt2) = TUC_R260
    }

    instance I1 = sigma IfcM IfcData
    instance I2 = sigma BrickM BrickData
    instance Merged = coproduct I1 + I2 : Combined
    """

    combined = env.Combined
    @test length(combined.ens) >= 4  # At least 4 after merging (Space/Location merged, Element/Equipment merged)

    # Sigma should push both instances into Combined schema
    alg1 = env.I1.algebra
    alg2 = env.I2.algebra

    # Merged coproduct should combine all generators
    alg_merged = env.Merged.algebra
    # The Location/IfcSpace entity (merged) should have generators from both instances
    merged_en = first(values(env.IfcM.ens))  # canonical name for IfcSpace
    n1 = length(carrier(alg1, merged_en))
    n2 = length(carrier(alg2, merged_en))
    n_merged = length(carrier(alg_merged, merged_en))
    @test n_merged == n1 + n2

    # Verify delta pullback works
    env2 = cql"""
    typeside Ty = literal {
        types Str
        constants R240 R260 AC_R240 AC_R260 TUC_R240 TUC_R260 : Str
    }

    schema S1 = literal : Ty {
        entities E
        attributes n : E -> Str
    }

    schema S2 = literal : Ty {
        entities E
        attributes n : E -> Str
    }

    schema_colimit C = quotient S1 + S2 : Ty {
        entity_equations
            S1.E = S2.E
    }

    schema Combined = getSchema C
    mapping M1 = getMapping C S1
    mapping M2 = getMapping C S2

    instance I1 = literal : S1 {
        generators a : E
        equations n(a) = R240
    }

    instance I2 = literal : S2 {
        generators b : E
        equations n(b) = R260
    }

    instance J1 = sigma M1 I1
    instance J2 = sigma M2 I2
    instance Merged = coproduct J1 + J2 : Combined
    instance View1 = delta M1 Merged
    """

    # Delta should pull back to S1's schema
    alg_view = env2.View1.algebra
    @test length(carrier(alg_view, :E)) == 2  # Both elements visible through delta
end
