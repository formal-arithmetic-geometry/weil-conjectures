module

public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import Sheaf.CategoryTheory.GrothendieckEdgeCocycle

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

def LerayEdge (X Y : Scheme.{u}) (f : X ⟶ Y) :=
  ∀ q : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ⟶
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q ⋙
      RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat

def LerayEdgeCocycle {X Y : Scheme.{u}} (f : X ⟶ Y) (ε : LerayEdge X Y f) : Prop :=
  ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution F)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℕ)
    (hK : K = ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
    (s : (RingedSpace.globalSectionsComplex I).cycles q),
    ∃ z : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj (K.cycles q),
      (I.cocomplex.X q).val.presheaf.map
          (eqToHom (congrArg op (Opens.map_top f.base).symm))
          ((RingedSpace.globalSectionsComplex I).iCycles q s) =
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
          (K.iCycles q ≫ (eqToHom hK).f q) z ∧
      (ε q).app F
          ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
            ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
          ((K.homologyπ q) ≫ HomologicalComplex.homologyMap (eqToHom hK) q ≫
            (I.isoRightDerivedObj
              (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) q).inv) z

/-- Construction of the cocycle Leray edge.
(blueprint: lem-pc-leray-edge-cocycle-data)

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.

Proof: apply the Grothendieck spectral-sequence edge construction to direct image
followed by global sections. The resulting edge is represented on an injective
resolution by the displayed cycle and homology maps, which gives the stated
cocycle equation. More explicitly, direct images of injectives are acyclic
for sections by module_pushforward_injective_acyclic. Apply
grothendieck_left_edge_cocycle to these two additive left exact functors and
identify their composite with sections on X via restriction along Opens.map_top.
Left exactness identifies sections of the cycle sheaf with cycles of the
sections complex, so the global cocycle lifts uniquely to z. The generic edge
equation, transported by the resolution comparison isomorphisms, is the second
equality. Resolution comparison and functoriality give a single natural edge
for every coefficient module, independent of the chosen resolution. -/
theorem leray_edge_cocycle_data {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ ε : LerayEdge X Y f, LerayEdgeCocycle f ε := by
  sorry
end AlgebraicGeometry
