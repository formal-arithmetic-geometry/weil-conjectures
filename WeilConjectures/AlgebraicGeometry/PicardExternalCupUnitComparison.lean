/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyPullbackComparison
import WeilConjectures.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities

/-! # Comparison of external cup products with the degree-zero unit class

## References

* Stacks Project, Varieties, Tag 0BED
* Stacks Project, Cohomology on Sites, Tag 03FD
* Stacks Project, Cohomology, Tag 01F7
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open Modules

/-- Module-to-abelian comparisons identify cup products with the class of 1 with
projection pullbacks. There is no assumption on the global structure ring maps
(Stacks, Tag 0BED). -/
theorem picard_external_cup_unit_comparison (k : Type u) [Field k] (X Y : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k)) :
    let F := SheafOfModules.unit X.ringCatSheaf
    let G := SheafOfModules.unit Y.ringCatSheaf
    ∃ (eX : scalarCohomology f F 1 ≃+ Sheaf.H (structureSheafAb X) 1)
      (eY : scalarCohomology g G 1 ≃+ Sheaf.H (structureSheafAb Y) 1)
      (eP : scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) 1
        ≃+ Sheaf.H (structureSheafAb (pullback f g)) 1),
      (∀ a : scalarCohomology f F 1,
        eP (externalCup f g F G 1 0 a (scalarUnitCohomologyClass g)) =
          structureSheafCohomologyPullback (pullback.fst f g) 1 (eX a)) ∧
      (∀ b : scalarCohomology g G 1,
        eP (externalCup f g F G 0 1 (scalarUnitCohomologyClass f) b) =
          structureSheafCohomologyPullback (pullback.snd f g) 1 (eY b)) := by
  classical
  let P := pullback f g
  let p := pullback.fst f g ≫ f
  let : MonoidalCategory (SheafOfModules.{u} P.ringCatSheaf) :=
    SheafOfModules.monoidalCategory P.sheaf
  let x := tensorPullbackObjUnitToUnit (pullback.fst f g)
  let y := tensorPullbackObjUnitToUnit (pullback.snd f g)
  have : IsIso x := (tensorPullbackObjUnitToUnit_isIso (pullback.fst f g)).1
  have : IsIso y := (tensorPullbackObjUnitToUnit_isIso (pullback.snd f g)).1
  let m := CategoryTheory.MonoidalCategory.tensorHom x y ≫
    (CategoryTheory.MonoidalCategory.leftUnitor (SheafOfModules.unit P.ringCatSheaf)).hom
  let c := (ModuleCat.restrictScalars (scalarMap p ⊤)).mapIso
    ((RingedSpace.moduleCohomology P.toRingedSpace 1).mapIso (asIso m))
  obtain ⟨e, he⟩ := scalar_unit_cohomology_pullback_comparison k
  obtain ⟨hx, hy⟩ := external_cup_unit_coefficient_identities k X Y f g
  refine ⟨e X f, e Y g, c.toLinearEquiv.toAddEquiv.trans (e P p), ?_, ?_⟩
  · intro a
    change e P p (scalarCohomologyMap p m 1
      (externalCup f g _ _ 1 0 a (scalarUnitCohomologyClass g))) = _
    rw [hx a]
    exact he f p (pullback.fst f g) rfl a
  · intro b
    change e P p (scalarCohomologyMap p m 1
      (externalCup f g _ _ 0 1 (scalarUnitCohomologyClass f) b)) = _
    rw [hy b]
    exact he g p (pullback.snd f g) pullback.condition.symm b

end AlgebraicGeometry.Scheme
