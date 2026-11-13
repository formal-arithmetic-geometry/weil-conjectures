/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.OpenRestrictionPerfectLocalModels
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardComplementZero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-!
# Perfectness of supported open pushforwards

The derived pushforward along an open immersion of a perfect complex with cohomology supported
in a closed subset of the ambient scheme is again perfect.

## References

* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The derived pushforward along an open immersion `U ⟶ X` of a perfect complex whose
cohomology is supported in a closed subset `T ⊆ U` of `X` is perfect. -/
theorem supported_open_pushforward_perfect (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ F : schemeDerivedCategory U.toScheme, IsPerfect U.toScheme F →
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      IsPerfect X ((schemeDerivedDirectImage U.ι).obj F)) := by
  classical
  intro F hF hs
  let L := schemeOpenRestriction X U
  let R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : L ⊣ R := (Modules.restrictAdjunction U.ι).ofNatIsoLeft
    (Modules.overFunctorEquiv U).symm
  let adj := a.mapDerivedCategoryRightDerivedAdjunction
  have : R.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : R.Full := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  have : R.Faithful := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  have hU : IsPerfect U.toScheme
      (L.mapDerivedCategory.obj ((schemeDerivedDirectImage U.ι).obj F)) := by
    intro x
    obtain ⟨W, hxW, K, hK, ⟨iK⟩⟩ := hF x
    exact ⟨W, hxW, K, hK, ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) W).mapDerivedCategory.mapIso
        (asIso (adj.counit.app F)) ≪≫ iK⟩⟩
  intro x
  by_cases hx : x ∈ U
  · exact open_restriction_perfect_local_models X U _ hU x hx
  · let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
    have hxV : x ∈ V := fun hxT ↦ hx (hTU hxT)
    have hz := supported_open_pushforward_complement_zero X U T V
      (fun _ h ↦ h) F hs
    let K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ :=
      HomologicalComplex.zero
    have hK : IsStrictlyPerfect X V K := by
      constructor
      · exact ⟨0, 0, fun _ _ ↦ isZero_zero _⟩
      · intro n
        refine ⟨0, 0, 0, ?_⟩
        exact (isZero_zero _).eq_of_src _ _
    refine ⟨V, hxV, K, hK, ?_⟩
    exact ⟨hz.iso (DerivedCategory.Q.map_isZero HomologicalComplex.isZero_zero)⟩

end AlgebraicGeometry.Scheme
