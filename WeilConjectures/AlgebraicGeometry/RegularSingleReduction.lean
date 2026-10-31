/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.UniformizerReductionCohomology

/-! # Completed reduction of a module with injective principal scalar -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem zero_module_sections_subsingleton
    (T : Scheme.{u}) {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : pbcModules T R) (hM : IsZero M) (U : T.ProEtᵒᵖ) :
    Subsingleton (M.val.obj U) := by
  let F := SheafOfModules.forget ((adicLisseForget T).obj R) ⋙
    PresheafOfModules.evaluation _ U
  have h := F.map_isZero hM
  exact ModuleCat.isZero_iff_subsingleton.mp h

/-- Reduction of a degree-zero module with injective principal scalar is still
concentrated in degree zero, without a flatness or finiteness hypothesis.

Source: Stacks Project, Tag 06YU; the principal quotient argument in the sufficient
condition of the levelwise-truncation proposition.
(blueprint: lem-weil-pbc-regular-single-reduction).

Proof: the cohomology of the single object is the supplied module in degree zero and
zero in every other degree. Thus the principal scalar is injective on all of its
cohomology sheaves, by transport through the degree-zero homology isomorphism and by
subsingleton sections in the other degrees. The normalized quotient triangle identifies
every reduced cohomology sheaf with ordinary scalar extension of the corresponding
original cohomology sheaf. In nonzero degrees its source is zero, and scalar extension
preserves zero objects. This proves the stated vanishing in every nonzero degree.
-/
theorem principalReduction_single_isConcentrated
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsDomain A]
    (d : AdicCoefficientDatum A) (π : A) (hI : d.ideal = Ideal.span {π})
    (hπ : π ≠ 0) (H : pbcModules T (pbcAdicCompletion T d))
    (hinj : ∀ U : T.ProEtᵒᵖ, Function.Injective (fun x : H.val.obj U ↦
      (CompletedConstantReduction.base T d.ideal ≫
        CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite).hom.app U
          ((adicLisseConstantUnit T A).app U π) • x)) (n : ℕ) :
    ∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((pbcDerivedExtend (pbcAdicProjection T d n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  let L := (DerivedCategory.singleFunctor _ 0).obj H
  let c := CompletedConstantReduction.base T d.ideal ≫
    CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  have hinjL (q : ℤ) (U : T.ProEtᵒᵖ) :
      Function.Injective (fun x : ((DerivedCategory.homologyFunctor _ q).obj L).val.obj U ↦
        c.hom.app U ((adicLisseConstantUnit T A).app U π) • x) := by
    by_cases hq : q = 0
    · subst q
      let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app H
      intro x y hxy
      have h : e.hom.val.app U x = e.hom.val.app U y := by
        apply hinj U
        have hh := congrArg (e.hom.val.app U) hxy
        change (e.hom.val.app U).hom
          (c.hom.app U ((adicLisseConstantUnit T A).app U π) • x) =
          (e.hom.val.app U).hom
          (c.hom.app U ((adicLisseConstantUnit T A).app U π) • y) at hh
        rw [(e.hom.val.app U).hom.map_smul, (e.hom.val.app U).hom.map_smul] at hh
        exact hh
      have hc := congrArg (e.inv.val.app U) h
      simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
        ← SheafOfModules.comp_val, Iso.hom_inv_id, SheafOfModules.id_val,
        PresheafOfModules.id_app, ModuleCat.id_apply] using hc
    · have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
        by_cases h : q < 0
        · exact DerivedCategory.isZero_of_isGE L 0 q h
        · exact DerivedCategory.isZero_of_isLE L 0 q (by omega)
      have := zero_module_sections_subsingleton T _ hz U
      exact fun _ _ _ ↦ Subsingleton.elim _ _
  intro q hq
  let φ := pbcAdicProjection T d n
  let v := ((pbcScalarAdjunction φ).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor _ q).map
        ((pbcDerivedScalarAdjunction φ).unit.app L) ≫
      ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).inv.app
        ((pbcDerivedExtend φ).obj L))
  have : IsIso v := principalReductionCohomology_isIso T d π hI hπ n L q (hinjL (q + 1))
  have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
    by_cases h : q < 0
    · exact DerivedCategory.isZero_of_isGE L 0 q h
    · exact DerivedCategory.isZero_of_isLE L 0 q (by omega)
  exact ((pbcExtend φ).map_isZero hz).of_iso (asIso v).symm

end AlgebraicGeometry.Scheme
