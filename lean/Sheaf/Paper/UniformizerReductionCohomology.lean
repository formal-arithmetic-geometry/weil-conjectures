/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedConstantSheafReduction
import all Sheaf.Paper.IntegralLocalReductionLowerBound
import all Sheaf.Paper.AdicReductionCohomologySequence
import all Sheaf.Paper.AdicReductionTriangle
import all Sheaf.Paper.CompletedConstantSheafReduction

/-! # Cohomology reduction under an injective principal scalar -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem constant_change_scalar_one
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (c : adicLisseConstantRing T A ⟶ S) (a : A) (U : T.ProEtᵒᵖ) :
    let F := adicLisseConstantModules T A ⋙ completedAdicChange T c
    let e := CompletedConstantReduction.constantChange_unit T c
    (e.inv ≫ F.map (ModuleCat.ofHom (LinearMap.mulLeft A a)) ≫ e.hom).val.app U
        (1 : S.obj.obj U) =
      c.hom.app U ((adicLisseConstantUnit T A).app U a) := by
  let M := (adicLisseConstantModules T A).obj (ModuleCat.of A A)
  let e := CompletedConstantReduction.constantChange_unit T c
  let z := constantGenerator T (ModuleCat.of A A) U (1 : A)
  let η := (pbcScalarAdjunction c).unit.app M
  have hz : e.inv.val.app U (1 : S.obj.obj U) = η.val.app U z := by
    rw [constant_unit_inv_one]
    exact ((pbcScalarAdjunction_exists c).exists.choose_spec M U z).symm
  have ha : constantGenerator T (ModuleCat.of A A) U a =
      (adicLisseConstantUnit T A).app U a • z := by
    have h := ((PresheafOfModules.sheafificationAdjunction
      (adicLisseConstantUnit T A)).unit.app
        ((constantPresheaves T A).obj (ModuleCat.of A A))).app U |>.hom.map_smul a (1 : A)
    change constantGenerator T (ModuleCat.of A A) U (a * 1) =
      (adicLisseConstantUnit T A).app U a • z at h
    simpa only [mul_one] using h
  have hη : (@id (((completedAdicChange T c).obj M).val.obj U)
        (η.val.app U (constantGenerator T (ModuleCat.of A A) U a))) =
      c.hom.app U ((adicLisseConstantUnit T A).app U a) •
        (@id (((completedAdicChange T c).obj M).val.obj U) (η.val.app U z)) := by
    rw [ha]
    exact (η.val.app U).hom.map_smul _ _
  have hunit (x : M.val.obj U) : η.val.app U x =
      completedAdicChangeTensor T c M U 1 x :=
    (pbcScalarAdjunction_exists c).exists.choose_spec M U x
  change e.hom.val.app U
    (((completedAdicChange T c).map
      ((adicLisseConstantModules T A).map
        (ModuleCat.ofHom (LinearMap.mulLeft A a)))).val.app U
          (e.inv.val.app U (1 : S.obj.obj U))) = _
  rw [constant_unit_inv_one, completed_map_tensor_one, constantGenerator_naturality]
  change e.hom.val.app U (completedAdicChangeTensor T c M U 1
    (constantGenerator T (ModuleCat.of A A) U (a * 1))) = _
  dsimp only [id] at hη
  rw [mul_one, ← hunit]
  erw [hη, ← hz]
  rw [(e.hom.val.app U).hom.map_smul]
  have he := congrArg (fun f : SheafOfModules.unit ((adicLisseForget T).obj S) ⟶
      SheafOfModules.unit ((adicLisseForget T).obj S) ↦
        @id (S.obj.obj U) ((f.val.app U).hom (1 : S.obj.obj U))) e.inv_hom_id
  change e.hom.val.app U (e.inv.val.app U (1 : S.obj.obj U)) =
    (1 : S.obj.obj U) at he
  erw [he]
  exact mul_one (c.hom.app U ((adicLisseConstantUnit T A).app U a))

/-- If the principal scalar acts injectively on the next cohomology, the canonical
cohomology scalar-extension comparison is an isomorphism.

Source: Stacks Project, sites-cohomology.tex, Tag 06YU, and sites-modules.tex,
Tag 093M; the sufficient-condition paragraph of the levelwise-truncation proposition.
(blueprint: lem-weil-pbc-uniformizer-reduction-cohomology).

Proof: the completed constant coefficient ring is flat over the constant scalar ring.
Consequently the two-term principal quotient sequence remains short exact after completion.
Tensor it with a K-flat representative. Its distinguished triangle gives the normalized
universal-coefficient short exact sequence. Multiplication by the scalar power is monic
on the next cohomology, since repeated multiplication by the scalar is injective on every
section. Thus its kernel is zero. The first arrow in the short exact sequence is therefore
an isomorphism. Exact faithful scalar restriction reflects this isomorphism. This argument
uses neither boundedness nor finiteness of the cohomology sheaves, and includes empty sites.
-/
theorem principalReductionCohomology_isIso
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsDomain A]
    (d : AdicCoefficientDatum A) (π : A) (hI : d.ideal = Ideal.span {π})
    (hπ : π ≠ 0) (n : ℕ) (K : PbcCompletedDerived T d) (q : ℤ)
    (hinj : ∀ U : T.ProEtᵒᵖ,
      Function.Injective (fun x :
        ((DerivedCategory.homologyFunctor _ (q + 1)).obj K).val.obj U ↦
        (CompletedConstantReduction.base T d.ideal ≫
          CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite).hom.app U
            ((adicLisseConstantUnit T A).app U π) • x)) :
    IsIso (((pbcScalarAdjunction (pbcAdicProjection T d n)).homEquiv _ _).symm
      ((DerivedCategory.homologyFunctor _ q).map
          ((pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app K) ≫
        ((pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryHomologyFunctorIso q).inv.app
          ((pbcDerivedExtend (pbcAdicProjection T d n)).obj K))) := by
  let c := CompletedConstantReduction.base T d.ideal ≫
    CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  let F := adicLisseConstantModules T A ⋙ completedAdicChange T c
  let e := CompletedConstantReduction.constantChange_unit T c
  let f := e.inv ≫ F.map (ModuleCat.ofHom (LinearMap.mulLeft A (π ^ (n + 1)))) ≫ e.hom
  let H := (DerivedCategory.homologyFunctor _ (q + 1)).obj K
  obtain ⟨p, hp, hs, hpone⟩ := completed_principal_resolution T d π hI hπ n
  obtain ⟨a, w, hT, hcoh⟩ := pbc_adic_reduction_triangle T
    (pbcAdicProjection T d n) f p hpone hp hs K
  obtain ⟨δ, hδ, hex⟩ := reduction_triangle_sequence T d n f K a w hT hcoh q
  let μ := ReductionTensor.tensorMultiplication T (pbcAdicCompletion T d) f H
  have hμ : Mono μ := by
    constructor
    intro Z g h hgh
    ext U x
    have hscalar : f.val.app U (1 : (pbcAdicCompletion T d).obj.obj U) =
        c.hom.app U ((adicLisseConstantUnit T A).app U (π ^ (n + 1))) :=
      constant_change_scalar_one T c (π ^ (n + 1)) U
    have hinjpow : Function.Injective (fun x : H.val.obj U ↦
        (c.hom.app U ((adicLisseConstantUnit T A).app U π)) ^ (n + 1) • x) := by
      induction n + 1 with
      | zero => intro x y h; simpa only [pow_zero, one_smul] using h
      | succ k ih =>
        intro x y h
        apply hinj U
        apply ih
        simpa only [pow_succ, mul_smul] using h
    apply hinjpow
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app U) hgh) x
    change μ.val.app U (g.val.app U x) = μ.val.app U (h.val.app U x) at hh
    simp only [μ, ReductionTensor.tensorMultiplication_apply] at hh
    erw [hscalar] at hh
    simpa only [map_pow] using hh
  have hmono : Mono ((SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := pbcAdicCompletion T d) H).map f) := by
    let eH := ReductionTensor.tensorUnitIso T (pbcAdicCompletion T d) H
    constructor
    intro Z g h hgh
    apply (cancel_mono eH.hom).1
    apply (cancel_mono μ).1
    change (g ≫ eH.hom) ≫ (eH.inv ≫ _ ≫ eH.hom) =
      (h ≫ eH.hom) ≫ (eH.inv ≫ _ ≫ eH.hom)
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using congrArg
      (fun k ↦ k ≫ eH.hom) hgh
  have := hmono
  have hc := hex.isIso_f_iff.mpr (isZero_kernel_of_mono _)
  let φ := pbcAdicProjection T d n
  let S := (pbcAdicRings T d).obj (op n)
  let v := ((pbcScalarAdjunction φ).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor _ q).map
        ((pbcDerivedScalarAdjunction φ).unit.app K) ≫
      ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).inv.app
        ((pbcDerivedExtend φ).obj K))
  have : IsIso ((pbcRestrict φ).map v) := hc
  have : IsIso ((SheafOfModules.toSheaf ((adicLisseForget T).obj S)).map v) :=
    inferInstanceAs (IsIso ((SheafOfModules.toSheaf
      ((adicLisseForget T).obj (pbcAdicCompletion T d))).map ((pbcRestrict φ).map v)))
  exact isIso_of_reflects_iso v (SheafOfModules.toSheaf ((adicLisseForget T).obj S))

end AlgebraicGeometry.Scheme
