/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import all WeilConjectures.AlgebraicGeometry.DualizingOpenMate.DualizingOpenMate
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionAffineCounit
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
/-! Invertibility of the finite counit comparison used by the integral extension map.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraph 2.
(blueprint: lem-sf-integral-finite-extension-finite-u-is-invertible)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

private theorem transpose_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {R : B ⥤ A} {T' : C ⥤ D} {R' : D ⥤ C}
    (a : T ⊣ R) (b : T' ⊣ R') (F : A ⥤ C) (G : B ⥤ D)
    (c : G ⋙ R' ≅ R ⋙ F) (K : A) (H : B) (v : T.obj K ⟶ H) :
    (b.homEquiv _ _).symm (F.map (a.homEquiv K H v) ≫ c.inv.app H) =
      (b.homEquiv _ _).symm (F.map (a.unit.app K) ≫ c.inv.app (T.obj K)) ≫
        G.map v := by
  rw [← b.homEquiv_naturality_right_symm]
  congr 1
  have hn := c.inv.naturality v
  dsimp only [Functor.comp_map] at hn
  simp only [Adjunction.homEquiv_unit, F.map_comp, Category.assoc]
  rw [hn]

private theorem scalar_mate_component
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {R : B ⥤ A} {T' : C ⥤ D} {R' : D ⥤ C}
    (a : T ⊣ R) (b : T' ⊣ R') (F : A ⥤ C) (G : B ⥤ D)
    (τ : R ⋙ F ⟶ G ⋙ R') (K : A) :
    (b.homEquiv _ _).symm (F.map (a.unit.app K) ≫ τ.app (T.obj K)) =
      ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).natTrans.app K := by
  apply (b.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ τ) K

private theorem isIso_mate_equivalences
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {R : B ⥤ A} {T' : C ⥤ D} {R' : D ⥤ C}
    (a : T ⊣ R) (b : T' ⊣ R') (F : A ≌ C) (G : B ≌ D)
    (τ : R ⋙ F.functor ⟶ G.functor ⋙ R') [IsIso τ] :
    IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).natTrans) := by
  let δ := (mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)
  have hm : mateEquiv a b δ = TwoSquare.mk _ _ _ _ τ := Equiv.apply_symm_apply _ _
  have h := iterated_mateEquiv_conjugateEquiv a b F.toAdjunction G.toAdjunction δ
  rw [hm] at h
  have hi : IsIso ((mateEquiv G.toAdjunction F.toAdjunction
      (TwoSquare.mk _ _ _ _ τ)).natTrans) := by
    have : IsIso F.toAdjunction.unit := inferInstanceAs (IsIso F.unitIso.hom)
    have : IsIso G.toAdjunction.counit := inferInstanceAs (IsIso G.counitIso.hom)
    dsimp [mateEquiv]
    infer_instance
  have : IsIso (conjugateEquiv (a.comp G.toAdjunction)
      (F.toAdjunction.comp b) δ.natTrans) := h ▸ hi
  exact conjugateEquiv_of_iso (a.comp G.toAdjunction) (F.toAdjunction.comp b) δ.natTrans

open scoped CategoryTheory.TwoSquare in
private theorem mate_vcomp_isIso
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {T₁ : A ⥤ B} {R₁ : B ⥤ A} {T₂ : C ⥤ D} {R₂ : D ⥤ C}
    {T₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : T₁ ⊣ R₁) (a₂ : T₂ ⊣ R₂) (a₃ : T₃ ⊣ R₃)
    {F₁ : A ⥤ C} {G₁ : B ⥤ D} {F₂ : C ⥤ E} {G₂ : D ⥤ F}
    (τ₁ : TwoSquare R₁ G₁ F₁ R₂) (τ₂ : TwoSquare R₂ G₂ F₂ R₃)
    [IsIso (((mateEquiv a₁ a₂).symm τ₁).natTrans)]
    [IsIso (((mateEquiv a₂ a₃).symm τ₂).natTrans)] :
    IsIso (((mateEquiv a₁ a₃).symm (τ₁ ≫ᵥ τ₂)).natTrans) := by
  have h := mateEquiv_vcomp a₁ a₂ a₃
    ((mateEquiv a₁ a₂).symm τ₁) ((mateEquiv a₂ a₃).symm τ₂)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]
  dsimp only [TwoSquare.hComp]
  infer_instance

private theorem transport_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {R : B ⥤ A} {T' : C ⥤ D} {R' : D ⥤ C}
    (a : T ⊣ R) (b : T' ⊣ R') (F : A ⥤ C) (G : B ⥤ D)
    (c : G ⋙ R' ≅ R ⋙ F)
    [IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.inv)).natTrans)]
    {K : A} {H : B} (v : T.obj K ⟶ H) [IsIso v]
    {K' : C} {H' : D} (eK : F.obj K ≅ K') (eH : G.obj H ≅ H') :
    IsIso ((b.homEquiv _ _).symm
      (eK.inv ≫ F.map (a.homEquiv _ _ v) ≫ c.inv.app H ≫ R'.map eH.hom)) := by
  rw [b.homEquiv_naturality_left_symm, ← Category.assoc (F.map _),
    b.homEquiv_naturality_right_symm, transpose_transport a b F G c,
    scalar_mate_component a b F G c.inv]
  infer_instance

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
private theorem finiteEtaleU_isIso (hl : l ≠ D.p) (n : ℕ) :
    IsIso (finiteEtaleU l E L ι X D n) := by
  let A := finiteDualizingCoeff l E n
  let B := finiteDualizingCoeff l L n
  let φ := RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)
  let c := finiteDualizingCompactification D X
  let GA := finiteDualizingEtaleExceptional l E D X n
  let GB := finiteDualizingEtaleExceptional l L D X n
  let aA := finiteDualizingEtaleAdjunction l E D X n
  let aB := finiteDualizingEtaleAdjunction l L D X n
  have : IsNoetherian (Spec (.of D.k)) := inferInstance
  apply Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective B
    X.affineCover.f X.affineCover.exists_eq (finiteEtaleU l E L ι X D n)
  intro i
  let j := X.affineCover.f i
  let ca := Etale.DualizingOpenMate.openCompactification c j
  let ea := Etale.DualizingOpenMate.openComposition A c j
  let eb := Etale.DualizingOpenMate.openComposition B c j
  let aa := Etale.DualizingOpenMate.localAdjunction c GA aA j
  let ab := Etale.DualizingOpenMate.localAdjunction c GB aB j
  let aa' := aa.ofNatIsoLeft ea
  let ab' := ab.ofNatIsoLeft eb
  have hlocal :
      Etale.DualizingOpenMate.globalMate φ ca _ _ aa' ab' =
        Etale.DualizingOpenMate.localMate φ c GA GB aA aB j := by
    simp only [Etale.DualizingOpenMate.globalMate, aa', ab',
      Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.ofNatIsoLeft_counit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp,
      Etale.DualizingOpenMate.localMate, Etale.DualizingOpenMate.localInverse,
      Category.assoc, aa, ab, ea, eb]
    rfl
  have hi : IsIso (Etale.DualizingOpenMate.localMate φ c GA GB aA aB j) := by
    rw [← hlocal]
    exact affineCounit_isIso D l hl E L ι n (X.affineCover.X i)
      (j ≫ X ↘ Spec (.of D.k)) ca _ _ aa' ab'
  have hr : Etale.DualizingOpenMate.restrictedMate φ c GA GB aA aB j =
      Etale.DualizingOpenMate.localMate φ c GA GB aA aB j := by
    apply ((Etale.DualizingOpenMate.localAdjunction c GB aB j).homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit,
      Etale.DualizingOpenMate.restrictedMate_adjunct,
      Etale.DualizingOpenMate.middleAdjunct_eq]
    unfold Etale.DualizingOpenMate.localMate
    rw [Equiv.symm_apply_apply]
  have hriso : IsIso (Etale.DualizingOpenMate.restrictedMate φ c GA GB aA aB j) := hr ▸ hi
  have : IsIso
      ((Etale.openScalarRestriction φ j).hom.app (GA.obj (Etale.constantComplex A _)) ≫
        (Etale.derivedRestriction (A := B) j).map
          (Etale.DualizingOpenMate.globalMate φ c GA GB aA aB)) := hriso
  exact IsIso.of_isIso_comp_left
    ((Etale.openScalarRestriction φ j).hom.app (GA.obj (Etale.constantComplex A _)))
    ((Etale.derivedRestriction (A := B) j).map
      (Etale.DualizingOpenMate.globalMate φ c GA GB aA aB))

/-- The finite counit comparison is invertible at every normalized quotient level.

Restrict the ordinary etale counit mate to the canonical affine open cover.
The local adjunction and scalar/open compatibility identify each restriction with
the affine counit calculation. Joint conservativity makes the etale map invertible.
The mate of the etale/pro-etale restriction comparison is an isomorphism, as is the
mate of the intrinsic equivalence square. Their composite transports the scalar
adjunct of the etale map to the prescribed normalized intrinsic realization.
Conjugation by the two origin isomorphisms gives exactly `finiteU`.
The characteristic hypothesis is explicit: it was dropped from the former section
variable list because it did not occur in the conclusion.
(blueprint: lem-sf-integral-finite-extension-finite-u-is-invertible)
-/
theorem finiteU_isIso (hl : l ≠ D.p) (n : ℕ) :
    IsIso (finiteU l E L ι X D n) := by
  let φ := RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let aE := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology φ)
  let aP := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) φ)
  let aI := pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)
  let tP := TwoSquare.mk _ _ _ _ (ProEtale.pbcDerivedComparisonRestrict.{u} X φ).inv
  let tI := TwoSquare.mk _ _ _ _
    (finiteDualizingGenericDerivedRestriction X (integralScalarQuotientMap l E L ι n)).inv
  have : IsIso (((mateEquiv aE aP).symm tP).natTrans) :=
    ProEtale.pbcComparisonReductionMap_isIso X φ
  have : IsIso (((mateEquiv aP aI).symm tI).natTrans) :=
    isIso_mate_equivalences aP aI
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1)))
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l L (n + 1))) _
  have hi := mate_vcomp_isIso aE aP aI tP tI
  have he : (TwoSquare.vComp tP tI).natTrans =
      (finiteRealizationRestriction l E L ι X n).inv := by
    ext K
    simp [tP, tI, φ, TwoSquare.mk, finiteRealizationRestriction, TwoSquare.vComp]
  have hm : IsIso (((mateEquiv aE aI).symm
      (TwoSquare.mk _ _ _ _ (finiteRealizationRestriction l E L ι X n).inv)).natTrans) := by
    rw [← he]
    exact hi
  have hv : IsIso (finiteEtaleU l E L ι X D n) :=
    finiteEtaleU_isIso l E L ι X D hl n
  exact transport_isIso aE aI (finiteDualizingRealization l E X n)
    (finiteDualizingRealization l L X n) (finiteRealizationRestriction l E L ι X n)
    (finiteEtaleU l E L ι X D n) (finiteDualizingOrigin l E D X n)
    (finiteDualizingOrigin l L D X n)
end WeilConjectures.IntegralFiniteExtension
