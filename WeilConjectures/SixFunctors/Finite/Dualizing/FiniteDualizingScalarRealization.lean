/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingRealizationRestrictionUnit
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingRealizationRestrictionComp

/-! # Scalar adjunction transport for arbitrary finite coefficient families -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local implicit_reducible] integralCoefficientSheaf

private theorem adjunct_conjugate
    {A B : Type*} [Category A] [Category B]
    {T₁ T₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a₁ : T₁ ⊣ R₁) (a₂ : T₂ ⊣ R₂) (α : T₂ ⟶ T₁)
    (K : A) (H : B) (f : T₁.obj K ⟶ H) :
    a₂.homEquiv K H (α.app K ≫ f) =
      a₁.homEquiv K H f ≫ (conjugateEquiv a₁ a₂ α).app H := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← unit_conjugateEquiv, Category.assoc, ← (conjugateEquiv a₁ a₂ α).naturality]
  simp only [Category.assoc]

private theorem adjunct_unit
    {A : Type*} [Category A] {T R : A ⥤ A}
    (a : T ⊣ R) (e : R ≅ 𝟭 A) (K : A) :
    a.homEquiv K K ((a.leftAdjointIdIso e).hom.app K) = e.inv.app K := by
  rw [Adjunction.homEquiv_unit]
  have h := unit_conjugateEquiv Adjunction.id a (a.leftAdjointIdIso e).hom K
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp]
    using h.symm

private theorem adjunct_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {T₁ : A ⥤ B} {R₁ : B ⥤ A} {T₂ : B ⥤ C} {R₂ : C ⥤ B}
    {T₃ : A ⥤ C} {R₃ : C ⥤ A}
    (a₁ : T₁ ⊣ R₁) (a₂ : T₂ ⊣ R₂) (a₃ : T₃ ⊣ R₃)
    (c : R₂ ⋙ R₁ ≅ R₃) {K : A} {H : B} {N : C}
    (v : T₁.obj K ⟶ H) (w : T₂.obj H ⟶ N) (z : T₃.obj K ⟶ N)
    (h : T₂.map v ≫ w = (a₁.leftAdjointCompIso a₂ a₃ c).hom.app K ≫ z) :
    a₃.homEquiv K N z ≫ c.inv.app N =
      a₁.homEquiv K H v ≫ R₁.map (a₂.homEquiv H N w) := by
  have hh := congrArg ((a₁.comp a₂).homEquiv K N) h
  rw [adjunct_conjugate a₃ (a₁.comp a₂)] at hh
  simp only [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
    Equiv.apply_symm_apply] at hh
  rw [Adjunction.comp_homEquiv] at hh
  change (a₁.homEquiv K _) ((a₂.homEquiv _ _) (T₂.map v ≫ w)) =
    a₃.homEquiv K N z ≫ c.inv.app N at hh
  rw [a₂.homEquiv_naturality_left, a₁.homEquiv_naturality_right] at hh
  exact hh.symm

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

private theorem scalar_mate_app
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

private theorem conjugate_unit
    {C : Type*} [Category C] (R : C ⥤ C) (U : R ≅ 𝟭 C)
    {K L : C} (e : K ≅ L) (s : K ⟶ R.obj K)
    (hs : s ≫ U.hom.app K = 𝟙 K) :
    e.inv ≫ s ≫ R.map e.hom ≫ U.hom.app L = 𝟙 L := by
  calc
    _ = e.inv ≫ (s ≫ U.hom.app K) ≫ e.hom := by
      rw [U.hom.naturality]
      simp only [Functor.id_map, Category.assoc]
    _ = 𝟙 _ := by rw [hs, Category.id_comp, Iso.inv_hom_id]

private theorem conjugate_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R₁ : B ⥤ A) (R₂ : C ⥤ B) (R₃ : C ⥤ A) (c : R₂ ⋙ R₁ ≅ R₃)
    {K₁ L₁ : A} {K₂ L₂ : B} {K₃ L₃ : C}
    (e₁ : K₁ ≅ L₁) (e₂ : K₂ ≅ L₂) (e₃ : K₃ ≅ L₃)
    (s₁ : K₁ ⟶ R₁.obj K₂) (s₂ : K₂ ⟶ R₂.obj K₃) (s₃ : K₁ ⟶ R₃.obj K₃)
    (hs : s₃ ≫ c.inv.app K₃ = s₁ ≫ R₁.map s₂) :
    e₁.inv ≫ s₃ ≫ R₃.map e₃.hom ≫ c.inv.app L₃ =
      (e₁.inv ≫ s₁ ≫ R₁.map e₂.hom) ≫
        R₁.map (e₂.inv ≫ s₂ ≫ R₂.map e₃.hom) := by
  calc
    _ = e₁.inv ≫ (s₃ ≫ c.inv.app K₃) ≫ R₁.map (R₂.map e₃.hom) := by
      rw [c.inv.naturality]
      simp only [Functor.comp_map, Category.assoc]
    _ = e₁.inv ≫ s₁ ≫ R₁.map s₂ ≫ R₁.map (R₂.map e₃.hom) := by
      rw [hs, Category.assoc]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← R₁.map_comp_assoc e₂.hom e₂.inv, Iso.hom_inv_id, R₁.map_id,
        Category.id_comp]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

private theorem canonicalScalarMate_isIso {m n : ℕ} (h : n ≤ m) :
    IsIso (((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (finiteDualizingQuotient l E h)))
      (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h))).symm
        (TwoSquare.mk _ _ _ _
          (finiteDualizingRealizationRestriction l E X h).inv)).natTrans) := by
  let φ := finiteDualizingQuotient l E h
  let aE := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let aP := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology X) φ)
  let aI := Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)
  let tP := TwoSquare.mk _ _ _ _ (ProEtale.pbcDerivedComparisonRestrict X φ).inv
  let tI := TwoSquare.mk _ _ _ _ (finiteDualizingIntrinsicRestriction l E X h).inv
  have : IsIso (((mateEquiv aE aP).symm tP).natTrans) :=
    ProEtale.pbcComparisonReductionMap_isIso X φ
  have : IsIso (((mateEquiv aP aI).symm tI).natTrans) :=
    isIso_mate_equivalences aP aI
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (m + 1)))
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))) _
  have hi := mate_vcomp_isIso aE aP aI tP tI
  have he : (TwoSquare.vComp tP tI).natTrans =
      (finiteDualizingRealizationRestriction l E X h).inv := by
    ext K
    simp [tP, tI, φ, TwoSquare.mk, finiteDualizingRealizationRestriction, TwoSquare.vComp]
  change IsIso (((mateEquiv aE aI).symm
    (TwoSquare.mk _ _ _ _ (finiteDualizingRealizationRestriction l E X h).inv)).natTrans)
  rw [← he]
  exact hi

/-- Scalar adjuncts transport through the section-normalized realization, preserving
invertibility and coherent transitions for arbitrary families of objects.
Source: current blueprint lem-coef-finite-dualizing.proof.md, final sentence;
lem-coef-dualizing-site-mates, normalized scalar transport
(blueprint: lem-coef-dualizing-scalar-realization).

Proof: the comparison-site restriction square is induced by ordinary scalar
restriction on sections. The intrinsic restriction comparison is uniquely fixed on
those same sections. Their identity and composition squares therefore agree before
localization. Exact localization preserves these squares, including the canonical
mapDerivedCategory identity and composition constraints. Transpose the resulting
restriction square under the two scalar adjunctions. On the comparison-site part
this is the published pbcComparisonReductionMap; on the intrinsic part conjugation
through the intrinsic equivalences gives an isomorphism of scalar extensions.
Consequently the intrinsic transpose of t is conjugate to the realized v by this
isomorphism and the two endpoint isomorphisms e. Thus it is invertible when v is.
For the identity law, transpose the normalized scalar unit: its adjunct followed by
the restriction unit is identity, by the triangle identity. Conjugate by e and
cancel e.inv followed by e.hom. For composition, transpose the assumed scalar
cocycle using the two scalar adjunctions. Naturality of their units and the defining
leftAdjointCompIso equation give the semilinear restriction cocycle. Transport
through the coherent realization restriction square, move the endpoint maps by
naturality, and cancel the two middle e factors. This gives exactly the displayed
normalizedDVRResComp equation. No exceptional functor, counit of compact support,
constructibility, or arbitrary ambient pro-etale exceptional adjunction enters. -/
theorem finiteDualizing_scalar_realization
    (K : ∀ n : ℕ, Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X)
    (L : ∀ n : ℕ, normalizedDVRDerived l E X n)
    (e : ∀ n : ℕ, (finiteDualizingRealization l E X n).obj (K n) ≅ L n)
    (v : ∀ {m n : ℕ} (h : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj (K m) ⟶ K n)
    (hv : ∀ {m n : ℕ} (h : n ≤ m), IsIso (v h))
    (hunit : ∀ n : ℕ, v (le_refl n) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)).hom.app (K n))
    (hcomp : ∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) X).map (v hrm) ≫ v hmn =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app (K r) ≫ v (hmn.trans hrm)) :
    let t := fun {m n : ℕ} (h : n ≤ m) ↦
      (e m).inv ≫ (finiteDualizingRealization l E X m).map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (finiteDualizingQuotient l E h))).homEquiv _ _ (v h)) ≫
      (finiteDualizingRealizationRestriction l E X h).inv.app (K n) ≫
      (normalizedDVRRes l E X h).map (e n).hom
    (∀ {m n : ℕ} (h : n ≤ m),
      IsIso (((Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _).symm
        (t h))) ∧
    (∀ n : ℕ, t (le_refl n) ≫ (normalizedDVRResUnit l E X n).hom.app (L n) = 𝟙 _) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      t (hmn.trans hrm) ≫ (normalizedDVRResComp l E X hrm hmn).inv.app (L n) =
        t hrm ≫ (normalizedDVRRes l E X hrm).map (t hmn)) := by
  let a := fun {m n : ℕ} (h : n ≤ m) ↦
    Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (finiteDualizingQuotient l E h))
  let s := fun {m n : ℕ} (h : n ≤ m) ↦
    (finiteDualizingRealization l E X m).map ((a h).homEquiv _ _ (v h)) ≫
      (finiteDualizingRealizationRestriction l E X h).inv.app (K n)
  have hsiso {m n : ℕ} (h : n ≤ m) :
      IsIso (((Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _).symm
        (s h)) := by
    let b := Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)
    let F := finiteDualizingRealization l E X m
    let G := finiteDualizingRealization l E X n
    let c := finiteDualizingRealizationRestriction l E X h
    have := hv h
    have := canonicalScalarMate_isIso l E X h
    rw [show s h = F.map ((a h).homEquiv _ _ (v h)) ≫ c.inv.app (K n) from rfl]
    rw [transpose_transport (a h) b F G c]
    rw [scalar_mate_app (a h) b F G c.inv]
    infer_instance
  have hsunit (n : ℕ) : s (le_refl n) ≫
      (normalizedDVRResUnit l E X n).hom.app
        ((finiteDualizingRealization l E X n).obj (K n)) = 𝟙 _ := by
    let U := Functor.mapDerivedCategoryNatIso
      (ProEtale.normalizedOriginRestrictionUnit X.smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)) ≪≫ Functor.mapDerivedCategoryIdIso _
    have hu : (a (le_refl n)).homEquiv _ _ (v (le_refl n)) = U.inv.app (K n) := by
      rw [hunit]
      exact adjunct_unit (a (le_refl n)) U (K n)
    dsimp only [s]
    rw [hu, Category.assoc, finiteDualizingRealizationRestriction_unit]
    change (finiteDualizingRealization l E X n).map (U.inv.app (K n)) ≫
      (finiteDualizingRealization l E X n).map (U.hom.app (K n)) = 𝟙 _
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hscomp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
      s (hmn.trans hrm) ≫ (normalizedDVRResComp l E X hrm hmn).inv.app
        ((finiteDualizingRealization l E X n).obj (K n)) =
      s hrm ≫ (normalizedDVRRes l E X hrm).map (s hmn) := by
    let c := Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
      (finiteDualizingQuotient_comp l E hrm hmn)
    have hc := adjunct_comp (a hrm) (a hmn) (a (hmn.trans hrm)) c
      (v hrm) (v hmn) (v (hmn.trans hrm)) (hcomp hrm hmn)
    calc
      _ = (finiteDualizingRealization l E X r).map
          ((a (hmn.trans hrm)).homEquiv _ _ (v (hmn.trans hrm)) ≫ c.inv.app (K n)) ≫
          (finiteDualizingRealizationRestriction l E X hrm).inv.app
            ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (finiteDualizingQuotient l E hmn)).obj (K n)) ≫
          (normalizedDVRRes l E X hrm).map
            ((finiteDualizingRealizationRestriction l E X hmn).inv.app (K n)) := by
        dsimp only [s]
        rw [Category.assoc, finiteDualizingRealizationRestriction_comp]
        simp only [Functor.map_comp, Category.assoc, c]
      _ = (finiteDualizingRealization l E X r).map
          ((a hrm).homEquiv _ _ (v hrm) ≫
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (finiteDualizingQuotient l E hrm)).map ((a hmn).homEquiv _ _ (v hmn))) ≫
          (finiteDualizingRealizationRestriction l E X hrm).inv.app
            ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (finiteDualizingQuotient l E hmn)).obj (K n)) ≫
          (normalizedDVRRes l E X hrm).map
            ((finiteDualizingRealizationRestriction l E X hmn).inv.app (K n)) := by rw [hc]
      _ = _ := by
        have hn := (finiteDualizingRealizationRestriction l E X hrm).inv.naturality
          ((a hmn).homEquiv _ _ (v hmn))
        dsimp only [Functor.comp_map] at hn
        simp only [Functor.map_comp, Category.assoc, s]
        rw [reassoc_of% hn]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro m n h
    have hi : IsIso
        (((Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _).symm
          ((e m).inv ≫ s h ≫ (normalizedDVRRes l E X h).map (e n).hom)) := by
      rw [Adjunction.homEquiv_naturality_left_symm,
        Adjunction.homEquiv_naturality_right_symm]
      have := hsiso h
      infer_instance
    simpa only [s, a, Category.assoc] using hi
  · intro n
    simpa only [s, a, Category.assoc] using
      conjugate_unit (normalizedDVRRes l E X (le_refl n))
        (normalizedDVRResUnit l E X n) (e n) (s (le_refl n)) (hsunit n)
  · intro r m n hrm hmn
    simpa only [s, a, Category.assoc] using
      conjugate_comp (normalizedDVRRes l E X hrm) (normalizedDVRRes l E X hmn)
        (normalizedDVRRes l E X (hmn.trans hrm)) (normalizedDVRResComp l E X hrm hmn)
        (e r) (e m) (e n) (s hrm) (s hmn) (s (hmn.trans hrm)) (hscomp hrm hmn)

end WeilConjectures
