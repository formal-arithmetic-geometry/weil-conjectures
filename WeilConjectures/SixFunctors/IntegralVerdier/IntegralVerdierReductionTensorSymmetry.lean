/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import all WeilConjectures.SecSmoothPurity.ModuleTensorExtensionEquation

/-! # Signed symmetry of the normalized integral reduction tensor comparison

Source: Stacks 06YL, 06YU and 07A4; the signed-swap calculation in the second
paragraph of the proof of `thm-coef-integral-verdier`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier

open MonoidalCategory
open CategoryTheory.CochainPullback

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  IntegralHom.totalPair IntegralHom.pair
  IntegralHom.reductionCounit
  completedIntegralCoefficientSheafUnrestricted

set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] completedIntegralCommRingSheaf
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheaf
  integralDerivedReduction integralReductionChangeOfRings completedIntegralRestrictScalars
  integralReductionExistence scalarReductionExistence scalarReductionExtension
  completedIntegralCommRingProjection completedIntegralCommRingProjectionUnrestricted
  completedIntegralCoefficientProjection CategoryTheory.sheafCompose
  integralCoefficientCommRingSheaf integralCoefficientSheaf
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars IntegralHom.totalTensor
  extensionFunctor PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' ModuleCat.RestrictScalars.map'

private theorem transport_square
    {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F : C ⥤ D)
    (μ : T ⋙ F ≅ F.prod F ⋙ U)
    (s : ∀ A B, T.obj (A, B) ≅ T.obj (B, A))
    (t : ∀ A B, U.obj (A, B) ≅ U.obj (B, A))
    (hs : ∀ A B A' B' (f : A ⟶ A') (g : B ⟶ B'),
      T.map (Prod.mkHom f g) ≫ (s A' B').hom =
        (s A B).hom ≫ T.map (Prod.mkHom g f))
    (ht : ∀ A B A' B' (f : A ⟶ A') (g : B ⟶ B'),
      U.map (Prod.mkHom f g) ≫ (t A' B').hom =
        (t A B).hom ≫ U.map (Prod.mkHom g f))
    {A B A' B' : C} (a : A ≅ A') (b : B ≅ B')
    (h : F.map (s A B).hom ≫ μ.hom.app (B, A) =
      μ.hom.app (A, B) ≫ (t (F.obj A) (F.obj B)).hom) :
    F.map (s A' B').hom ≫ μ.hom.app (B', A') =
      μ.hom.app (A', B') ≫ (t (F.obj A') (F.obj B')).hom := by
  have : IsIso (Prod.mkHom a.hom b.hom) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (F.map (T.map (Prod.mkHom a.hom b.hom)))).mp
  have hn := μ.hom.naturality (Prod.mkHom a.hom b.hom)
  have hn' := μ.hom.naturality (Prod.mkHom b.hom a.hom)
  simp only [Functor.comp_map, Functor.prod_map] at hn hn'
  calc
    _ = F.map (s A B).hom ≫ F.map (T.map (Prod.mkHom b.hom a.hom)) ≫
        μ.hom.app (B', A') := by
      rw [← Category.assoc, ← F.map_comp, hs, F.map_comp, Category.assoc]
    _ = F.map (s A B).hom ≫ μ.hom.app (B, A) ≫
        U.map (Prod.mkHom (F.map b.hom) (F.map a.hom)) := by rw [hn']
    _ = μ.hom.app (A, B) ≫ (t (F.obj A) (F.obj B)).hom ≫
        U.map (Prod.mkHom (F.map b.hom) (F.map a.hom)) := by
      rw [← Category.assoc, h, Category.assoc]
    _ = μ.hom.app (A, B) ≫ U.map (Prod.mkHom (F.map a.hom) (F.map b.hom)) ≫
        (t (F.obj A') (F.obj B')).hom := by rw [ht]
    _ = _ := by rw [← Category.assoc, ← hn, Category.assoc]

private theorem normalized_square
    {C : Type*} [Category* C]
    {A A' B B' C₀ C₀' D D' E₀ E₀' H H' : C}
    (a : A ≅ B) (a' : A' ≅ B') (μ : B ≅ C₀) (μ' : B' ≅ C₀')
    (c : C₀ ≅ D) (c' : C₀' ≅ D') (r : E₀ ≅ D) (r' : E₀' ≅ D')
    (b : E₀ ≅ H) (b' : E₀' ≅ H')
    (s : B ⟶ B') (σ : A ⟶ A') (t : C₀ ⟶ C₀') (τ : E₀ ⟶ E₀')
    (ε : A ⟶ H) (ε' : A' ⟶ H') (v : H ⟶ H')
    (hs : a.inv ≫ σ ≫ a'.hom = s)
    (ht : c.hom ≫ r.inv ≫ τ ≫ r'.hom = t ≫ c'.hom)
    (hn : a.hom ≫ μ.hom ≫ c.hom ≫ r.inv ≫ b.hom = ε)
    (hn' : a'.hom ≫ μ'.hom ≫ c'.hom ≫ r'.inv ≫ b'.hom = ε')
    (hε : σ ≫ ε' = ε ≫ v) (hτ : τ ≫ b'.hom = b.hom ≫ v) :
    s ≫ μ'.hom = μ.hom ≫ t := by
  apply (cancel_epi a.hom).mp
  apply (cancel_mono (c'.hom ≫ r'.inv ≫ b'.hom)).mp
  simp only [Category.assoc]
  have hts : t ≫ c'.hom ≫ r'.inv ≫ b'.hom =
      c.hom ≫ r.inv ≫ b.hom ≫ v := by
    rw [← Category.assoc t c'.hom, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hτ]
  rw [hts, ← hs]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hn, ← hn'] at hε
  simpa only [Category.assoc] using hε

private theorem identified_pair_ext
    (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (φ : R ⟶ S)
    (M N : IntegralHom.Modules.{u, u} X R)
    (M' N' H : IntegralHom.Modules.{u, u} X S)
    (eM : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ≅ M')
    (eN : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N ≅ N')
    (xM : ∀ U : X.ProEtᵒᵖ, M.val.obj U → M'.val.obj U)
    (xN : ∀ U : X.ProEtᵒᵖ, N.val.obj U → N'.val.obj U)
    (hM : ∀ U x, eM.hom.val.app U (extensionTmul φ M U 1 x) = xM U x)
    (hN : ∀ U x, eN.hom.val.app U (extensionTmul φ N U 1 x) = xN U x)
    {f g : ((IntegralHom.ordinaryTensor.{u, u} X S).obj M').obj N' ⟶ H}
    (h : ∀ U x y, f.val.app U (IntegralHom.pair.{u, u} X S M' N' U (xM U x) (xN U y)) =
      g.val.app U (IntegralHom.pair.{u, u} X S M' N' U (xM U x) (xN U y))) : f = g := by
  let := IntegralHom.tensorLocalization.{u, u} X S
  let := SheafOfModules.monoidalCategory S
  apply (cancel_epi (eM.hom ⊗ₘ eN.hom)).mp
  apply scalarTensor_hom_ext₂ φ M N H
  intro U x y
  change f.val.app U ((eM.hom ⊗ₘ eN.hom).val.app U _) =
    g.val.app U ((eM.hom ⊗ₘ eN.hom).val.app U _)
  rw [moduleTmul_map (R := S) eM.hom eN.hom U
    (extensionTmul φ M U 1 x) (extensionTmul φ N U 1 y), hM, hN]
  unfold IntegralHom.pair at h
  unfold moduleTmul
  exact h U x y

private theorem extension_pair_ext
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) (M N : scalarReductionSource l E X)
    (H : scalarReductionTarget l E X n)
    {f g : ((IntegralHom.ordinaryTensor.{u, u} X (integralCoefficientCommRingSheaf l E X n)).obj
      ((scalarReductionExtension l E X n).obj M)).obj
        ((scalarReductionExtension l E X n).obj N) ⟶ H}
    (h : ∀ U x y, f.val.app U (IntegralHom.pair.{u, u} X _ _ _ U
        ((IntegralHom.reductionUnit l E X D hl n M).val.app U x)
        ((IntegralHom.reductionUnit l E X D hl n N).val.app U y)) =
      g.val.app U (IntegralHom.pair.{u, u} X _ _ _ U
        ((IntegralHom.reductionUnit l E X D hl n M).val.app U x)
        ((IntegralHom.reductionUnit l E X D hl n N).val.app U y))) : f = g := by
  exact identified_pair_ext X (completedIntegralCommRingSheafUnrestricted l E X)
    (integralCoefficientCommRingSheaf l E X n)
    (completedIntegralCommRingProjectionUnrestricted l E X n) M N _ _ H
    (eqToIso ((scalarReductionExistence l E X n).choose_spec.choose M).symm)
    (eqToIso ((scalarReductionExistence l E X n).choose_spec.choose N).symm)
    (fun U x ↦ (IntegralHom.reductionUnit l E X D hl n M).val.app U x)
    (fun U x ↦ (IntegralHom.reductionUnit l E X D hl n N).val.app U x)
    (fun U x ↦ ((scalarReductionExtension_adjunction l E X n).choose_spec M U x).symm)
    (fun U y ↦ ((scalarReductionExtension_adjunction l E X n).choose_spec N U y).symm) h

private theorem totalPair_comp_apply
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q H : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (f : ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ⟶ H)
    (i j : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    (CochainComplex.ιMapBifunctor P Q (IntegralHom.ordinaryTensor.{u, u} X R)
      i j (i + j) rfl ≫ f.f (i + j)).val.app U
        (IntegralHom.pair.{u, u} X R (P.X i) (Q.X j) U x y) =
    (f.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) := by
  unfold IntegralHom.totalPair
  rfl

private theorem restricted_unit_naturality
    (X : Scheme.{u}) (R S : Sheaf (ProEt.topology X) RingCat.{u + 1}) (φ : R ⟶ S)
    (F : SheafOfModules.{u + 1} R ⥤ SheafOfModules.{u + 1} S)
    (η : 𝟭 _ ⟶ F ⋙ SheafOfModules.restrictScalars φ)
    {M N : SheafOfModules.{u + 1} R} (f : M ⟶ N)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (F.map f).val.app U ((η.app M).val.app U x) =
      (η.app N).val.app U (f.val.app U x) := by
  have hn := congrArg (fun q ↦ q.val.app U x) (η.naturality f)
  change (η.app N).val.app U (f.val.app U x) =
    (F.map f).val.app U ((η.app M).val.app U x) at hn
  exact hn.symm

private theorem extension_total_ext
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (H : CochainComplex (scalarReductionTarget l E X n) ℤ)
    {f g : ((IntegralHom.totalTensor.{u, u} X
      (integralCoefficientCommRingSheaf l E X n)).obj
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ⟶ H}
    (h : ∀ i j U x y, (f.f (i + j)).val.app U
        (IntegralHom.totalPair.{u, u} X _ _ _ i j U
          ((IntegralHom.reductionUnit l E X D hl n (P.X i)).val.app U x)
          ((IntegralHom.reductionUnit l E X D hl n (Q.X j)).val.app U y)) =
      (g.f (i + j)).val.app U
        (IntegralHom.totalPair.{u, u} X _ _ _ i j U
          ((IntegralHom.reductionUnit l E X D hl n (P.X i)).val.app U x)
          ((IntegralHom.reductionUnit l E X D hl n (Q.X j)).val.app U y))) : f = g := by
  let := IntegralHom.countableColimits.{u, u} X (integralCoefficientCommRingSheaf l E X n)
  let := IntegralHom.ordinaryTensorZero.{u, u} X (integralCoefficientCommRingSheaf l E X n)
  let : ∀ M : IntegralHom.Modules.{u, u} X (integralCoefficientCommRingSheaf l E X n),
      ((IntegralHom.ordinaryTensor.{u, u} X (integralCoefficientCommRingSheaf l E X n)).obj
        M).PreservesZeroMorphisms := fun M ↦ IntegralHom.ordinaryTensorObjZero.{u, u} X _ M
  dsimp only [IntegralHom.totalTensor] at f g
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex
      (.up ℤ)).obj P)
    (K₂ := ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex
      (.up ℤ)).obj Q)
    (F := IntegralHom.ordinaryTensor.{u, u} X (integralCoefficientCommRingSheaf l E X n))
    (c := .up ℤ)
  intro i j hij
  change i + j = k at hij
  subst k
  apply extension_pair_ext D l hl E X n (P.X i) (Q.X j) (H.X (i + j))
  intro U x y
  exact (totalPair_comp_apply X _ _ _ H f i j U _ _).trans
    ((h i j U x y).trans (totalPair_comp_apply X _ _ _ H g i j U _ _).symm)

private theorem unit_naturality_apply
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) {M N : scalarReductionSource l E X}
    (f : M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((integralReductionChangeOfRings l E X D hl n).map f).val.app U
      ((IntegralHom.reductionUnit l E X D hl n M).val.app U x) =
    (IntegralHom.reductionUnit l E X D hl n N).val.app U (f.val.app U x) := by
  let η : 𝟭 (scalarReductionSource l E X) ⟶
      integralReductionChangeOfRings l E X D hl n ⋙
        completedIntegralRestrictScalars l E X D hl n :=
    (scalarReductionExtension_adjunction l E X n).choose.unit
  exact restricted_unit_naturality X _ _
    (completedIntegralCoefficientProjection l E X D hl n)
    (integralReductionChangeOfRings l E X D hl n) η f U x

private theorem unit_eqToHom_apply
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) {M N : scalarReductionSource l E X} (h : M = N)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (IntegralHom.reductionUnit l E X D hl n N).val.app U ((eqToHom h).val.app U x) =
    (eqToHom (congrArg (scalarReductionExtension l E X n).obj h)).val.app U
      ((IntegralHom.reductionUnit l E X D hl n M).val.app U x) := by
  subst N
  rfl

private theorem component_transport
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {J : Type*} {c : ComplexShape J}
    {P Q : HomologicalComplex C c} (f : P ⟶ Q) {i j : J} (h : i = j) :
    f.f i ≫ eqToHom (congrArg Q.X h) = eqToHom (congrArg P.X h) ≫ f.f j := by
  subst j
  simp

private theorem counit_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hp : IntegralHom.flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    IsIso (IntegralHom.reductionCounit l E X D hl n P) := by
  have := integralDerivedReduction_counit_isIso l E X D hl n P hp
  unfold IntegralHom.reductionCounit
  infer_instance

private theorem counit_naturality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ)
    {P Q : CochainComplex (scalarReductionSource l E X) ℤ} (f : P ⟶ Q) :
    (scalarReductionDerivedExtension l E X n).map (DerivedCategory.Q.map f) ≫
      IntegralHom.reductionCounit l E X D hl n Q =
    IntegralHom.reductionCounit l E X D hl n P ≫ DerivedCategory.Q.map
      (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).map f) := by
  let ε : DerivedCategory.Q ⋙ integralDerivedReduction l E X D hl n ⟶
      (integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
        (integralDerivedReductionCounit l E X D hl n) ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        ((integralReductionChangeOfRings l E X D hl n).mapHomotopyCategoryFactors
          (.up ℤ)).hom _ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso _).hom
  have hn := ε.naturality f
  dsimp only [ε, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map] at hn
  simpa only [IntegralHom.reductionCounit, Category.id_comp, Category.comp_id,
    integralDerivedReduction, Iso.app_hom, Iso.app_inv] using hn

/-- The normalized coefficient tensor comparison preserves signed interchange.
This concerns tensor and scalar reduction alone, with no dualizing object, internal
Hom comparison, evaluation, or double-dual morphism.

Source: Stacks 06YL, 06YU and 07A4; the tensor interchange calculation in
`thm-coef-integral-verdier`, second proof paragraph.
(blueprint: lem-sf-integral-verdier-reduction-tensor-symmetry).

Proof: resolve the two inputs by K-flat complexes with flat terms. The reduction
counits on these representatives are isomorphisms. Use the representative equations
of the source and finite signed symmetries and the normalization of the reduction
presentation. On the summand of bidegree (i,j), both paths send the scalar-unit
pure tensor x tensor y to (-1)^(ij) times the scalar-unit tensor y tensor x.
The scalar extension units generate their extended modules, the sheafified tensor
is generated locally by pure tensors, and the total tensor is the direct sum of
these summands. Consequently the chain maps agree. The representative comparison
squares identify their derived images with the desired two composites. Finally
naturality of both signed symmetries and of mu transports the equality along the
representing isomorphisms to every pair of derived objects. The formula also holds
for zero objects and empty schemes, since the same generator calculation applies. -/
theorem reduction_tensor_symmetry
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (s : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) a)
    (hs : ∀ (K L K' L' : Ambient l E X) (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (n : ℕ) (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (t : SignedSymmetry X (integralCoefficientCommRingSheaf l E X n) m.target)
    (ht : ∀ (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
      (f : K ⟶ K') (g : L ⟶ L'),
      m.target.tensor.map (Prod.mkHom f g) ≫ (t.swap K' L').hom =
        (t.swap K L).hom ≫ m.target.tensor.map (Prod.mkHom g f))
    (K L : Ambient l E X) :
    m.mu.inv.app (K, L) ≫
        (scalarReductionDerivedExtension l E X n).map (s.swap K L).hom =
      (t.swap ((scalarReductionDerivedExtension l E X n).obj K)
        ((scalarReductionDerivedExtension l E X n).obj L)).hom ≫ m.mu.inv.app (L, K)  := by
  classical
  let F := scalarReductionDerivedExtension l E X n
  let G := (integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)
  have hrep (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
      (hp : IntegralHom.flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P)
      (hq : IntegralHom.flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) Q) :
      F.map (s.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
          m.mu.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
        m.mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (t.swap (F.obj (DerivedCategory.Q.obj P))
            (F.obj (DerivedCategory.Q.obj Q))).hom := by
    obtain ⟨hp', hq', β, hβ, hβpure, hβsquare⟩ := m.normalization P Q hp hq
    obtain ⟨hq'', hp'', β', hβ', hβ'pure, hβ'square⟩ := m.normalization Q P hq hp
    obtain ⟨σ, hσpure, hσsquare⟩ := s.representative P Q hp hq
    obtain ⟨τ, hτpure, hτsquare⟩ := t.representative (G.obj P) (G.obj Q) hp' hq'
    have hchain : β ≫ G.map σ = τ ≫ β' := by
      apply extension_total_ext D l hl E X n P Q
      intro i j U x y
      change ((integralReductionChangeOfRings l E X D hl n).map (σ.f (i + j))).val.app U
          ((β.f (i + j)).val.app U _) =
        (β'.f (i + j)).val.app U ((τ.f (i + j)).val.app U _)
      rw [hβpure, unit_naturality_apply, hσpure]
      rw [hτpure i j U
        ((IntegralHom.reductionUnit l E X D hl n (P.X i)).val.app U x)
        ((IntegralHom.reductionUnit l E X D hl n (Q.X j)).val.app U y)]
      simp only [Units.smul_def, map_zsmul]
      congr 1
      have htransport := congrArg (fun f ↦ f.val.app U
        (IntegralHom.totalPair.{u, u} X (integralCoefficientCommRingSheaf l E X n)
          (G.obj Q) (G.obj P) j i U
          ((IntegralHom.reductionUnit l E X D hl n (Q.X j)).val.app U y)
          ((IntegralHom.reductionUnit l E X D hl n (P.X i)).val.app U x)))
        (component_transport β' (add_comm j i))
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply] at htransport
      rw [← htransport, hβ'pure]
      exact unit_eqToHom_apply D l hl E X n _ U _
    have : IsIso β := hβ
    have : IsIso β' := hβ'
    have : IsIso (IntegralHom.reductionCounit l E X D hl n P) :=
      counit_iso D l hl E X n P hp
    have : IsIso (IntegralHom.reductionCounit l E X D hl n Q) :=
      counit_iso D l hl E X n Q hq
    have : IsIso (Prod.mkHom (IntegralHom.reductionCounit l E X D hl n P)
        (IntegralHom.reductionCounit l E X D hl n Q)) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have : IsIso (Prod.mkHom (IntegralHom.reductionCounit l E X D hl n Q)
        (IntegralHom.reductionCounit l E X D hl n P)) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    apply normalized_square
      (F.mapIso (a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)))
      (F.mapIso (a.representative.app (⟨Q, hq⟩, ⟨P, hp⟩)))
      (m.mu.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
      (m.mu.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
      (asIso (m.target.tensor.map (Prod.mkHom
        (IntegralHom.reductionCounit l E X D hl n P)
        (IntegralHom.reductionCounit l E X D hl n Q))))
      (asIso (m.target.tensor.map (Prod.mkHom
        (IntegralHom.reductionCounit l E X D hl n Q)
        (IntegralHom.reductionCounit l E X D hl n P))))
      (m.target.representative.app (⟨G.obj P, hp'⟩, ⟨G.obj Q, hq'⟩))
      (m.target.representative.app (⟨G.obj Q, hq'⟩, ⟨G.obj P, hp'⟩))
      (DerivedCategory.Q.mapIso (asIso β)) (DerivedCategory.Q.mapIso (asIso β'))
      _ (F.map (DerivedCategory.Q.map σ)) _ (DerivedCategory.Q.map τ)
      (IntegralHom.reductionCounit l E X D hl n _)
      (IntegralHom.reductionCounit l E X D hl n _)
      (DerivedCategory.Q.map (G.map σ))
    · simpa only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
        ← F.map_comp] using congrArg F.map hσsquare
    · simpa only [asIso_hom, Iso.app_inv, Iso.app_hom, Category.assoc, hτsquare,
        Functor.comp_obj, Functor.prod_obj, integralDerivedReduction, F, G] using
        ht _ _ _ _ (IntegralHom.reductionCounit l E X D hl n P)
          (IntegralHom.reductionCounit l E X D hl n Q)
    · exact hβsquare
    · exact hβ'square
    · exact counit_naturality D l hl E X n σ
    · simpa only [Functor.map_comp, Functor.mapIso_hom, asIso_hom] using
        (congrArg DerivedCategory.Q.map hchain).symm
  have hrepresent (M : Ambient l E X) :
      ∃ P : CochainComplex (scalarReductionSource l E X) ℤ,
        IntegralHom.flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P ∧
          Nonempty (DerivedCategory.Q.obj P ≅ M) := by
    let A := DerivedCategory.Q.objPreimage M
    obtain ⟨P, p, hp, _, hqi, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheaf l E X D hl) A
    have := hqi
    exact ⟨P, hp, ⟨asIso (DerivedCategory.Q.map p) ≪≫
      DerivedCategory.Q.objObjPreimageIso M⟩⟩
  obtain ⟨P, hp, ⟨eP⟩⟩ := hrepresent K
  obtain ⟨Q, hq, ⟨eQ⟩⟩ := hrepresent L
  have hhom := transport_square a.tensor m.target.tensor F m.mu s.swap t.swap hs ht
    eP eQ (hrep P Q hp hq)
  apply (cancel_epi (m.mu.hom.app (K, L))).mp
  apply (cancel_mono (m.mu.hom.app (L, K))).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc,
    Category.comp_id, Functor.comp_obj, Functor.prod_obj, integralDerivedReduction, F]
      using hhom

end WeilConjectures.IntegralVerdier
