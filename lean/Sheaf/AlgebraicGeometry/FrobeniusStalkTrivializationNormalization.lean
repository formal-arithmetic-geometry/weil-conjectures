/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import Mathlib.FieldTheory.Perfect
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Normalization of the absolute-Frobenius stalk trivialization

Source: Stacks Project, `more-morphisms.tex`, Tag 0F6W
(blueprint: lem-trf-frobenius-stalk-trivialization-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Cancellation of the inverse field reparametrization on a geometric point.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
theorem frobeniusNormalization_inverse_point {k : Type u} [Field k] (δ : k ≃+* k)
    {T : Scheme.{u}} (x : Spec (.of k) ⟶ T) :
    Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x = x := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simp

/-- Identity-point form of a specified scheme-map equality.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
theorem frobeniusNormalization_identity_point {S : Scheme.{u}}
    {f g : S ⟶ S} (h : f = g) : f ≫ 𝟙 S = 𝟙 S ≫ g := by
  simpa only [Category.comp_id, Category.id_comp] using h

/-- The projection formula specifying the relative-Frobenius site isomorphism.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationSite (p : ℕ) (hp : p.Prime) (b : ℕ)
    {T : Scheme.{u}} (f : T ⟶ T) (r : 𝟭 T.ProEt ≅ proEtaleBaseChange f) : Prop :=
  ∀ V : T.ProEt, ∃ hV : (p : Γ(V.left, ⊤)) = 0,
    (r.hom.app V).left ≫ pullback.fst V.hom f = V.left.iterateFrobenius hp hV b

/-- The sectionwise adjunction-unit equation specifying the module trivialization.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationUnit {T : Scheme.{u}} (f : T ⟶ T)
    (A : Type u) [CommRing A] (r : 𝟭 T.ProEt ≅ proEtaleBaseChange f)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (V : T.ProEt) (a : M.val.obj (op V)),
    ((proEtaleConstantRingAdjunction A f).unit.app M ≫
      (proEtaleConstantRingPushforward A f).map (tau.hom.app M)).val.app (op V) a =
        M.val.map (r.inv.app V).op a

set_option backward.isDefEq.respectTransparency.types false in
/-- The germs clause of inverse-Frobenius normalization, with the map and point
kept as parameters to avoid expanding their constructions during type comparison.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationGerms
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x y : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (α : k ≃+* k) (hx : y = x ≫ f)
    (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood
      y)
    (a : M.val.obj (op N.right)),
  (eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hx) ≫
    (proEtalePullbackStalkComparison A
      f x).inv.app M ≫
    (finiteCoefficientModuleStalkFunctor x A).map (tau.hom.app M))
      (proEtaleCoefficientModuleGerm
        y A M N a) =
  eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hα)
    ((proEtaleStalkReparam A
      y α).hom.app M
      (proEtaleCoefficientModuleGerm
        y A M N a))

set_option backward.isDefEq.respectTransparency.types false in
/-- The maps clause of inverse-Frobenius normalization, with the map and point
kept as parameters to avoid expanding their constructions during type comparison.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationMaps
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x y : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (α : k ≃+* k) (hx : y = x ≫ f)
    (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A)),
  eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hx) ≫
    (proEtalePullbackStalkComparison A
      f x).inv.app M ≫
    (finiteCoefficientModuleStalkFunctor x A).map (tau.hom.app M) =
  (proEtaleStalkReparam A y
    α).hom.app M ≫
    eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
      hα)

set_option backward.isDefEq.respectTransparency.types false in
/-- The derived clause of inverse-Frobenius normalization, with the map and point
kept as parameters to avoid expanding their constructions during type comparison.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationDerived
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x y : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (α : k ≃+* k) (hx : y = x ≫ f)
    (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _) : Prop :=
  ∀ (H : CochainComplex (proEtaleRingModules T
    (proEtaleConstantRing T A)) ℤ),
  (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
  eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
      (DerivedCategory.Q.obj H)) hx) ≫
    (proEtaleDerivedPullbackStalkComparison A
      f x).inv.app (DerivedCategory.Q.obj H) ≫
    (proEtaleFiniteCoefficientDerivedStalk A x).map
      ((proEtaleFrobeniusDerivedIso A tau).hom.app (DerivedCategory.Q.obj H)) =
  (proEtaleDerivedStalkReparam A
    y α).hom.app
      (DerivedCategory.Q.obj H) ≫
    eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
      (DerivedCategory.Q.obj H))
      hα)

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback compatibility with field reparametrization in the normalization formula.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationReparametrization
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (z : Spec (.of k) ⟶ X) (A : Type u) [CommRing A] [Finite A]
    (δ : k ≃+* k) : Prop :=
  ∀ (M : proEtaleRingModules X
    (proEtaleConstantRing X A)),
  (proEtalePullbackStalkComparison A z (𝟙 _)).hom.app M ≫
    (proEtaleStalkReparam A (𝟙 _ ≫ z) δ).hom.app M =
  (proEtaleStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
      ((proEtaleConstantRingPullback A z).obj M) ≫
    (proEtalePullbackStalkComparison A z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app M ≫
    eqToHom (congrArg (fun w =>
        (finiteCoefficientModuleStalkFunctor w A).obj M)
      (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
        (𝟙 (Spec (.of k))) z))

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback compatibility with field reparametrization in the normalization formula.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationDerivedReparametrization
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (z : Spec (.of k) ⟶ X) (A : Type u) [CommRing A] [Finite A]
    (δ : k ≃+* k) : Prop :=
  ∀ (H : CochainComplex (proEtaleRingModules X
    (proEtaleConstantRing X A)) ℤ),
  (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
  (proEtaleDerivedPullbackStalkComparison A z (𝟙 _)).hom.app
      (DerivedCategory.Q.obj H) ≫
    (proEtaleDerivedStalkReparam A (𝟙 _ ≫ z) δ).hom.app
      (DerivedCategory.Q.obj H) =
  (proEtaleDerivedStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
      ((proEtaleConstantRingDerivedPullback A z).obj
        (DerivedCategory.Q.obj H)) ≫
    (proEtaleDerivedPullbackStalkComparison A z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app
      (DerivedCategory.Q.obj H) ≫
    eqToHom (congrArg (fun w =>
        (proEtaleFiniteCoefficientDerivedStalk A w).obj
          (DerivedCategory.Q.obj H))
      (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
        (𝟙 (Spec (.of k))) z))

/-- The unit-normalized pullback composition comparison used in normalization.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationComposition (A : Type u) [CommRing A]
    (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
      proEtaleConstantRingPullback A (f ≫ g) ≅
        proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f) : Prop :=
  ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
                (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
                (V : W.ProEt)
                (m : ((proEtaleConstantRingPushforward A f ⋙
                  proEtaleConstantRingPushforward A g).obj M).val.obj (op V)),
              ((conjugateIsoEquiv
                ((proEtaleConstantRingAdjunction A g).comp
                  (proEtaleConstantRingAdjunction A f))
                (proEtaleConstantRingAdjunction A (f ≫ g))
                (comp f g)).hom.app M).val.app (op V) m =
                M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m

/-- The derived naturality equation for the specified Frobenius trivializations.
Source: Stacks Tag 0F6W (blueprint: lem-trf-frobenius-stalk-trivialization-normalization). -/
def FrobeniusNormalizationNaturality (A : Type u) [CommRing A]
    (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
      proEtaleConstantRingPullback A (f ≫ g) ≅
        proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f)
    {T X : Scheme.{u}} (t : T ⟶ X) (f : T ⟶ T) (g : X ⟶ X)
    (tauT : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (tauX : proEtaleConstantRingPullback A g ≅ 𝟭 _) : Prop :=
  ∃ (w : f ≫ t =
                t ≫ g),
              (proEtaleFrobeniusDerivedComp A t
                g
                (comp t g)).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  f t
                  (comp f t)).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A t)
                  (proEtaleFrobeniusDerivedIso A tauT).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight
                (proEtaleFrobeniusDerivedIso A tauX).hom
                (proEtaleConstantRingDerivedPullback A t) ≫
                (Functor.leftUnitor _).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized inverse-Frobenius formula on geometric pro-etale stalks.

Source: Stacks Project, `more-morphisms.tex`, Tag 0F6W, and the normalized stalk
calculation in the proof of `lem-trf-local-frobenius-conjugacy`
(blueprint: lem-trf-frobenius-stalk-trivialization-normalization).
-/
def FrobeniusStalkTrivializationNormalized
    (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [IsAlgClosed k]
    (hs : (Spec (.of k)).IsCharacteristic p) (X : Scheme.{u})
    (hX : X.IsCharacteristic p) (z : Spec (.of k) ⟶ X)
    (A : Type u) [CommRing A] [Finite A] : Prop :=
  ∀ b : ℕ,
    ∃ (δ : k ≃+* k),
      (∀ x : k, δ x = x ^ p ^ b) ∧
      ∃ (_hδS : Spec.map (CommRingCat.ofHom δ.toRingHom) =
          (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b),
      ∃ (_hz : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z =
          z ≫ X.iterateFrobenius hp (hX.2 ⊤) b),
        ∃ (rS : 𝟭 (Spec (.of k)).ProEt ≅ proEtaleBaseChange
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b))
          (rX : 𝟭 X.ProEt ≅ proEtaleBaseChange
            (X.iterateFrobenius hp (hX.2 ⊤) b))
          (tauS : proEtaleConstantRingPullback A
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) ≅ 𝟭 _)
          (tauX : proEtaleConstantRingPullback A
            (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _),
          FrobeniusNormalizationSite p hp b
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) rS ∧
          FrobeniusNormalizationSite p hp b (X.iterateFrobenius hp (hX.2 ⊤) b) rX ∧
          FrobeniusNormalizationUnit ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) A rS tauS ∧
          FrobeniusNormalizationUnit (X.iterateFrobenius hp (hX.2 ⊤) b) A rX tauX ∧
          FrobeniusNormalizationGerms (X.iterateFrobenius hp (hX.2 ⊤) b) z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A δ.symm _hz
      (frobeniusNormalization_inverse_point δ z) tauX ∧
          FrobeniusNormalizationReparametrization z A δ ∧
          FrobeniusNormalizationDerivedReparametrization z A δ ∧
          FrobeniusNormalizationGerms ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)
            (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _) A δ.symm
            (frobeniusNormalization_identity_point _hδS)
            (frobeniusNormalization_inverse_point δ (𝟙 _)) tauS ∧
          FrobeniusNormalizationMaps ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)
            (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _) A δ.symm
            (frobeniusNormalization_identity_point _hδS)
            (frobeniusNormalization_inverse_point δ (𝟙 _)) tauS ∧
          FrobeniusNormalizationMaps (X.iterateFrobenius hp (hX.2 ⊤) b) z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A δ.symm _hz
      (frobeniusNormalization_inverse_point δ z) tauX ∧
          FrobeniusNormalizationDerived ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)
            (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _) A δ.symm
            (frobeniusNormalization_identity_point _hδS)
            (frobeniusNormalization_inverse_point δ (𝟙 _)) tauS ∧
          ∃ (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
              proEtaleConstantRingPullback A (f ≫ g) ≅
                proEtaleConstantRingPullback A g ⋙
                  proEtaleConstantRingPullback A f),
            FrobeniusNormalizationComposition A comp ∧
            FrobeniusNormalizationNaturality A comp z
              ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b)
              (X.iterateFrobenius hp (hX.2 ⊤) b) tauS tauX ∧
          FrobeniusNormalizationDerived (X.iterateFrobenius hp (hX.2 ⊤) b) z
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A δ.symm _hz
      (frobeniusNormalization_inverse_point δ z) tauX

set_option backward.isDefEq.respectTransparency.types false in
private theorem frobenius_naturality {T U : Scheme.{u}} (f : T ⟶ U)
    {p : ℕ} (hp : p.Prime) (hT : (p : Γ(T, ⊤)) = 0)
    (hU : (p : Γ(U, ⊤)) = 0) (b : ℕ) :
    T.iterateFrobenius hp hT b ≫ f = f ≫ U.iterateFrobenius hp hU b := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro V
  simp only [Scheme.Hom.comp_app]
  change f.app V ≫ (T.iterateFrobenius hp hT b).app (f ⁻¹ᵁ V) ≫
    T.presheaf.map (𝟙 _) = (U.iterateFrobenius hp hU b).app V ≫ f.app V
  rw [T.presheaf.map_id, Category.comp_id]
  ext a
  exact (map_pow (f.app V).hom a (p ^ b)).symm

private theorem field_frobenius (p : ℕ) (hp : p.Prime) (k : Type u)
    [Field k] [IsAlgClosed k] (hs : (Spec (.of k)).IsCharacteristic p) (b : ℕ) :
    ∃ δ : k ≃+* k, (∀ x : k, δ x = x ^ p ^ b) ∧
      Spec.map (CommRingCat.ofHom δ.toRingHom) =
        (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b := by
  have hk : (p : k) = 0 := by
    have h := congrArg (Scheme.ΓSpecIso (.of k)).hom (hs.2 ⊤)
    simpa using h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 hk
  refine ⟨iterateFrobeniusEquiv k p b, (fun x ↦ ?_), ?_⟩
  · exact iterateFrobeniusEquiv_def k p b x
  · symm
    apply AlgebraicGeometry.ext_to_Spec
    change (Scheme.ΓSpecIso (.of k)).inv ≫
        ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b).appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusEquiv k p b).toRingHom)).appTop
    rw [← Scheme.ΓSpecIso_inv_naturality]
    ext x
    exact (map_pow (Scheme.ΓSpecIso (.of k)).inv.hom x (p ^ b)).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem stalk_map_germ (A : Type u) [CommRing A]
    {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ T)
    {M M' : proEtaleRingModules T (proEtaleConstantRing T A)} (f : M ⟶ M')
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)) :
    (finiteCoefficientModuleStalkFunctor x A).map f
        (proEtaleCoefficientModuleGerm x A M N a) =
      proEtaleCoefficientModuleGerm x A M' N (f.val.app (op N.right) a) := by
  let F := PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget x)
    ((proEtaleConstantRing T A).obj ⋙ forget₂ CommRingCat RingCat)
  exact PresheafOfModules.ModuleColimit.map_apply
    (colimit.isColimit (proEtaleGeometricStalkRingDiagram x (proEtaleConstantRing T A)))
    (colimit.isColimit (F.obj M.val).presheaf)
    (colimit.isColimit (F.obj M'.val).presheaf) (F.map f.val) a

set_option backward.isDefEq.respectTransparency.types false in
private theorem stalk_germ_ext (A : Type u) [CommRing A]
    {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ T)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    {L : ModuleCat.{u + 1} (ULift.{u + 1, u} A)}
    {f g : (finiteCoefficientModuleStalkFunctor x A).obj M ⟶ L}
    (h : ∀ (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)),
      f (proEtaleCoefficientModuleGerm x A M N a) =
        g (proEtaleCoefficientModuleGerm x A M N a)) : f = g := by
  ext a
  obtain ⟨N, m, hm⟩ := PresheafOfModules.ModuleColimit.ιM_jointly_surjective
    (hcR := colimit.isColimit (proEtaleGeometricStalkRingDiagram x
      (proEtaleConstantRing T A)))
    (hcM := colimit.isColimit ((proEtaleGeometricNeighbourhoodForget x).op ⋙
      M.val.presheaf)) a
  change proEtaleCoefficientModuleGerm x A M N.unop m = a at hm
  rw [← hm]
  exact h N.unop m

private theorem germ_cast (A : Type u) [CommRing A]
    {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    {x y : Spec (.of k) ⟶ T} (h : x = y)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)) :
    eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M) h)
        (proEtaleCoefficientModuleGerm x A M N a) =
      proEtaleCoefficientModuleGerm y A M
        (StructuredArrow.mk (Over.homMk N.hom.left (N.hom.w.trans h))) a := by
  subst y
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem germ_relation (A : Type u) [CommRing A]
    {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ T)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    {N P : ProEtaleGeometricNeighbourhood x} (e : N ⟶ P)
    (a : M.val.obj (op P.right)) :
    proEtaleCoefficientModuleGerm x A M N (M.val.map e.right.op a) =
      proEtaleCoefficientModuleGerm x A M P a := by
  exact ConcreteCategory.congr_hom
    (colimit.w ((proEtaleGeometricNeighbourhoodForget x).op ⋙ M.val.presheaf) e.op) a

set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_pushforward_apply (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (f : T ⟶ S)
    (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (P Q : proEtaleRingModules T (proEtaleConstantRing T A))
    (g : M ⟶ (proEtaleConstantRingPushforward A f).obj P) (h : P ⟶ Q)
    (V : S.ProEt) (a : M.val.obj (op V)) :
    ((g ≫ (proEtaleConstantRingPushforward A f).map h).val.app (op V)) a =
      h.val.app (op ((proEtaleBaseChange f).obj V)) (g.val.app (op V) a) := rfl

private theorem reparam_cast_germ (A : Type u) [CommRing A]
    {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (x y : Spec (.of k) ⟶ T) (α : k ≃+* k)
    (h : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x = y)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)) :
    eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M) h)
      ((proEtaleStalkReparam A x α).hom.app M (proEtaleCoefficientModuleGerm x A M N a)) =
      proEtaleCoefficientModuleGerm y A M
        (StructuredArrow.mk (Over.homMk
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ N.hom.left)
          ((Category.assoc _ _ _).trans ((congrArg (fun f ↦
            Spec.map (CommRingCat.ofHom α.toRingHom) ≫ f) N.hom.w).trans h)))) a := by
  have hr := (proEtaleStalkReparam_existsUnique A x α).exists.choose_spec M N a
  exact (congrArg (fun m ↦ eqToHom
    (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M) h) m) hr).trans
      (germ_cast A h M ((proEtaleStalkNeighbourhoodReparam x α).obj N) a)

private theorem comparison_germ_inv (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (f : T ⟶ S) {k : Type u} [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ T)
    (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (N : ProEtaleGeometricNeighbourhood (x ≫ f))
    (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange f).obj N.right))
    (a : M.val.obj (op N.right))
    (hl : l.left ≫ pullback.fst N.right.hom f = N.hom.left) :
    (proEtalePullbackStalkComparison A f x).inv.app M
      (proEtaleCoefficientModuleGerm _ A M N a) =
      proEtaleCoefficientModuleGerm x A ((proEtaleConstantRingPullback A f).obj M)
        (StructuredArrow.mk l)
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (op N.right) a) :=
  (proEtalePullbackStalkComparison_existsUnique A f x).exists.choose_spec.2 M N l a hl

set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_germ_of_lift
    {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (f : T ⟶ T) (x : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (y : Spec (.of k) ⟶ T) (α : k ≃+* k)
    (hx : y = x ≫ f) (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (r : 𝟭 T.ProEt ≅ proEtaleBaseChange f)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (htau : ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
      (V : T.ProEt) (a : M.val.obj (op V)),
      ((proEtaleConstantRingAdjunction A f).unit.app M ≫
        (proEtaleConstantRingPushforward A f).map (tau.hom.app M)).val.app (op V) a =
          M.val.map (r.inv.app V).op a)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood y)
    (a : M.val.obj (op N.right))
    (hv : (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ N.hom.left) ≫ N.right.hom = x)
    (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange f).obj N.right))
    (hlift : l.left = (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ N.hom.left) ≫
      (r.hom.app N.right).left)
    (hl : l.left ≫ pullback.fst N.right.hom f = N.hom.left) :
    (eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M) hx) ≫
      (proEtalePullbackStalkComparison A f x).inv.app M ≫
      (finiteCoefficientModuleStalkFunctor x A).map (tau.hom.app M))
        (proEtaleCoefficientModuleGerm _ A M N a) =
    eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M)
      (hα))
      ((proEtaleStalkReparam A y
        α).hom.app M (proEtaleCoefficientModuleGerm _ A M N a)) := by
  let v := Spec.map (CommRingCat.ofHom α.toRingHom) ≫ N.hom.left
  let Nc : ProEtaleGeometricNeighbourhood
      (x ≫ f) :=
    StructuredArrow.mk (Over.homMk N.hom.left (N.hom.w.trans hx))
  have hi := comparison_germ_inv A f x M Nc l a hl
  have hu := (unit_pushforward_apply A f M
    _ _ ((proEtaleConstantRingAdjunction A f).unit.app M)
      (tau.hom.app M) N.right a).symm.trans (htau M N.right a)
  let N' : ProEtaleGeometricNeighbourhood x := StructuredArrow.mk (Over.homMk v hv)
  let e : StructuredArrow.mk l ⟶ N' :=
    StructuredArrow.homMk (r.inv.app N.right) (by
      apply Over.OverMorphism.ext
      change l.left ≫ (r.inv.app N.right).left = v
      rw [hlift]
      have hi : (r.hom.app N.right).left ≫ (r.inv.app N.right).left = 𝟙 _ :=
        congrArg (fun f ↦ f.left) (r.hom_inv_id_app N.right)
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ v ≫ f) hi).trans (Category.comp_id v)))
  have hright :
      eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M)
        (hα))
        ((proEtaleStalkReparam A y
          α).hom.app M (proEtaleCoefficientModuleGerm _ A M N a)) =
        proEtaleCoefficientModuleGerm x A M N' a :=
    reparam_cast_germ A y x α hα M N a
  exact (congrArg (fun m ↦ (finiteCoefficientModuleStalkFunctor x A).map
    (tau.hom.app M) ((proEtalePullbackStalkComparison A f x).inv.app M m))
      (germ_cast A hx M N a)).trans
    ((congrArg (fun m ↦ (finiteCoefficientModuleStalkFunctor x A).map
      (tau.hom.app M) m) hi).trans
      ((stalk_map_germ A x (tau.hom.app M) (StructuredArrow.mk l) _).trans
        ((congrArg (fun a ↦ proEtaleCoefficientModuleGerm x A M
          (StructuredArrow.mk l) a) hu).trans
          ((germ_relation A x M e a).trans hright.symm))))

set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_germ (p : ℕ) (hp : p.Prime) (k : Type u)
    [Field k] [IsAlgClosed k] (hs : (Spec (.of k)).IsCharacteristic p)
    (T : Scheme.{u}) (hT : T.IsCharacteristic p) (x : Spec (.of k) ⟶ T)
    (A : Type u) [CommRing A] [Finite A] (b : ℕ) (δ : k ≃+* k)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) =
      (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b)
    (hx : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x =
      x ≫ T.iterateFrobenius hp (hT.2 ⊤) b)
    (r : 𝟭 T.ProEt ≅ proEtaleBaseChange (T.iterateFrobenius hp (hT.2 ⊤) b))
    (tau : proEtaleConstantRingPullback A (T.iterateFrobenius hp (hT.2 ⊤) b) ≅ 𝟭 _)
    (hr : ∀ V : T.ProEt, ∃ hV : (p : Γ(V.left, ⊤)) = 0,
      (r.hom.app V).left ≫ pullback.fst V.hom (T.iterateFrobenius hp (hT.2 ⊤) b) =
        V.left.iterateFrobenius hp hV b)
    (htau : ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
      (V : T.ProEt) (a : M.val.obj (op V)),
      ((proEtaleConstantRingAdjunction A (T.iterateFrobenius hp (hT.2 ⊤) b)).unit.app M ≫
        (proEtaleConstantRingPushforward A (T.iterateFrobenius hp (hT.2 ⊤) b)).map
          (tau.hom.app M)).val.app (op V) a = M.val.map (r.inv.app V).op a) :
    FrobeniusNormalizationGerms (T.iterateFrobenius hp (hT.2 ⊤) b) x
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x) A δ.symm hx
      (frobeniusNormalization_inverse_point δ x) tau := by
  intro M N a
  let v := Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫ N.hom.left
  have hv : v ≫ N.right.hom = x := by
    change (Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫ N.hom.left) ≫
      N.right.hom = x
    have hw : N.hom.left ≫ N.right.hom =
        Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x := N.hom.w
    rw [Category.assoc, hw]
    exact frobeniusNormalization_inverse_point δ x
  let N' : ProEtaleGeometricNeighbourhood x := StructuredArrow.mk (Over.homMk v hv)
  let l : Over.mk x ⟶
      (ProEt.forget T).obj
        ((proEtaleBaseChange (T.iterateFrobenius hp (hT.2 ⊤) b)).obj N.right) :=
    Over.homMk (v ≫ (r.hom.app N.right).left) (by
      change (v ≫ (r.hom.app N.right).left) ≫
        ((proEtaleBaseChange (T.iterateFrobenius hp (hT.2 ⊤) b)).obj N.right).hom = x
      have hw : (r.hom.app N.right).left ≫
          ((proEtaleBaseChange (T.iterateFrobenius hp (hT.2 ⊤) b)).obj N.right).hom =
          N.right.hom := (r.hom.app N.right).w
      rw [Category.assoc, hw]
      exact hv)
  have hl : l.left ≫ pullback.fst N.right.hom
      (T.iterateFrobenius hp (hT.2 ⊤) b) = N.hom.left := by
    obtain ⟨hV, hVeq⟩ := hr N.right
    have hn : (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b ≫ N.hom.left =
        N.hom.left ≫ N.right.left.iterateFrobenius hp hV b :=
      frobenius_naturality N.hom.left hp (hs.2 ⊤) hV b
    calc
      l.left ≫ pullback.fst N.right.hom _ =
          v ≫ ((r.hom.app N.right).left ≫ pullback.fst N.right.hom _) :=
        Category.assoc _ _ _
      _ = v ≫ N.right.left.iterateFrobenius hp hV b :=
        congrArg (fun f ↦ v ≫ f) hVeq
      _ = Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
          (N.hom.left ≫ N.right.left.iterateFrobenius hp hV b) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
          ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b ≫ N.hom.left) :=
        congrArg (fun f ↦ Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫ f) hn.symm
      _ = Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ N.hom.left) :=
        congrArg (fun f ↦ Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
          (f ≫ N.hom.left)) hδ.symm
      _ = N.hom.left := frobeniusNormalization_inverse_point δ N.hom.left
  exact normalized_germ_of_lift _ x A _ δ.symm hx (frobeniusNormalization_inverse_point δ x)
    r tau htau M N a hv l rfl hl


set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_map
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x y : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (α : k ≃+* k) (hx : y = x ≫ f)
    (hα : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ y = x)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (hg : FrobeniusNormalizationGerms f x y A α hx hα tau) :
    FrobeniusNormalizationMaps f x y A α hx hα tau := by
  intro M
  apply stalk_germ_ext A _ M
  exact hg M


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derive_trivialization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ C) (S T : C ⥤ D)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (tau : P ≅ 𝟭 C) (c : P ⋙ S ≅ T) (e : T ≅ S)
    (h : c.symm ≪≫ isoWhiskerRight tau S ≪≫ S.leftUnitor = e) :
    (Functor.mapDerivedCategoryNatIso c).inv ≫
      (Functor.mapDerivedCategoryCompIso P S).hom ≫
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso tau ≪≫ Functor.mapDerivedCategoryIdIso C).hom
        S.mapDerivedCategory = (Functor.mapDerivedCategoryNatIso e).hom := by
  have hu : S.leftUnitor = Iso.refl S := by ext; rfl
  rw [← h, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    hu]
  simp only [Functor.mapDerivedCategoryNatIso_refl (F := S)]
  simp only [Iso.trans_hom, Functor.whiskerRight_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight tau S)]
  rw [Functor.mapDerivedCategoryCompIso_id_comp]

private theorem derive_normalized
    {C D I : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ C) (F : I → C ⥤ D)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [∀ i, PreservesFiniteColimits (F i)]
    (s t v w : I) (hvt : v = t) (hws : w = s)
    (tau : P ≅ 𝟭 C) (c : P ⋙ F s ≅ F t) (e : F v ≅ F w)
    (hm : ∀ M : C,
      eqToHom (congrArg (fun i ↦ (F i).obj M) hvt) ≫ c.inv.app M ≫
        (F s).map (tau.hom.app M) = e.hom.app M ≫
          eqToHom (congrArg (fun i ↦ (F i).obj M) hws))
    (H : DerivedCategory C) :
    eqToHom (congrArg (fun i ↦ (F i).mapDerivedCategory.obj H) hvt) ≫
      (Functor.mapDerivedCategoryNatIso c).inv.app H ≫
      (Functor.mapDerivedCategoryCompIso P (F s)).hom.app H ≫
      (F s).mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso tau ≪≫
        Functor.mapDerivedCategoryIdIso C).hom.app H) =
    (Functor.mapDerivedCategoryNatIso e).hom.app H ≫
      eqToHom (congrArg (fun i ↦ (F i).mapDerivedCategory.obj H) hws) := by
  subst v
  subst w
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm ⊢
  have he : c.symm ≪≫ isoWhiskerRight tau (F s) ≪≫ (F s).leftUnitor = e := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    change c.inv.app M ≫ (F s).map (tau.hom.app M) ≫ 𝟙 _ = e.hom.app M
    rw [Category.comp_id]
    exact hm M
  have hd := congrArg (fun f ↦ f.app H) (derive_trivialization P (F s) (F t) tau c e he)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc] using hd

set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_derived_of_map
    {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (f : T ⟶ T) (x : Spec (.of k) ⟶ T) (A : Type u) [CommRing A]
    (δ : k ≃+* k) (hx : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x = x ≫ f)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (hm : ∀ M : proEtaleRingModules T (proEtaleConstantRing T A),
      eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M) hx) ≫
        (proEtalePullbackStalkComparison A f x).inv.app M ≫
        (finiteCoefficientModuleStalkFunctor x A).map (tau.hom.app M) =
      (proEtaleStalkReparam A (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x)
        δ.symm).hom.app M ≫
        eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M)
          (frobeniusNormalization_inverse_point δ x)))
    (H : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    eqToHom (congrArg (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj
        (DerivedCategory.Q.obj H)) hx) ≫
      (proEtaleDerivedPullbackStalkComparison A f x).inv.app (DerivedCategory.Q.obj H) ≫
      (proEtaleFiniteCoefficientDerivedStalk A x).map
        ((proEtaleFrobeniusDerivedIso A tau).hom.app (DerivedCategory.Q.obj H)) =
    (proEtaleDerivedStalkReparam A (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x)
      δ.symm).hom.app (DerivedCategory.Q.obj H) ≫
      eqToHom (congrArg (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj
        (DerivedCategory.Q.obj H)) (frobeniusNormalization_inverse_point δ x)) := by
  have h := derive_normalized (proEtaleConstantRingPullback A f)
    (fun w ↦ finiteCoefficientModuleStalkFunctor w A)
    x (x ≫ f) _ _ hx (frobeniusNormalization_inverse_point δ x)
    tau (proEtalePullbackStalkComparison A f x)
    (proEtaleStalkReparam A (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x) δ.symm)
    hm (DerivedCategory.Q.obj H)
  change eqToHom _ ≫
    ((Functor.mapDerivedCategoryNatIso (proEtalePullbackStalkComparison A f x)).inv.app
      (DerivedCategory.Q.obj H) ≫
      (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A f)
        (finiteCoefficientModuleStalkFunctor x A)).hom.app (DerivedCategory.Q.obj H)) ≫
      (finiteCoefficientModuleStalkFunctor x A).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso tau ≪≫ Functor.mapDerivedCategoryIdIso _).hom.app
          (DerivedCategory.Q.obj H)) =
    (Functor.mapDerivedCategoryNatIso (proEtaleStalkReparam A
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x) δ.symm)).hom.app
      (DerivedCategory.Q.obj H) ≫ _
  exact (congrArg (fun q ↦ eqToHom (congrArg (fun w ↦
    (proEtaleFiniteCoefficientDerivedStalk A w).obj (DerivedCategory.Q.obj H)) hx) ≫ q)
    (Category.assoc _ _ _)).trans h


set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_derived
    {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}}
    (f : T ⟶ T) (x : Spec (.of k) ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (δ : k ≃+* k) (hx : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x = x ≫ f)
    (tau : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (hm : FrobeniusNormalizationMaps f x
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x) A δ.symm hx
      (frobeniusNormalization_inverse_point δ x) tau) :
    FrobeniusNormalizationDerived f x
      (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ x) A δ.symm hx
      (frobeniusNormalization_inverse_point δ x) tau := by
  intro H _
  exact normalized_derived_of_map f x A δ hx tau hm H


set_option backward.isDefEq.respectTransparency false in
private theorem identity_reparam
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (z : Spec (.of k) ⟶ X) (A : Type u) [CommRing A] [Finite A] (δ : k ≃+* k) :
    FrobeniusNormalizationReparametrization z A δ := by
  intro M
  have hh := (proEtalePullbackStalkCoherence A).2.2.2.1 z (𝟙 _) δ M
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem derived_identity_reparam
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (z : Spec (.of k) ⟶ X) (A : Type u) [CommRing A] [Finite A] (δ : k ≃+* k) :
    FrobeniusNormalizationDerivedReparametrization z A δ := by
  intro H hH
  have hh := (proEtalePullbackStalkCoherence A).2.2.2.2.2.2.2 z (𝟙 _) δ H hH
  exact hh

set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_from_data
    (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [IsAlgClosed k]
    (hs : (Spec (.of k)).IsCharacteristic p) (X : Scheme.{u})
    (hX : X.IsCharacteristic p) (z : Spec (.of k) ⟶ X)
    (A : Type u) [CommRing A] [Finite A]
    (r : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
        𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n))
    (hr : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
        ∃ hV : (p : Γ(V.left, ⊤)) = 0,
          ((r X hX n).hom.app V).left ≫
              pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
            V.left.iterateFrobenius hp hV n)
    (comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
          proEtaleConstantRingPullback A (f ≫ g) ≅
            proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f)
    (hcomp : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
          (m : ((proEtaleConstantRingPushforward A f ⋙
            proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)),
          ((conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
            (proEtaleConstantRingAdjunction A (f ≫ g)) (comp f g)).hom.app M).val.app
              (Opposite.op V) m =
            M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m)
    (tau : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
            proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) n) ≅ 𝟭 _)
    (htau : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
            (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : X.ProEt)
            (m : M.val.obj (Opposite.op V)),
            ((proEtaleConstantRingAdjunction A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).map ((tau X hX n).hom.app M)).val.app
                  (Opposite.op V) m = M.val.map ((r X hX n).inv.app V).op m)
    (hnat : ∀ (X Y : Scheme.{u}) (hX : X.IsCharacteristic p)
            (hY : Y.IsCharacteristic p) (u : X ⟶ Y) (b : ℕ),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) b ≫ u =
                u ≫ Y.iterateFrobenius hp (hY.2 ⊤) b,
              (proEtaleFrobeniusDerivedComp A u
                (Y.iterateFrobenius hp (hY.2 ⊤) b)
                (comp u (Y.iterateFrobenius hp (hY.2 ⊤) b))).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  (X.iterateFrobenius hp (hX.2 ⊤) b) u
                  (comp (X.iterateFrobenius hp (hX.2 ⊤) b) u)).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A u)
                  (proEtaleFrobeniusDerivedIso A (tau X hX b)).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight
                (proEtaleFrobeniusDerivedIso A (tau Y hY b)).hom
                (proEtaleConstantRingDerivedPullback A u) ≫
                (Functor.leftUnitor _).hom)
    (delta : ℕ → k ≃+* k)
    (hpower : ∀ b x, delta b x = x ^ p ^ b)
    (hdelta : ∀ b, Spec.map (CommRingCat.ofHom (delta b).toRingHom) =
      (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) :
    FrobeniusStalkTrivializationNormalized p hp k hs X hX z A := by
  classical
  intro b
  let δ := delta b
  have hpow := hpower b
  have hδ := hdelta b
  have hz : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z =
      z ≫ X.iterateFrobenius hp (hX.2 ⊤) b := by
    rw [hδ]
    exact frobenius_naturality z hp (hs.2 ⊤) (hX.2 ⊤) b
  have hid : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 (Spec (.of k)) =
      (𝟙 (Spec (.of k))) ≫ (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b := by
    simpa only [Category.comp_id, Category.id_comp] using hδ
  have hgX := normalized_germ p hp k hs X hX z A b δ hδ hz
    (r X hX b) (tau X hX b) (hr X hX b) (htau X hX b)
  have hgS := normalized_germ p hp k hs (Spec (.of k)) hs (𝟙 _) A b δ hδ hid
    (r (Spec (.of k)) hs b) (tau (Spec (.of k)) hs b)
    (hr (Spec (.of k)) hs b) (htau (Spec (.of k)) hs b)
  have hmX := normalized_map _ z _ A δ.symm hz
    (frobeniusNormalization_inverse_point δ z) (tau X hX b) hgX
  have hmS := normalized_map _ (𝟙 _) _ A δ.symm hid
    (frobeniusNormalization_inverse_point δ (𝟙 _)) (tau _ hs b) hgS
  refine ⟨δ, hpow, hδ, hz, r _ hs b, r X hX b, tau _ hs b, tau X hX b,
    hr _ hs b, hr X hX b, htau _ hs b, htau X hX b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hgX
  · exact identity_reparam z A δ
  · exact derived_identity_reparam z A δ
  · exact hgS
  · exact hmS
  · exact hmX
  · exact normalized_derived _ (𝟙 _) A δ hid (tau _ hs b) hmS
  · refine ⟨comp, ?_, ?_⟩
    · intro Y Z W f g M V m
      exact hcomp Y Z W f g M V m
    · exact ⟨hnat _ X hs hX z b,
        normalized_derived _ z A δ hz (tau X hX b) hmX⟩


set_option backward.isDefEq.respectTransparency.types false in
/-- The specified absolute-Frobenius trivialization satisfies the normalized stalk formulas.

For each iterate `b`, the field automorphism `δ` is the $p^b$-power map and its induced map on
`Spec k` is the iterate Frobenius; naturality gives the displayed point equation.  The
relative-Frobenius site isomorphisms `rS`, `rX` and their projection formulas, and the unit
equations for `tauS` and `tauX`, fix the specified data of
`absoluteFrobenius_proEtale_trivialization_pullback` uniquely.  The germ clauses evaluate
`tauS ∘ c⁻¹` and `tauX ∘ c⁻¹` on every represented germ, with the equality transports from the
point equation, and identify them with the inverse reparametrization `r_{zδ,δ⁻¹}`.  The
remaining clauses give the same equalities as maps, on bounded complexes in the ordinary derived
category, the pullback-along-`z` reparametrization equation, the unit-normalized composition
comparison and the derived pullback equation along `z`.

Proof (the seven steps of the DAG node):

1. Frobenius is natural on characteristic-$p$ schemes: for every scheme map $a:U\to T$, its maps
on sections satisfy $a^\sharp(f^{p^b})=a^\sharp(f)^{p^b}$, and both Frobenius maps are
identities on underlying spaces. Thus $aF_U^b=F_T^ba$ by [def-weil-absolute-frobenius-scheme].
The field map $x\mapsto x^{p^b}$ on $k$ is injective, since $(x-y)^{p^b}=0$ implies $x=y$, and
surjective, since $t^{p^b}-c$ has a root in the algebraically closed field $k$. Hence
$\delta=F_s^b$ is an automorphism, including $\delta=1$ for $b=0$. In particular
$F_X^bz=z\delta$ and $F_V^bv=v\delta$ for every geometric lift $v:s\to V$.

2. First work with a sheaf $M$ on a characteristic-$p$ scheme $T$. Put $P=(F_T^b)^*$,
$Q=(F_T^b)_*$ and $B(V)=V\times_{T,F_T^b}T$. By [lem-pur-frobenius-trivialization-pullback],
$R_V=(F_V^b,h):V\to B(V)$ is the specified natural isomorphism for each weakly etale
$h:V\to T$. Thus the specified direct-image trivialization is $d_M:QM\to M$, with
$d_M(V)=M(R_V)$. Let $\eta:M\to QPM$ be the unit of the module adjunction
[def-weil-pbc-proetale-operations]. Apply [lem-weil-pbc-conjugate-iso-unit-equation] with
$(L_1,R_1)=(P,Q)$, $(L_2,R_2)=(\mathrm{id},\mathrm{id})$, and right-adjoint comparison $d^{-1}$.
The adjoint trivialization is characterized by $Q(\tau_M)\eta_M=d_M^{-1}$. Evaluated at $V$,
the pullback-unit section $\eta_{M,V}(a)\in PM(B(V))$ is sent by $\tau_M$ to
$M(R_V^{-1})(a)\in M(B(V))$. The coefficient identification preserves constant sections by
[prop-weil-pbc-proetale-constant-ring-map], so these are $A$-linear section maps with no
scalar factor.

3. Take a geometric point $u:s\to T$ and a germ $[V,v,a]\in M_{F_T^bu}$, so $hv=F_T^bu=u\delta$.
By the inverse formula in [lem-trf-proetale-pullback-stalk-coherence], $c_{F_T^b,u,M}^{-1}$
represents this germ by the pullback-unit section of $PM$ on $B(V)$ at the lift $w=(v,u)$.
Step 1 gives $h(v\delta^{-1})=u$ and $F_V^b(v\delta^{-1})=v$, hence
$R_V(v\delta^{-1})=(v,u)=w$. The fibre-product universal property [def-pc-fibre-product] and
invertibility of $R_V$ give $R_V^{-1}w=v\delta^{-1}$. Step 2 therefore sends the germ to
$[B(V),w,M(R_V^{-1})(a)]$. The pointed morphism $R_V^{-1}:(B(V),w)\to(V,v\delta^{-1})$
identifies this with $[V,v\delta^{-1},a]$ by the germ relation in
[def-weil-proetale-geometric-stalk].

4. For any scheme automorphism $\beta$ of $s$, precomposition sends a pointed neighbourhood
$(V,v)$ of $u$ to $(V,v\beta)$ of $u\beta$, leaving site arrows and sections unchanged. A
relation $[V',v',a']=[V,v,M(e)(a')]$ with $ev=v'$ remains a relation because
$e(v\beta)=v'\beta$. Thus [def-weil-proetale-geometric-stalk] defines $r_{u,\beta,M}$ on the
quotient, with inverse $r_{u\beta,\beta^{-1},M}$. The maps preserve sums and
$A$-multiplication, and for a sheaf map $f:M\to M'$ both orders send $[V,v,a]$ to
$[V,v\beta,f_V(a)]$, so $r$ is natural. In Step 3 the resulting map is exactly
$r_{u\delta,\delta^{-1},M}$.

5. Specialize Step 3 to $T=s$, $u=\mathrm{id}_s$ and $M=N$: it gives
$[V,v,a]\mapsto[V,v\delta^{-1},a]$ under $c_{\delta,\mathrm{id}_s,N}$. Specialize it to $T=X$,
$u=z$ and $M=H$; since $F_X^bz=z\delta$, it gives
$(\tau_X^{(b)}{}_H)_z\,c_{F_X^b,z,H}^{-1}=r_{z\delta,\delta^{-1},H}$. These are equalities of
maps, since every germ has a representative in the colimit of
[def-weil-proetale-geometric-stalk]. Step 4 proves naturality of the right side; naturality of
the left side is part of [lem-trf-proetale-pullback-stalk-coherence] and of the specified
natural transformation [lem-pur-frobenius-trivialization-pullback].

6. Apply the pullback naturality statement of [lem-pur-frobenius-trivialization-pullback] to
$z:s\to X$. With its specified composition comparison $C:Lz^*L(F_X^b)^*\to L\delta^*Lz^*$, it
gives $\tau_s^{(b)}{}_{Lz^*H}\circ C_H=Lz^*(\tau_X^{(b)}{}_H)$. Take the stalk at
$\mathrm{id}_s$. The composition equation for $c$ in
[lem-trf-proetale-pullback-stalk-coherence] identifies the two source stalks with
$H_{F_X^bz}=H_{z\delta}$. Its reparametrization equation identifies the target maps from
Steps 3--5 as well. This proves the compatibility through the specified composition
comparisons, not through arbitrary isomorphisms.

7. Apply Steps 2--6 in every degree of a bounded complex. All section maps commute with the
differentials by naturality, so the germ equations are equalities of chain maps. The module
pullbacks are exact and their derived pullbacks are the termwise functors by
[def-weil-pbc-proetale-operations]. The cited Frobenius trivialization is the termwise one by
[lem-pur-frobenius-trivialization-pullback], and [lem-trf-proetale-pullback-stalk-coherence]
supplies the stalk comparisons, composition equalities and reparametrizations after
localization. Parts (2) and (3) of [lem-weil-pbc-localization-universal-property] carry their
naturality and equalities to the localization; no resolution choice changes the formula. For
$b=0$, $R_V$, $\delta$, and both germ reparametrizations are identities, consistent with
$\tau^{(0)}=1$.

Source: Stacks Project, `more-morphisms.tex`, Tag 0F6W
(blueprint: lem-trf-frobenius-stalk-trivialization-normalization).
-/
theorem frobeniusStalkTrivializationNormalization
    (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [IsAlgClosed k]
    (hs : (Spec (.of k)).IsCharacteristic p) (X : Scheme.{u})
    (hX : X.IsCharacteristic p) (z : Spec (.of k) ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    FrobeniusStalkTrivializationNormalized p hp k hs X hX z A := by
  have hf := absoluteFrobenius_proEtale_trivialization_pullback p hp A
  rcases hf with ⟨r, hr, comp, hcomp, tau, htau, hnat, hrest⟩
  exact normalized_from_data p hp k hs X hX z A r hr comp hcomp tau htau hnat
    (fun b ↦ (field_frobenius p hp k hs b).choose)
    (fun b ↦ (field_frobenius p hp k hs b).choose_spec.1)
    (fun b ↦ (field_frobenius p hp k hs b).choose_spec.2)

end AlgebraicGeometry.Scheme
