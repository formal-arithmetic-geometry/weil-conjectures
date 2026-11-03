/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Compact.CompactSupportTermHomFinite
import WeilConjectures.Mathlib.CategoryTheory.CofilteredSystem

/-! # Canonical constructible exceptional composition

Source: blueprint main-20261015, Verdier exchange, proof Step 1
(blueprint: def-sf-constructible-exceptional-compositor-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- Change from the finite tensor-pullback presentation to the published fixed-scalar
one, preserving the ordinary units. The coefficient-identification transport has
identity hom. Source: blueprint finite exceptional adjunction
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
def constructibleFinitePullIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModulePullback f
        ((PurCompactSupport.finite l E n n.pos).ring Y)
        ((PurCompactSupport.finite l E n n.pos).ring X)
        ((PurCompactSupport.finite l E n n.pos).pull f) ≅
      @sfIntrinsicPullback (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n n.pos) X Y f :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n n.pos
  eqToIso (congrArg
      (fun e ↦ proEtaleRingModulePullback f
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)) e)
      (Iso.ext (by rfl) :
        @sfConstantCoefficientIso X Y f (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n n.pos) =
        proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E n))) ≪≫
    @openSquarePullbackModel (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n n.pos) X Y f

/-- The finite proper/open presentations are compared by their unit-normalized
adjunctions, then by termwise and K-injective descent.
Source: blueprint finite exceptional adjunction, ordinary open-extension comparison
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
def constructibleFiniteImageIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    PurCompactSupport.image (PurCompactSupport.finite l E n n.pos) c ≅
      @sfIntrinsicCompactSupport X Y f c (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n n.pos) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n n.pos
  letI : IsOpenImmersion c.i := c.isOpenImmersion
  letI : (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)).Additive :=
    sfIntrinsicExtensionByZero_additive c.i (Padic.coefficientExtensionRing l E n)
  letI : Limits.PreservesFiniteLimits
      (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)) :=
    sfIntrinsicExtensionByZero_preservesFiniteLimits c.i (Padic.coefficientExtensionRing l E n)
  letI : Limits.PreservesFiniteColimits
      (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)) :=
    sfIntrinsicExtensionByZero_preservesFiniteColimits c.i (Padic.coefficientExtensionRing l E n)
  letI : (proEtaleConstantModuleDirectImage c.g
      (Padic.coefficientExtensionRing l E n)).Additive :=
    proEtaleConstantModuleDirectImage_additive c.g (Padic.coefficientExtensionRing l E n)
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (((PurCompactSupport.openAdjunction
          (PurCompactSupport.finite l E n n.pos) c.i).ofNatIsoRight
            (constructibleFinitePullIso l E n c.i)).leftAdjointUniq
          (@sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n n.pos) X c.Z c.i
            c.isOpenImmersion))) _ ≪≫
  Functor.isoWhiskerLeft _
    (Functor.rightDerivedFunctorNatIso
      (((proEtaleRingModuleAdjunction c.g
          (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
          (proEtaleConstantRing c.Z (Padic.coefficientExtensionRing l E n))
          (@sfConstantCoefficientIso c.Z Y c.g (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n n.pos))).ofNatIsoLeft
              (constructibleFinitePullIso l E n c.g)).rightAdjointUniq
        (@sfIntrinsicConstantModuleAdjunction c.Z Y c.g
          (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n n.pos))))

private theorem derivedLimit_hom_ext_of_finite
    {T : Type*} [Category T] [CategoryTheory.Limits.HasZeroObject T] [HasShift T ℤ]
    [Preadditive T] [∀ m : ℤ, (shiftFunctor T m).Additive] [Pretriangulated T]
    (V : ℕ → T) [CategoryTheory.Limits.HasProduct V]
    (v : ∀ n, V (n + 1) ⟶ V n) (Q : T)
    (q : Q ⟶ CategoryTheory.Limits.piObj V)
    (d : CategoryTheory.Limits.piObj V ⟶ Q⟦(1 : ℤ)⟧)
    (hQ : IsDerivedLimitTriangle v Q q d) (P : T)
    (hfinite : ∀ n, Finite (P⟦(1 : ℤ)⟧ ⟶ V n))
    (a b : P ⟶ Q)
    (hab : ∀ n, a ≫ q ≫ CategoryTheory.Limits.Pi.π V n =
      b ≫ q ≫ CategoryTheory.Limits.Pi.π V n) : a = b := by
  let S := Pretriangulated.Triangle.mk q (towerTransitionEndomorphism v) d
  have hS : S ∈ Pretriangulated.distinguishedTriangles := hQ
  have hvd : towerTransitionEndomorphism v ≫ d = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₂₃ S hS
  have hq : (a - b) ≫ q = 0 := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro n
    simp only [Preadditive.sub_comp, Category.assoc, CategoryTheory.Limits.zero_comp]
    exact sub_eq_zero.mpr (hab n)
  obtain ⟨u, hu⟩ := Pretriangulated.Triangle.coyoneda_exact₁ S hS
    ((a - b)⟦(1 : ℤ)⟧') (by
      simp only [S, Pretriangulated.Triangle.mk_mor₁, ← Functor.map_comp,
        hq, Functor.map_zero])
  dsimp only [S, Pretriangulated.Triangle.mk] at u hu
  let (n : ℕ) : Finite (P⟦(1 : ℤ)⟧ ⟶ V n) := hfinite n
  obtain ⟨w, hw⟩ := AddCommGroup.exists_sub_map_succ_eq_of_finite
    (G := fun n ↦ P⟦(1 : ℤ)⟧ ⟶ V n)
    (fun n ↦ Preadditive.rightComp _ (v n))
    (fun n ↦ u ≫ CategoryTheory.Limits.Pi.π V n)
  have huw : u = CategoryTheory.Limits.Pi.lift w ≫ towerTransitionEndomorphism v := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro n
    simpa [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Category.assoc, Preadditive.rightComp] using (hw n).symm
  apply sub_eq_zero.mp
  apply (shiftFunctor T (1 : ℤ)).map_eq_zero_iff.mp
  rw [hu, huw, Category.assoc, hvd, CategoryTheory.Limits.comp_zero]

private theorem normalizedProjection_functor_ext
    {A C T : Type*} [Category A] [Category C] [Category T]
    (i : C ⥤ T) [i.Faithful] (F G : A ⥤ C) (V : A → C)
    (L : ℕ → A ⥤ T) (p : ∀ K n, i.obj (V K) ⟶ (L n).obj K)
    (hF : ∀ K, F.obj K = V K) (hG : ∀ K, G.obj K = V K)
    (qF : ∀ n, F ⋙ i ⟶ L n) (qG : ∀ n, G ⋙ i ⟶ L n)
    (hqF : ∀ K n, HEq ((qF n).app K) (p K n))
    (hqG : ∀ K n, HEq ((qG n).app K) (p K n))
    (hp : ∀ K K' (a b : i.obj (V K) ⟶ i.obj (V K')),
      (∀ n, a ≫ p K' n = b ≫ p K' n) → a = b) : F = G := by
  have hnorm {W W' Z : T} (e : W = W') (a : W ⟶ Z) (b : W' ⟶ Z)
      (h : HEq a b) : a = eqToHom e ≫ b := by
    subst W'
    simpa using eq_of_heq h
  have hmap {W W' : C} (e : W = W') :
      i.map (eqToHom e) = eqToHom (congrArg i.obj e) := by
    subst W'
    exact i.map_id _
  have hqF' (K : A) (n : ℕ) :
      (qF n).app K = i.map (eqToHom (hF K)) ≫ p K n := by
    simpa only [hmap] using hnorm (congrArg i.obj (hF K)) _ _ (hqF K n)
  have hqG' (K : A) (n : ℕ) :
      (qG n).app K = i.map (eqToHom (hG K)) ≫ p K n := by
    simpa only [hmap] using hnorm (congrArg i.obj (hG K)) _ _ (hqG K n)
  let F' := F.copyObj V (fun K ↦ eqToIso (hF K))
  let G' := G.copyObj V (fun K ↦ eqToIso (hG K))
  have hcopy (J : A ⥤ C) (hJ : ∀ K, J.obj K = V K) :
      J.copyObj V (fun K ↦ eqToIso (hJ K)) = J := by
    apply Functor.hext (fun K ↦ (hJ K).symm)
    intro K K' f
    dsimp only [Functor.copyObj, eqToIso.hom, eqToIso.inv]
    exact (eqToHom_comp_heq _ (hJ K).symm).trans (comp_eqToHom_heq _ (hJ K'))
  have hFG : F' = G' := by
    refine CategoryTheory.Functor.ext (F := F') (G := G') (fun _ ↦ rfl) ?_
    intro K K' f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply i.map_injective
    apply hp K K'
    intro n
    have hf := (qF n).naturality f
    have hg := (qG n).naturality f
    rw [hqF', hqF'] at hf
    rw [hqG', hqG'] at hg
    simp only [Functor.comp_map] at hf hg
    have hf' := congrArg (fun z ↦ i.map (eqToHom (hF K).symm) ≫ z) hf
    have hg' := congrArg (fun z ↦ i.map (eqToHom (hG K).symm) ≫ z) hg
    simp only [← Category.assoc, ← Functor.map_comp, eqToHom_trans,
      eqToHom_refl] at hf' hg'
    rw [i.map_id, Category.id_comp] at hf' hg'
    simp only [Category.assoc] at hf' hg'
    apply Eq.trans (b := p K n ≫ (L n).map f)
    · simpa only [F', Functor.copyObj, eqToIso.hom, eqToIso.inv] using hf'
    · symm
      simpa only [G', Functor.copyObj, eqToIso.hom, eqToIso.inv] using hg'
  exact (hcopy F hF).symm.trans (hFG.trans (hcopy G hG))

private theorem projections_from_realization
    {A C T U : Type*} [Category A] [Category C] [Category T] [Category U]
    {i : A ⥤ C} {F : A ⥤ U} {tower : C ⥤ T} {limit : T ⥤ U}
    {eval : ℕ → T ⥤ U} {L : ℕ → C ⥤ U}
    {e : ∀ n, tower ⋙ eval n ≅ L n}
    {π : ∀ n, limit ⟶ eval n}
    {V : A → U} {p : ∀ K n, V K ⟶ (L n).obj (i.obj K)}
    (γ : F ≅ i ⋙ tower ⋙ limit)
    (hγ : ∀ K n, HEq (γ.hom.app K ≫ (π n).app (tower.obj (i.obj K)) ≫
        (e n).hom.app (i.obj K)) (p K n)) :
    ∃ q : ∀ n, F ⟶ i ⋙ L n, ∀ K n, HEq ((q n).app K) (p K n) := by
  refine ⟨fun n ↦ γ.hom ≫ Functor.whiskerLeft i
    (Functor.whiskerLeft tower (π n) ≫ (e n).hom), ?_⟩
  intro K n
  exact hγ K n

attribute [local irreducible] sfCompactSupportTransition
  sfIntegralCompactSupportValue in
set_option backward.isDefEq.respectTransparency true in
end WeilConjectures

namespace WeilConjectures.ConstructibleExceptionalCompositor
open ConstructibleExceptionalCoefficients
variable {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section OneArrow
variable {X Y : SixFunctorSpace D} (f : X ⟶ Y)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))

end OneArrow

section TwoArrows
variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))
  (Q : System.{u, u} B.l B.Qbar D B.different (f := g.hom.left))
  (R : System.{u, u} B.l B.Qbar D B.different (f := (f ≫ g).hom.left))

end TwoArrows

end WeilConjectures.ConstructibleExceptionalCompositor
