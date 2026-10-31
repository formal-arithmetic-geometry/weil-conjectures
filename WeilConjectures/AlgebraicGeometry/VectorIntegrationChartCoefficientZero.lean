/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegrationCharts

import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-! # Rank-zero chart coefficient normalization

Source: blueprint vector-bundle purity, paragraph 2, prescribed counit on a frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  vectorIntegrationChart upperStar Functor.leftDerivedFunctor
  Functor.mapDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  leftDerivedUpperStarComp leftDerivedUpperStarId

set_option allowUnsafeReducibility true in
attribute [local reducible] affineTraceTower affineTraceProjection affineLinearBaseCoefficient
attribute [local implicit_reducible] Scheme.Modules vectorIntegrationCoefficient
  vectorIntegrationChartCoefficient vectorIntegrationBaseCoefficientPullback
  affineLinearCoefficientDescent

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private lemma named_compositor
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (v : Y ⟶ Z) (k : X ⟶ Z) (e : k = r ≫ v) :
    eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v k e := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]

private lemma square_compositor
    (A : Type (u + 1)) [CommRing A] {X X' Y Y' : Scheme.{u}}
    (q : X' ⟶ X) (r : X' ⟶ Y') (p : X ⟶ Y) (v : Y' ⟶ Y)
    (hs : q ≫ p = r ≫ v) (k : X' ⟶ Y) (hk : k = q ≫ p) :
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p k hk ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).symm ≪≫
      eqToIso (congrArg (ordinaryFinitePullback A) hs) ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v k (hk.trans hs) := by
  subst k
  simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  exact named_compositor A r v (q ≫ p) hs

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

private lemma normalize_identity_coefficient
    {C : Type*} [Category* C] {M L P Q R : C}
    (G : C ⥤ C) (η : G ≅ 𝟭 C) (b : M ≅ L)
    (a : M ≅ P) (c : P ≅ Q) (d : Q ≅ R) (e : R ≅ G.obj M)
    (z : M ≅ G.obj M) (h : a ≪≫ c ≪≫ d ≪≫ e = z)
    (hz : z.hom ≫ η.hom.app M = 𝟙 M) :
    a.hom ≫ (c ≪≫ d ≪≫ e ≪≫ G.mapIso b ≪≫ η.app L).hom = b.hom := by
  have hh := congrArg Iso.hom h
  simp only [Iso.trans_hom, ← Category.assoc] at hh
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [η.hom.naturality]
  simp only [Functor.id_map, ← Category.assoc]
  rw [hh, hz, Category.id_comp]

private lemma normalize_natural_coefficient
    {C D : Type*} [Category* C] [Category* D]
    (H P Q R : C ⥤ D) (G : D ⥤ D) (η η' : G ≅ 𝟭 D) (hη : η = η')
    (K : C) (L : D) (b : H.obj K ≅ L)
    (a : H ≅ P) (c : P ≅ Q) (d : Q ≅ R) (e : R ≅ H ⋙ G)
    (z : H ≅ H ⋙ G) (h : a ≪≫ c ≪≫ d ≪≫ e = z)
    (hz : z.hom.app K ≫ η'.hom.app (H.obj K) = 𝟙 (H.obj K)) :
    a.hom.app K ≫
      (c.app K ≪≫ d.app K ≪≫ e.app K ≪≫ G.mapIso b ≪≫ η.app L).hom = b.hom := by
  subst η'
  apply normalize_identity_coefficient G η b (a.app K) (c.app K)
    (d.app K) (e.app K) (z.app K)
  · simpa only [NatIso.trans_app] using congrArg (fun i ↦ i.app K) h
  · exact hz

private lemma identity_square_coefficient
    (A : Type (u + 1)) [CommRing A] {T X S : Scheme.{u}}
    (q : T ⟶ X) (p : X ⟶ S) (f : T ⟶ S) (hc : q ≫ p = f)
    (K : DerivedCategoryModule A S) (L : DerivedCategoryModule A T)
    (b : (ordinaryFinitePullback A f).obj K ≅ L) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p f hc.symm).hom.app K ≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).symm.app K ≪≫
        (eqToIso (congrArg (ordinaryFinitePullback A)
          (hc.trans (Category.id_comp f).symm))).app K ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 T) f).app K ≪≫
        (ordinaryFinitePullback A (𝟙 T)).mapIso b ≪≫
        (affineLinearPullbackId A T).app L).hom = b.hom := by
  exact normalize_natural_coefficient
    (ordinaryFinitePullback A f)
    (ordinaryFinitePullback A p ⋙ ordinaryFinitePullback A q)
    (ordinaryFinitePullback A (q ≫ p))
    (ordinaryFinitePullback A (𝟙 T ≫ f))
    (ordinaryFinitePullback A (𝟙 T))
    (affineLinearPullbackId A T) (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T)
    (pullback_id_eq A T) K L b
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p f hc.symm)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).symm
    (eqToIso (congrArg (ordinaryFinitePullback A) (hc.trans (Category.id_comp f).symm)))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 T) f)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 T) f f (Category.id_comp f).symm)
    (square_compositor A q (𝟙 T) p f (hc.trans (Category.id_comp f).symm) f hc.symm)
    (leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) f K)

/-- The rank-zero chart coefficient becomes the constant-unit pullback map after the
chart/projection pullback compositor.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, the prescribed local affine counit.
(blueprint: lem-pur-vector-integration-chart-coefficient-zero).

Proof: expand the zero cases of vectorIntegrationBaseCoefficientPullback and
affineLinearCoefficientDescent. The first is ordinaryFiniteUnitPullback; the second
is the inverse of affineLinearPullbackId at the unit. Write a for the chart and p for
the bundle projection. The chart square gives a≫p = id≫V.ι. The equality transport
between the two pullback compositors therefore identifies their composite with the
inverse compositor for a≫p=V.ι followed by the compositor for id≫V.ι=V.ι.
Cancel the first against the displayed leading compositor. Naturality moves the
unit pullback through the identity-pullback comparison. The latter is the canonical
leftDerivedUpperStarId (expand the definitions of their exact/derived comparisons).
The left unit law for leftDerivedUpperStarComp then cancels the remaining compositor
and identity comparison. The map left is exactly ordinaryFiniteUnitPullback.
No nonempty-open or nonzero-ring assumption is used. -/
theorem vectorIntegration_chartCoefficient_zero
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank 0]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S 0 F V)
    (hc : vectorIntegrationChart S 0 F V e ≫ VectorBundleZeroSection.π S 0 F = V.ι) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (vectorIntegrationChart S 0 F V e) (VectorBundleZeroSection.π S 0 F)
        V.ι hc.symm).hom.app (ordinaryFiniteUnit A S) ≫
      (vectorIntegrationChartCoefficient A N hA t S hS 0 F V e).hom =
        (ordinaryFiniteUnitPullback A V.ι).hom := by
  exact identity_square_coefficient A (vectorIntegrationChart S 0 F V e)
    (VectorBundleZeroSection.π S 0 F) V.ι hc (ordinaryFiniteUnit A S)
    (ordinaryFiniteUnit A V.toScheme) (ordinaryFiniteUnitPullback A V.ι)

end AlgebraicGeometry.Etale
