/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData
import Sheaf.Paper.QuotientRootLineComparison
import Sheaf.Paper.QuotientInverseOrientation
import Sheaf.Paper.QuotientIntrinsicCtf
import Sheaf.Paper.FiniteProCoefficientCounitTransport
import all Sheaf.SecSmoothPurity.ReductionCompatibilities
import all Sheaf.Paper.ExceptionalCoefficientComparison
import all Sheaf.Paper.FiniteSmoothLevelOfOrientation
import all Sheaf.Paper.FiniteCompactSupportDomains

/-! # Two-level finite smooth reduction

Source: main-20261015, sk-prop-sp-orientation and sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-two-level-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem reductionOriginIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) : IsIso (originReductionMap φ T K) := by
  have := intrinsicOriginCounit A T K hK
  have hp := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ T
    ((origin A T).obj K) (actualOriginCtf A T K hK).2
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat B) T
    ((ordinaryScalar φ T).obj ((origin A T).obj K)) hp
  unfold originReductionMap
  rw [Adjunction.homEquiv_unit]
  infer_instance

private theorem reductionOriginInverseIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) : IsIso (originInverse A T K) := by
  have hc := intrinsicOriginCounit A T K hK
  unfold originInverse
  rw [dif_pos hc]
  infer_instance

private theorem reductionCompactSiteIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (hM : _root_.DerivedCategory.TStructure.t.plus M) :
    IsIso (compactSiteMap A f M) ∧ IsIso (compactSiteInverse A f M) := by
  unfold compactSiteMap compactSiteInverse
  rw [dif_pos hM, dif_pos hM]
  constructor <;> infer_instance

private theorem reductionCompactIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    (M : proCategory A X) (hM : IsCtf A X M) :
    IsIso (proCompactCoefficientMap φ f M) := by
  have := intrinsicOriginCounit A X M hM
  have := reductionOriginInverseIso A X M hM
  have hO := actualOriginCtf A X M hM
  have := (reductionCompactSiteIso A f _ hO.1.1.1).1
  have hplus := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X
    ((origin A X).obj M) hO.2
  have hsiteB : IsIso (compactSiteInverse B f
      ((ordinaryScalar φ X).obj ((origin A X).obj M))) :=
    (reductionCompactSiteIso B f _ hplus).2
  have hsiteScalar : IsIso ((ProEtale.pbcComparisonReduction Y φ).hom.app
      ((rightDerivedLowerShriek (ModuleCat A) f).obj ((origin A X).obj M))) := by
    infer_instance
  have := ExceptionalCoefficients.compactSupport_isIso φ
    (HasCompactification.compactification f) ((origin A X).obj M)
  have h₁ : IsIso ((proScalar φ Y).map
      ((proCompact A f).map (originInverse A X M) ≫
        compactSiteMap A f ((origin A X).obj M))) := by infer_instance
  have h₂ : IsIso ((comparison B Y).map
      (ExceptionalCoefficients.compactSupportMap φ
        (HasCompactification.compactification f) ((origin A X).obj M))) := by
    infer_instance
  have h₃ : IsIso ((proCompact B f).map
      ((ProEtale.pbcComparisonReduction X φ).inv.app ((origin A X).obj M) ≫
        (proScalar φ X).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat A) X).counit.app M))) := by
    infer_instance
  unfold proCompactCoefficientMap
  infer_instance

private theorem reductionPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsIso (proPullbackMap φ f K) := by
  have := reductionOriginInverseIso A Y K hK
  have := scalarOriginCounit φ Y K hK
  have := reductionOriginIso φ Y K hK
  unfold proPullbackMap pullbackToOrigin pullbackFromOrigin
  infer_instance

private theorem reductionOriginNaturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) {K L : proCategory A T} (v : K ⟶ L) :
    (ordinaryScalar φ T).map ((origin A T).map v) ≫ originReductionMap φ T L =
      originReductionMap φ T K ≫ (origin B T).map ((proScalar φ T).map v) := by
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat B) T
  unfold originReductionMap
  apply adj.homEquiv_naturality_left_square
  have he := (ProEtale.pbcComparisonReduction T φ).inv.naturality ((origin A T).map v)
  have hc := (ProEtale.derivedComparisonAdjunction (ModuleCat A) T).counit.naturality v
  dsimp only [Functor.comp_map] at he hc
  erw [← Category.assoc, he, Category.assoc, ← Functor.map_comp, hc, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

private theorem reductionCoefficientNaturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    {K L : proCategory A Y} (v : K ⟶ L) :
    (proScalar φ X).map ((exceptional A f).map v) ≫ proCoefficientMap φ f L =
      proCoefficientMap φ f K ≫ (exceptional B f).map ((proScalar φ Y).map v) := by
  have hn := (ProEtale.pbcComparisonReduction X φ).hom.naturality
    ((rightDerivedUpperShriek (ModuleCat A) f).map ((origin A Y).map v))
  have hm := (mateEquiv
    (rightDerivedUpperShriekAdjunction (ModuleCat A) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat B) f)
    (TwoSquare.mk _ _ _ _ (ExceptionalCoefficients.compactSupportIso φ
      (HasCompactification.compactification f)).inv)).naturality ((origin A Y).map v)
  dsimp only [Functor.comp_map] at hn hm
  simp only [← ExceptionalCoefficients.mateMap_eq] at hm
  have hn' : (proScalar φ X).map
      ((comparison A X).map ((rightDerivedUpperShriek (ModuleCat A) f).map
        ((origin A Y).map v))) ≫
        (ProEtale.pbcComparisonReduction X φ).hom.app
          ((rightDerivedUpperShriek (ModuleCat A) f).obj ((origin A Y).obj L)) =
      (ProEtale.pbcComparisonReduction X φ).hom.app
          ((rightDerivedUpperShriek (ModuleCat A) f).obj ((origin A Y).obj K)) ≫
        (comparison B X).map ((ordinaryScalar φ X).map
          ((rightDerivedUpperShriek (ModuleCat A) f).map ((origin A Y).map v))) := hn
  have hm' := congrArg (comparison B X).map hm
  have hr := congrArg (fun t ↦ (comparison B X).map
    ((rightDerivedUpperShriek (ModuleCat B) f).map t))
    (reductionOriginNaturality φ Y v)
  simp only [Functor.map_comp] at hm' hr
  change (comparison B X).map ((ordinaryScalar φ X).map
        ((rightDerivedUpperShriek (ModuleCat A) f).map ((origin A Y).map v))) ≫
      (comparison B X).map (ExceptionalCoefficients.mateMap φ f ((origin A Y).obj L)) =
    (comparison B X).map (ExceptionalCoefficients.mateMap φ f ((origin A Y).obj K)) ≫
      (comparison B X).map ((rightDerivedUpperShriek (ModuleCat B) f).map
        ((ordinaryScalar φ Y).map ((origin A Y).map v))) at hm'
  unfold proCoefficientMap
  change (proScalar φ X).map
    ((comparison A X).map ((rightDerivedUpperShriek (ModuleCat A) f).map
      ((origin A Y).map v))) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn', reassoc_of% hm', hr]
  simp only [exceptional, Functor.comp_map]

/-- Two-level reduction of the specified finite smooth maps.
Source: sk-lem-sp-reduction-exceptional and sk-lem-sp-reduction-compatibilities (3)
(blueprint: lem-pur-finite-smooth-two-level-reduction).
Proof: quotientRootLineComparison gives the generator-normalized root line.
quotientInverseOrientation gives its inverse-orientation square at the coefficient
unit. Apply the proved ordinaryGammaCoefficient tensor calculation to this square.
The supplied ordinary purity isomorphisms on both levels make the resulting
exceptional mate an isomorphism; its defining adjunction gives the counit equation.
quotientIntrinsicCtf transports constructibility and finite Tor amplitude through
the canonical scalar realization on every scheme. On the Noetherian schemes X,Y,
actualOriginCtf and the comparison-adjunction unit identify the origin comparisons
as isomorphisms. The proper/open compact comparison is invertible at the resulting
bounded-below ordinary origins, and the pullback comparison is a composite of
these isomorphisms. Naturality follows from the two adjunction counits and the
ordinary compact-support mate. finiteProCoefficientCounitTransport gives the
counit equation, with its bounded-below hypotheses supplied by ordinary smooth
exceptional-domain preservation at the two levels. Finally proGammaCoefficient
transports the ordinary purity square. Its other three edges are isomorphisms
by the supplied pro purity properties, so proLambda is an isomorphism. Assemble
these ten assertions with the original canonical maps into ReductionData.
This uses no triple-level quotient coherence. -/
theorem finiteSmoothTwoLevelReduction
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r)
    (a : Level ell r f d) (b : Level ell m f d) :
    Nonempty (ReductionData (FiniteReduction.quotient ell hmr) f d a b) := by
  classical
  let φ := FiniteReduction.quotient.{u} ell hmr
  let A := coefficient.{u} ell r
  let B := coefficient.{u} ell m
  have hYunit : IsUnit (ell : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using hY y
  have hXunit : IsUnit (ell : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hYunit.map f.appTop.hom
  obtain ⟨e⟩ := quotientRootLineComparison ell X hXunit r m hm hmr
  have ho := quotientInverseOrientation ell f d hY r m hm hmr a b e
  have hp (K : DerivedCategoryModule A Y) :=
    ordinaryGammaCoefficient φ f (ell ^ r) (ell ^ m)
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) d e a.alpha b.alpha ho K
  have hred := quotientIntrinsicCtf ell r m hm hmr
  have hann (n : ℕ) : ∃ k : ℕ, ∀ x : coefficient.{u} ell n, (ell ^ k) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (coefficient ell n), CharP.cast_eq_zero, zero_smul]
  have hscalar (K : DerivedCategoryModule A Y)
      (hK : DerivedCategory.boundedConstructibleFiniteTor A Y K) :
      DerivedCategory.boundedConstructibleFiniteTor B Y ((ordinaryScalar φ Y).obj K) := by
    exact (ProEtale.domain_scalar ell A B (hann r) (hann m) φ Y K hK).2.1
  have hmate (K : DerivedCategoryModule A Y)
      (hK : DerivedCategory.boundedConstructibleFiniteTor A Y K) :
      IsIso (ExceptionalCoefficients.mateMap φ f K) := by
    have := a.ordinary_isIso K hK
    have := b.ordinary_isIso ((ordinaryScalar φ Y).obj K) (hscalar K hK)
    have hi : IsIso ((ordinaryScalar φ X).map (gamma A f _ a.alpha K) ≫
        ExceptionalCoefficients.mateMap φ f K) := by
      rw [hp K]
      infer_instance
    exact IsIso.of_isIso_comp_left ((ordinaryScalar φ X).map (gamma A f _ a.alpha K)) _
  refine ⟨{
    twist := e
    ordinary_compact := fun Q hQ ↦
      ExceptionalCoefficients.compactSupportMap_isIso ell r m d hmr hm hY
        (HasCompactification.compactification f) Q hQ
    ordinary_counit := ?_
    ordinary_purity := fun K _ ↦ hp K
    reduction_ctf := hred
    pro_compact := ?_
    pro_counit := ?_
    pro_natural := ?_
    pro_pullback := ?_
    pro_purity := ?_ }⟩
  · intro K hK
    refine ⟨hmate K hK, ?_⟩
    unfold ExceptionalCoefficients.mateMap
    exact ((rightDerivedUpperShriekAdjunction (ModuleCat B) f).homEquiv _ _).symm_apply_apply _
  · exact fun Q hQ ↦ reductionCompactIso φ f Q hQ
  · intro K hK
    have hO := a.origin_ctf K hK
    have := hmate ((origin A Y).obj K) hO
    have := reductionOriginIso φ Y K hK
    have hi : IsIso (proCoefficientMap φ f K) := by
      unfold proCoefficientMap
      infer_instance
    refine ⟨hi, ?_⟩
    let : HasInvertibleExponent A Y :=
      ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r,
        CharP.cast_eq_zero _ _, by simpa only [Nat.cast_pow] using hYunit.pow r⟩
    let : HasInvertibleExponent B Y :=
      ⟨ell ^ m, pow_pos (Fact.out : ell.Prime).pos m,
        CharP.cast_eq_zero _ _, by simpa only [Nat.cast_pow] using hYunit.pow m⟩
    exact finiteProCoefficientCounitTransport φ f K hK
      (ordinaryExceptionalCtf A f d _ hO)
      (ordinaryExceptionalCtf B f d _
        (b.origin_ctf _ (hred Y K hK))).1.1.1
  · intro K L _ _ v
    exact reductionCoefficientNaturality φ f v
  · exact fun K hK ↦ reductionPullbackIso φ f K hK
  · intro K hK
    have heq := proGammaCoefficient φ f (ell ^ r) (ell ^ m)
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) d e a.alpha b.alpha hp K hK
    have := a.pro_purity K hK |>.2.2
    have := b.pro_purity ((proScalar φ Y).obj K) (hred Y K hK) |>.2.2
    have := hmate ((origin A Y).obj K) (a.origin_ctf K hK)
    have := reductionOriginIso φ Y K hK
    have hi : IsIso (proCoefficientMap φ f K) := by
      unfold proCoefficientMap
      infer_instance
    have hj : IsIso (proLambda f d e K ≫
        proGamma B f _ b.alpha ((proScalar φ Y).obj K)) := by
      rw [← heq]
      infer_instance
    exact ⟨IsIso.of_isIso_comp_right (proLambda f d e K)
      (proGamma B f _ b.alpha ((proScalar φ Y).obj K)), heq⟩

end AlgebraicGeometry.Etale.FiniteSmoothPurity
