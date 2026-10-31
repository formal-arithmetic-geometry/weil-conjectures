/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteGeneralRingData
import WeilConjectures.SecSmoothPurity.FiniteGeneralRingIntegrationExponent

/-! # Kummer comparison of normalized smooth orientations
Source: general-ring smooth purity, proof (1)-(3).
(blueprint: lem-sp-general-ring-exponent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem bundle_exponent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (q : S.rootsOfUnitySheaf M ⟶ S.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN S q b) :
    (finiteGeneralRingLevelPower A M N hM hN S b d).hom ≫
        Etale.FiniteRingSectionDeformation.bundleSectionAdjoint N hNpos A hN S hS' d F =
      Etale.FiniteRingSectionDeformation.bundleSectionAdjoint M hMpos A hM S hS d F := by
  let P := Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)
  let U := Etale.ordinaryFinitePullback A (VectorBundleZeroSection.zero S d F)
  let e := finiteGeneralRingLevelPower A M N hM hN S b d
  have htrace := finiteGeneralRingIntegrationExponent A M N hMpos hNpos hdiv
    hM hN S hS hS' d F q b hb
  have hadj : P.map e.hom ≫
      Etale.FiniteRingSectionDeformation.bundleAdjoint N hNpos A hN S hS' d F =
    Etale.FiniteRingSectionDeformation.bundleAdjoint M hMpos A hM S hS d F := by
    unfold Etale.FiniteRingSectionDeformation.bundleAdjoint
    exact ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv_naturality_left
      (P.map e.hom) (Etale.vectorBundleIntegration N hNpos A hN S hS' d F)).symm.trans
      (congrArg ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ _) htrace)
  let c := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d F) (VectorBundleZeroSection.π S d F)
    (VectorBundleZeroSection.zero_spec S d F).1
  have hc := c.inv.naturality e.hom
  change e.hom ≫ c.inv.app _ = c.inv.app _ ≫ U.map (P.map e.hom) at hc
  change e.hom ≫ (c.inv.app _ ≫ U.map _) = c.inv.app _ ≫ U.map _
  rw [← Category.assoc, hc, Category.assoc, ← U.map_comp, hadj]
  rfl

/-- The direct normalized orientation agrees through the common maximum exponent.
This statement compares orientations, before applying any tensor purity maps.

Source: general-ring smooth purity, proof (3), exponent-independence paragraph
(blueprint: lem-sp-general-ring-exponent).

Proof: ell^max(n,n') is a multiple of both annihilating powers, hence kills A.
The two root power maps are the unique maps into the corresponding kernels induced
by multiplication by the quotients on G_m. Kummer exactness and the free-line
scalar/root generators give the two normalized sheaf isomorphisms b and b'.
Run the direct diagonal construction at n'. Its geometry is the same actual smooth
diagonal, so it gives alpha' with the asserted OrientationNormalized equation.
The Kummer diagram has quotient power on the left and middle G_m and identity on
the right. It therefore preserves the boundary class of O(1), hence the normalized
projective-line trace. Iterating preserves the ordered affine counits, with the
identity in dimension zero. Unique frame gluing identifies bundle integration.
The Rees family comparison is fixed by its t=1 value; the uniqueness of that
normalization identifies the two specializations. The diagonal comparison is
independent of coefficient exponent. Substitution in the two normalization
equations therefore gives the displayed equality of orientation maps to the
common maximum line. This holds for the zero ring and empty schemes as well,
and never divides by a nonunit of A. -/
theorem finiteGeneralRingExponent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n) (hA : ((ell ^ n : ℕ) : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (d : ℕ) (f : X ⟶ Y) [SmoothOfRelativeDimension d f]
    [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hUnits : ∀ m : ℕ, 1 ≤ m → IsUnit ((ell ^ m : ℕ) : Γ(X, ⊤)))
    (alpha : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d)
    (halpha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f d geometry (hUnits n hn) alpha) :
  ∀ (n' : ℕ) (hn' : 1 ≤ n') (hA' : ((ell ^ n' : ℕ) : A) = 0),
    ∃ hM : ((ell ^ max n n' : ℕ) : A) = 0,
    ∃ (q : X.rootsOfUnitySheaf (ell ^ max n n') ⟶ X.rootsOfUnitySheaf (ell ^ n))
      (q' : X.rootsOfUnitySheaf (ell ^ max n n') ⟶ X.rootsOfUnitySheaf (ell ^ n'))
      (b : Scheme.finiteEtaleTateLine X (ell ^ max n n') A hM ≅
        Scheme.finiteEtaleTateLine X (ell ^ n) A hA)
      (b' : Scheme.finiteEtaleTateLine X (ell ^ max n n') A hM ≅
        Scheme.finiteEtaleTateLine X (ell ^ n') A hA')
      (alpha' : Etale.dualizingComplex A f ≅
        Etale.FiniteSmoothPurity.line A (ell ^ n') hA' X d),
      FiniteGeneralRingKummerComparison A _ _ hM hA X q b ∧
      FiniteGeneralRingKummerComparison A _ _ hM hA' X q' b' ∧
      Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n')
        (pow_pos (Fact.out : ell.Prime).pos n') hA' f d geometry (hUnits n' hn') alpha' ∧
      alpha.hom ≫ (finiteGeneralRingLevelPower A _ _ hM hA X b d).inv =
        alpha'.hom ≫ (finiteGeneralRingLevelPower A _ _ hM hA' X b' d).inv
 := by
  intro n' hn' hA'
  have hdiv : ell ^ n ∣ ell ^ max n n' := pow_dvd_pow ell (le_max_left n n')
  have hdiv' : ell ^ n' ∣ ell ^ max n n' := pow_dvd_pow ell (le_max_right n n')
  have hM : ((ell ^ max n n' : ℕ) : A) = 0 :=
    (CharP.cast_eq_zero_iff A (ringChar A) _).mpr
      (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) _).mp hA) hdiv)
  have hpos (m : ℕ) : 0 < ell ^ m := pow_pos (Fact.out : ell.Prime).pos m
  have hmax : 1 ≤ max n n' := hn.trans (le_max_left n n')
  obtain ⟨_, _, _, laws⟩ := Scheme.etaleFiniteTwistPullback A (ell ^ n) (hpos n) hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hexp⟩ := laws
  obtain ⟨q, t, hq, ht, _⟩ :=
    hexp (ell ^ max n n') (hpos _) hdiv X (hUnits _ hmax)
  obtain ⟨_, _, _, laws'⟩ := Scheme.etaleFiniteTwistPullback A (ell ^ n') (hpos n') hA'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hexp'⟩ := laws'
  obtain ⟨q', t', hq', ht', _⟩ :=
    hexp' (ell ^ max n n') (hpos _) hdiv' X (hUnits _ hmax)
  let b : Scheme.finiteEtaleTateLine X (ell ^ max n n') A hM ≅
      Scheme.finiteEtaleTateLine X (ell ^ n) A hA := t 1
  let b' : Scheme.finiteEtaleTateLine X (ell ^ max n n') A hM ≅
      Scheme.finiteEtaleTateLine X (ell ^ n') A hA' := t' 1
  have hb : FiniteGeneralRingKummerComparison A _ _ hM hA X q b := ⟨hq, ht⟩
  have hb' : FiniteGeneralRingKummerComparison A _ _ hM hA' X q' b' := ⟨hq', ht'⟩
  let e := finiteGeneralRingLevelPower A _ _ hM hA X b d
  let e' := finiteGeneralRingLevelPower A _ _ hM hA' X b' d
  let alpha' := alpha ≪≫ e.symm ≪≫ e'
  refine ⟨hM, q, q', b, b', alpha', hb, hb', ?_, ?_⟩
  · let := geometry
    obtain ⟨κ, hκ, sq, heq⟩ := halpha
    refine ⟨κ, hκ, sq, ?_⟩
    have he := bundle_exponent A _ _ (hpos _) (hpos n) hdiv
      hM hA X (hUnits _ hmax) (hUnits n hn) d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) q b hb
    have he' := bundle_exponent A _ _ (hpos _) (hpos n') hdiv'
      hM hA' X (hUnits _ hmax) (hUnits n' hn') d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) q' b' hb'
    change _ = (alpha.hom ≫ e.inv ≫ e'.hom) ≫ _ ≫ _
    simp only [Category.assoc]
    rw [reassoc_of% he', ← reassoc_of% he, Iso.inv_hom_id_assoc]
    exact heq
  · change alpha.hom ≫ e.inv = (alpha.hom ≫ e.inv ≫ e'.hom) ≫ e'.inv
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.ProEtale
