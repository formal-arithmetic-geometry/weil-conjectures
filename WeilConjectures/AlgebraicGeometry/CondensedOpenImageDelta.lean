/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RightDerivedSingleH0
public import WeilConjectures.AlgebraicGeometry.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageBasic
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageConstructibility
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageExactness
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageNaturality
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageUnderivedCounit
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageFrobeniusSquare
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageWeil

/-! # Connecting sequence and open restriction for condensed direct image

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-exact,
p-dl-a1-exact.proof.md, Steps 1--2; Stacks Project, Tag 09BN
(blueprint: lem-dl-a1-condensed-open-image-delta).

The boundary is the homology boundary of the actual image of the geometric
short-exact-sequence triangle. All Weil maps use the canonical pullback-composition
comparison and its adjunction mate. No triangulated structure on fixed pairs is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Connecting sequence and restriction for the ordinary condensed Qbar_l module
pushforward of a dense quasi-compact open in a separated smooth finite-type curve.

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-exact,
p-dl-a1-exact.proof.md, Steps 1--2; Stacks Project, Tag 09BN
(blueprint: lem-dl-a1-condensed-open-image-delta).

Proof:
1. The sheaf tensor category and its module categories are Grothendieck abelian by
sk-def-sfb-sheaf-tensor, lem-sfb-proetale-sheaves-grothendieck and
lem-sfb-modobj-grothendieck. Enough injectives and K-injectives follow from
lem-sp-grothendieck-enough-injectives and lem-sfb-grothendieck-k-injective.
The recorded module operations and exact pullback give the actual derived adjunction.
2. An ordinary nonnegative injective resolution computes the derived image of M[0].
Apply lem-weil-pbc-derived-functor-negative-vanishing and
lem-sp-derived-functor-single-identification. The canonical H0 comparison is normalized
by lem-kun-right-derived-single-h0. Bounded constructibility follows from
sk-def-sfb-dc-restricted-functors.
3. By sk-lem-coefficient-heart the sequence is exact in the ambient module category.
Apply lem-sf-derived-ses-triangle, lem-pc-right-derived-functor-triangulated and
lem-sf-derived-homology-long-exact. Negative vanishing and the canonical H0 comparisons
give the stated exact initial segment in the constructible heart.
4. The boundary is natural: lem-sc-p1-right-derived-triangle-connecting identifies it
with the horseshoe boundary and lem-weil-pbc-horseshoe-delta-functor gives naturality.
5. Transport internal modules to section-ring modules by
lem-sfb-internal-module-operations-transport. Apply
lem-sfb-proetale-open-restriction-counit with f=h=j. Monicity identifies U times_C U
with U, so the actual underived counit is an isomorphism on every module.
6. At a K-injective representative I the actual derived counit is the localization of
that degreewise counit, by lem-sc-derived-adjunction-from-underived and
lem-weil-pbc-exact-functor-derived-factorization. Hence it is invertible. Restrict to
bounded constructible objects using sk-def-sfb-dc-restricted-functors.
7. Exact restriction commutes with homology by lem-sp-exact-functor-preserves-homology.
The counit identifies the restricted derived object with M[0], proving positive vanishing.
8. The two geometric Frobenius automorphisms commute with the base-changed open map.
The given three Weil isomorphisms give an isomorphism of the underlying single triangles
by lem-weil-pbc-exact-functor-ses-triangle-image. Apply Rj_* and the canonical exchange
of lem-fix-weil-operations. By lem-sfb-ambient-qcqs-exchange-canonical-shifts it is a
morphism of image triangles; lem-weil-pbc-derived-cohomology-ladder gives the boundary
square. Exact pullback commutes with homology. The H0 augmentation normalization
identifies the degree-zero operation with ordinary direct image. Every displayed map
is therefore Weil equivariant, without a triangulated structure on the strict pairs.

The Lean proof assembles these steps from their component theorems:
Steps 2 and 7 are `condensedOpenImage_basic` and `condensedOpenImage_constructibility`,
Steps 5--6 `condensedOpenImage_underivedCounit`, Step 3 `condensedOpenImage_exactness`,
Step 4 `condensedOpenImage_naturality`, and Step 8 `condensedOpenImage_frobeniusSquare`
and `condensedOpenImage_weil`.
-/
theorem condensedOpenImageDelta (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left] :
    DlOpenImageAssertions (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀) ∧
      ∃ sq : CommSq (StrictWeil.modelFrobenius D U₀).hom (dlGeometricOpen D j₀)
          (dlGeometricOpen D j₀) (StrictWeil.modelFrobenius D C₀).hom,
        DlOpenImageWeilAssertions (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀) sq := by
  obtain ⟨sq⟩ := condensedOpenImage_frobeniusSquare
    D ell _hEll _iota U₀ C₀ j₀
  have hCounit := condensedOpenImage_underivedCounit D ell _hEll _iota U₀ C₀ j₀
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro M
      rcases condensedOpenImage_basic D ell _hEll _iota U₀ C₀ j₀ M with ⟨hn, h0⟩
      rcases condensedOpenImage_constructibility D ell _hEll _iota U₀ C₀ j₀ M with
        ⟨hc0, hcr, hp⟩
      exact ⟨hn, h0, hc0, hcr, hp⟩
    · refine ⟨?_, ?_⟩
      · exact hCounit
      · refine ⟨?_, ?_⟩
        · exact condensedOpenImage_exactness D ell _hEll _iota U₀ C₀ j₀
        · exact condensedOpenImage_naturality D ell _hEll _iota U₀ C₀ j₀
  · exact ⟨sq, condensedOpenImage_weil D ell _hEll _iota U₀ C₀ j₀ sq⟩

end AlgebraicGeometry.ProEtale.CondensedRing
