/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import Sheaf.Paper.TraceFormulaCoefficientSetup
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.DerivedPullbackTensorHom
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.Paper.FiniteTorStability
import Sheaf.Paper.SfCommonStageDirectImage

/-!
# Topological invariance of the trace-formula coefficient category

Source: Weil conjectures blueprint, main-20261015,
`sec-trace-formula/sk-i-topology/i-topology.md` (blueprint: i-topology).

The equivalence is identified with the recorded derived pullback through the full
subcategory inclusions. Its inverse is identified with both ordinary derived direct
image and the specified compactification's compact-support direct image. The unit and
counit are the natural isomorphisms supplied by the equivalence, not just objectwise
existence assertions. All three operations use the intrinsic constant-ring realization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The full conclusion of topological invariance, packaged without choosing an equivalence.
The functor and inverse are identified naturally with the actual recorded operations,
after the fully faithful inclusions into the ambient derived categories. In particular
both operations preserve the finite-Tor constructible subcategories. The equivalence's
`unitIso` and `counitIso` give the invertible unit and counit with their triangle identities.
The compactification parameter specifies the existing definition of `Rr_!`.
Source: blueprint, main-20261015, proposition `i-topology` (blueprint: i-topology). -/
def TraceFormulaTopologicalEquivalence (T : TraceFormulaCoefficientConventions.{u})
    {X Y : Scheme.{u}} (r : X ⟶ Y) (c : Compactification r) : Prop :=
  ∃ e : finiteTorConstructibleCategory T.coefficients.l T.coefficientField
      T.level T.level_pos Y ≌
        finiteTorConstructibleCategory T.coefficients.l T.coefficientField
          T.level T.level_pos X,
    Nonempty (e.functor ⋙
        (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos X).ι ≅
      (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos Y).ι ⋙
        T.derivedPullback r) ∧
    Nonempty (e.inverse ⋙
        (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos Y).ι ≅
      (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos X).ι ⋙
        proEtaleConstantDerivedDirectImage r T.coefficientRing) ∧
    Nonempty (e.inverse ⋙
        (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos Y).ι ≅
      (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos X).ι ⋙
        @sfIntrinsicCompactSupport X Y r c T.coefficientRing inferInstance
          (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
            T.level T.level_pos))

/-- Finite universal homeomorphisms induce the asserted pullback equivalence on `Dᵇ_ctf`,
with inverse both `Rr_*` and `Rr_!` and invertible unit and counit, including reduction.
Here `X` and `Y` are arbitrary separated finite-type schemes over the geometric field of
the coefficient conventions; neither is required to descend to their stored model `X₀`.
The positive coefficient level, finite extension in the fixed algebraic closure, and
prime different from the characteristic are all part of `T`.
Source: blueprint, main-20261015, proposition `i-topology` (blueprint: i-topology).

Proof:
1. Apply `lem-trf-proetale-topological-invariance` to obtain the actual inverse/direct
image equivalence of pro-etale topoi, with invertible specified unit and counit.
2. Transport addition, zero and scalar action using
`prop-weil-pbc-proetale-constant-ring-map`. Naturality makes the unit and counit linear.
The pullback is the exact functor of `prop-weil-pbc-proetale-constant-exact`; its inverse
is exact because an equivalence preserves kernels and cokernels.
3. Apply the two exact functors termwise to complexes. They commute with cohomology
and preserve quasi-isomorphisms, so their unit, counit and triangles descend through
derived localization. The resulting pullback is the recorded finite derived pullback.
Exact direct image sends a K-injective resolution map to a quasi-isomorphism, identifying
its termwise descent with the recorded total right-derived direct image.
4. Finite morphisms are proper and hence separated of finite type. Clauses (i) and (iii)
of `thm-sf-ctf-stability` preserve precisely the bounded constructible finite-Tor
subcategories. Restrict both functors and their unit and counit to these full subcategories.
5. The proper comparison in clause (3) of `prop-functor-package` identifies `Rr_!`
with `Rr_*`. Transport the inverse equivalence through this natural isomorphism;
naturality gives the two triangle identities, and both maps remain invertible.
6. The reduction immersion is a surjective closed immersion and a universal homeomorphism
by `lem-weil-pbc-reduction-universal-homeomorphism`, and closed immersions are finite.
Reduction is still finite type over the field: affine coordinate rings are quotients
of the original finitely generated algebras. Its diagonal is the base change of the
original closed diagonal, so it is separated. Apply the first part to this immersion.
No nilpotence or finite generation of the nilradical is required. -/
theorem finiteUniversalHomeomorphism_traceFormula
    (T : TraceFormulaCoefficientConventions.{u}) :
    (∀ (X Y : Over (Spec (CommRingCat.of T.datum.k)))
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (r : X ⟶ Y) [IsFinite r.left],
      (topologically IsHomeomorph).universally r.left →
      ∀ c : Compactification r.left, TraceFormulaTopologicalEquivalence T r.left c) ∧
    (∀ (Y : Over (Spec (CommRingCat.of T.datum.k)))
      [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (c : Compactification Y.left.nilradical.subschemeι),
      TraceFormulaTopologicalEquivalence T Y.left.nilradical.subschemeι c) := by
  sorry

end WeilConjectures
