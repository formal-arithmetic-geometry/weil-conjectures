/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.Paper.CommonStageLisse
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.ConstantExtensionCompactComparison
import Sheaf.CategoryTheory.NaturalTransportPowers
import Sheaf.Paper.LocalFrobeniusTransportNormalization
import Sheaf.TraceFormula.CompactFrobeniusTransportComposition
import Sheaf.Paper.IteratedWeilCocycle
import Sheaf.Paper.LocalFrobeniusConjugacyClass
import Sheaf.AlgebraicGeometry.ClosedPointField
import Mathlib.FieldTheory.Finite.Basic
import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.Paper.AdicPunctualWeights
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.LisseIntegralSmallCoefficients
import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.SixFunctors.FrobeniusCohomologyTransport

/-! # Constant extension of a lisse Weil sheaf and Frobenius powers

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-p-dl-general-relative-line/lem-zl-affine-curve-hc2-purity.proof.md,
second paragraph (blueprint: lem-zl-weil-constant-extension-frobenius).

The common geometric fibre is used as coordinates for both coefficient cohomologies.
The extended Weil structure is specified by ConstantExtensionRestrictionSpec, including
its underlying identification and its normalized iterated structure map. In these
coordinates the extended operator is the recorded global geometric Frobenius for
the actual extension datum and model, on the actual restricted Weil object. The
comparison is fixed by the canonical proper/open fibre comparison and the underlying
isomorphism in the restriction specification, followed by coefficient cohomology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- Restriction to F_(q^e) retains the underlying lisse coefficient sheaf, replaces
its Weil map by theta^[e], raises compact-cohomology Frobenius to its eth power,
raises local Frobenius by the residue degree, and preserves every punctual weight.
The fibre equation states that the extended geometric Frobenius is g_X^e.
The compact-cohomology equation compares the two recorded global geometric
Frobenius operators through constantExtensionCompactCohomologyComparison.

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-p-dl-general-relative-line/lem-zl-affine-curve-hc2-purity.proof.md,
second paragraph (blueprint: lem-zl-weil-constant-extension-frobenius).

Proof:
1. Keep the actual subfield k_e of the fixed closure and the associativity fibre
isomorphism. On affine tensors geometric Frobenius acts by gamma on the closure
factor. The new finite base has coefficient action gamma^e, proving the fibre
identity. Pullback along this identification preserves lissity. Compose theta,
g^*theta, ..., (g^(e-1))^*theta with the normalized pullback compositors. The iterated
Weil cocycle (lem-trf-iterated-weil-cocycle) gives exactly RestrictionSpec below.
2. At finite coefficient level point transports and direct power-square compact
exchanges compose with the same compositors
(lem-trf-compact-frobenius-transport-composition). Pass to rational coefficients.
The extended recorded operator uses the actual extension datum and restricted
Weil object. The comparison is normalized by the proper/open fibre mate before
rationalization and the restriction carrier isomorphism. Naturality moves each
theta past the next transport. The abstract
identity inducedEndomorphism_pow (lem-trf-global-frobenius-iterate-formula)
identifies the result with F_q^e. Compute H^r at each finite Weil presentation
and extend scalars to Ω. Every fixed pair descends after a finite stage enlargement,
as its structure map, inverse and inverse equations have common representatives.
The normalized scalar comparisons identify all these presentations with the recorded
coefficient cohomology. The comparison is identity on the common geometric fibre.
3. A closed point z over x has finite residue extension of degree d. Finite-field
Galois theory (lem-sfb-finite-field-galois-frobenius) identifies its return as d
returns at x. The stalk transport and theta cocycle therefore give F_x^d. Changes
of residue embeddings conjugate the operator (lem-weil-local-frobenius-conjugacy-class).
This is checked on finite Weil presentations and extended to Ω; no semisimplicity
is used. Closed residue fields are finite (lem-kun-closed-point-field).
4. If alpha is a local eigenvalue at x, the eigenvalues at z are alpha^d and
#kappa(z)=#kappa(x)^d. Consequently |iota(alpha^d)|=|iota(alpha)|^d equals
#kappa(z)^(w/2). This is precisely the recorded punctual-purity predicate over k_e.
5. All constructions are on the underlying sheaf and its finite-field actions.
They require no geometric connectedness, component choice or semisimplicity.
For e=1 they are the original constructions. Zero stalks have no eigenvalues,
and zero or empty compact cohomology satisfies the operator equality. -/
theorem weil_constant_extension_frobenius (e : ℕ) (he : 1 ≤ e) (iota : Ω ≃+* ℂ) :
    (((constantExtensionDatum D e he).geometricFrobenius
        (constantExtensionModel D e he X₀)).hom ≫
          (constantExtensionFiberIso D e he X₀).hom =
      (constantExtensionFiberIso D e he X₀).hom ≫
        localPositivePower (D.geometricFrobenius X₀).hom (e - 1)) ∧
    ∃ R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
        sfCommonStageWeilSheaf (constantExtensionDatum D e he) l hl
          (constantExtensionModel D e he X₀) Ω,
      ∃ hR : ConstantExtensionRestrictionSpec D e he X₀ l hl Ω R,
      ∀ (F : sfCommonStageWeilSheaf D l hl X₀ Ω),
        HasCommonStageLisseLattice l Ω (D.geometricFiber X₀).left F.obj.carrier →
        HasCommonStageLisseLattice l Ω
          ((constantExtensionDatum D e he).geometricFiber
            (constantExtensionModel D e he X₀)).left (R.obj F).obj.carrier ∧
        (∀ (c : Compactification X₀.hom),
          ∃ C : ConstantExtensionCompactComparison l D hl X₀ e he Ω c,
            ∀ r : ℤ,
              (constantExtensionCompactCohomologyComparison
                l D hl X₀ e he Ω c C R hR F r).hom ≫
                  globalGeometricFrobeniusQbarOnCohomology
                    (constantExtensionDatum D e he) l hl
                    (constantExtensionModel D e he X₀) Ω
                    (constantExtensionModelCompactification D X₀ e he c)
                    (R.obj F).obj true r =
                ((End.of (globalGeometricFrobeniusQbarOnCohomology D l hl X₀ Ω c
                  F.obj true r)) ^ e) ≫
                  (constantExtensionCompactCohomologyComparison
                    l D hl X₀ e he Ω c C R hR F r).hom) ∧
        (∀ z : {z : (constantExtensionModel D e he X₀).left //
            z ∈ closedPoints (constantExtensionModel D e he X₀).left},
          ConstantExtensionLocalConjugacy D e he X₀ l hl Ω X₀ F (R.obj F)
            (constantExtensionClosedImage D e he X₀ z) z
            (constantExtensionResidueDegree D e he X₀ z.val)) ∧
        ∀ w : ℝ, SfIsPunctuallyPureOfWeight D l hl Ω X₀ iota F w →
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D e he) l hl Ω
            (constantExtensionModel D e he X₀) iota (R.obj F) w := by
  sorry

end WeilConjectures
