/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import Sheaf.Paper.DerivedGeometricStalk
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.Paper.PointSectionsFiniteness
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.FiniteTensorConstructibleCohomology
import Sheaf.Paper.ProEtaleResidueTorTest
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Paper.GeometricStalkPerfect
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.Paper.FiniteTorAmplitudeSites

/-!
# Perfect compact-support cohomology and geometric stalks

Source: Weil blueprint main-20261015, sec-smooth-purity/sk-prop-sf-trace-perfectness,
`prop-trf-compact-support-perfectness.md`
(blueprint: prop-trf-compact-support-perfectness).

Perfectness uses the bounded finite-projective predicate of the categorical-trace
convention, rather than the larger bounded finite-cohomology category. The helper
only specializes the recorded derived geometric stalk to the positive coefficient
level stored in the conventions, transporting along `(level - 1) + 1 = level`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace TraceFormulaCoefficientConventions

/-- The recorded ordinary-module derived geometric stalk, specialized to the coefficient
level of `T`. The coefficient prime is a unit in every local ring by transporting its
inverse from the base field along the structure map and the germ. The level equality
only reindexes the existing positive-level construction; no stalk functor is chosen.
Source: blueprint main-20261015, compact-support perfectness, geometric-stalk clause,
and `pur9-def-derived-stalk`
(blueprint: prop-trf-compact-support-perfectness). -/
def perfectnessDerivedGeometricStalk (T : TraceFormulaCoefficientConventions.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ T.geometricBaseChange)
    (K : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) := by
  have hX : ∀ x : T.geometricBaseChange,
      IsUnit (T.coefficients.l : T.geometricBaseChange.presheaf.stalk x) := fun x ↦
    let φ : T.datum.k →+* T.geometricBaseChange.presheaf.stalk x :=
      (T.geometricBaseChange.presheaf.germ ⊤ x trivial).hom.comp
        (T.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (.of T.datum.k)).inv.hom)
    (map_natCast φ T.coefficients.l) ▸
      (finiteFieldDatumPrimeUnit T.datum T.coefficients.l T.coefficients.different).map φ
  unfold coefficientRing at K ⊢
  rw [← Nat.sub_add_cancel T.level_pos] at K ⊢
  exact finiteDerivedGeometricStalk T.coefficients.l T.coefficientField (T.level - 1)
    T.geometricBaseChange hX Ω xbar K

/-- Both compact-support cohomology and every ordinary-module derived geometric stalk
are perfect at the finite coefficient level. The compactification is the representative
already used in the recorded compact-support construction, and is arbitrary.
Source: blueprint main-20261015, compact-support perfectness, statement and proof
(blueprint: prop-trf-compact-support-perfectness).

Proof:
1. Put F = Ra_X! K and C = Fib_s(F). Finite compact-support constructibility makes F
   bounded constructible; point-sections finiteness gives bounded finite cohomology of C.
   This alone does not establish perfectness over the finite local coefficient ring.
2. Reduce K to the residue field. K-flat change of rings and the scalar-tensor comparison
   identify this with its derived tensor by the constant residue sheaf. Tensor
   constructibility and the Tor interval of K give bounded constructibility of this
   residue-coefficient input. Its finite-module trivializations are residue-linear.
3. Compact-support coefficient change identifies the residue reduction of F with compact
   support of that input, as residue-coefficient objects on the small pro-etale point.
4. Finite compact-support constructibility at residue level bounds this reduction.
   The pro-etale residue Tor test gives finite Tor amplitude for F itself.
5. For bounded constructible objects, descend to the etale site. Comparison pullback,
   its unit on the final object, the geometric-point germ and comparison-stalk maps
   identify the geometric stalk with sections of the pullback to Spec Ω. Inverse image,
   comparison, point sections and the geometric stalk are exact, so this identification
   passes to complexes and agrees with the recorded ordinary-module derived stalk.
6. Apply the finite-free stalk lemma to F at the identity geometric point of Spec k.
   Exact point sections identify this stalk with C. The finite-free model is in
   particular a bounded finite-projective model, proving the compact-support clause.
7. Apply the same finite-free stalk lemma directly to K at any geometric point. Step 5
   identifies its output with the displayed derived stalk, proving its perfectness.
   No finite-type condition on the geometric point or its source is needed. -/
theorem compactSupport_perfect
    (T : TraceFormulaCoefficientConventions.{u}) (c : Compactification T.structureMap)
    (K : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing)
    (hK : T.boundedConstructibleFiniteTor K) :
    @DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        (ULift.{u + 1, u} T.coefficientRing) _
        (HasDerivedCategory.ofIsGrothendieckAbelian _)
        (T.compactSupportComplex c ⟨K, hK.1⟩).obj ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (xbar : Spec (.of Ω) ⟶ T.geometricBaseChange),
        DerivedCategory.IsPerfectRingComplex.{u + 1, u + 2}
          (T.perfectnessDerivedGeometricStalk Ω xbar K) := by
  sorry

end TraceFormulaCoefficientConventions
end WeilConjectures
