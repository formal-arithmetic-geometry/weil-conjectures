/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.Paper.FiniteProjectiveTensorProducts
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.CompletedReductionTensorModelComparison

/-! # A strict-perfect tensor model of completed finite reduction

Source: proper base change, finite-reduction-reconstruction, order 1249, step 1;
completed-constant-sheaf-reduction; Stacks Tags 099M and 091Z.
(blueprint: lem-weil-pbc-completed-reduction-strict-perfect-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Finite scalar reduction, after restriction, is tensor by a bounded complex
of finite-free retracts over the completed coefficient sheaf.

Source: blueprint finite-reduction-reconstruction, order 1249, step 1;
completed-constant-sheaf-reduction, bounded finite-projective representative clause;
Stacks Tags 099M and 091Z.
(blueprint: lem-weil-pbc-completed-reduction-strict-perfect-model).

Proof: perfectness of the positive quotient supplies a bounded complex of finite
projective A-modules representing A/I^(n+1). Choose degreewise finite-free splittings,
including rank zero outside its bounds. Apply constant sheafification and extension
to A_T to this complex and its splittings. Additivity preserves the splitting
identities and zero terms, yielding P, its bounds, and its strict-perfect package.
The completed-constant-sheaf reduction theorem identifies its augmentation with the
quotient sheaf, for the actual limit projection A_T to (P_n)_T. On each K-flat test
complex, tensor that augmentation and use tensor balancing to identify the result
with scalar extension followed by restriction. All maps commute with chain maps and
quasi-isomorphisms between K-flat test complexes. The universal left-derived property
of scalar extension and the localization property defining finiteProjectiveTensorRight
then extend these comparisons to a natural isomorphism on the entire unbounded derived
category. The construction also works for a zero quotient or the empty scheme, using
zero objects and rank-zero splittings. -/
theorem completedReductionStrictPerfectModel (n : ℕ) :
    ∃ (P : CochainComplex (adicDatumModules T d) ℤ)
      (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
      (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((adicLisseForget T).obj (adicDatumRing T d)) P),
      Nonempty (finiteProjectiveTensorRight T d P hb p ≅
        adicDatumReductionUnderlying T d n) := by
  let d' : AdicCoefficientDatum A :=
    { ideal := d.ideal
      noetherian := d.noetherian
      finitelyGenerated := d.finitelyGenerated
      quotientTorsion := d.quotientTorsion
      quotientPerfect := d.quotientPerfect
      quotientFinite := d.quotientFinite }
  obtain ⟨R⟩ := PerfectProjection.resolution_exists d' (X := T) (Y := T)
    ((DerivedCategory.singleFunctor (adicDatumModules T d) 0).obj
      (SheafOfModules.unit ((adicLisseForget T).obj (adicDatumRing T d)))) n
  exact ⟨R.coefficient, R.bounded, R.package,
    completedReductionTensorModelComparison T d n R.coefficient R.bounded R.package
      R.representsQuotient⟩

end AlgebraicGeometry.Scheme
