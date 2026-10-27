/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.AdicStratifiedPerfectData

import Sheaf.Paper.GeneralLfpAdicInputWitness

/-! # Adic input witnesses in the fixed projection-normalized presentation

Source: Bhatt--Scholze, Definition 6.5.1 and Proposition 6.8.11(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})


/-- General-lfp inputs satisfy the adic predicate in the fixed section-action presentation.
This compares presentations of the same object; it does not complete that object.

Source: Bhatt--Scholze, Definition 6.5.1 and Proposition 6.8.11(3); the scalar
normalization in the general-lfp input witness
(blueprint: lem-sfb-integral-adic-input-normalization).

Proof: identify the continuous integral coefficient ring in the witness with the spectral
integer ring by WithAbs.equiv on values. This is an isometric ring isomorphism, so scalar
restriction is an exact equivalence and carries the given general constructible input to
the witness's input. The section-action equivalences retain all sections and their scalar
actions. The composite of integralSectionRingIso, integralDetailedCoefficientComparison
and pbcCompletedComparison sends a constant scalar to its image in every positive quotient.
Thus it satisfies the witness's IsNormalized equation. Its uniqueness clause identifies
this composite with the coefficient comparison chosen by the witness. Localizing the
termwise section equivalences therefore identifies the witness's transported representative
with F(M). Transport completeness and the residue isomorphism along this derived
isomorphism. The same quotient projections identify the residue coefficient actions and
retain the etale complex, its cohomology bounds and its Tor tests. Consequently every
clause of IsSfbAdicConstructible holds for F(M). This includes torsion modules and the
zero object, and uses no extra completeness assumption. -/
theorem integralAdicInput_normalization
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (M : DerivedCategory (AdicCompletion.Modules l E X))
    (hM : boundedConstructible (AdicCompletion.ring l E X) M) :
    Scheme.IsSfbAdicConstructible X (Scheme.pbcIntegralDatum l E).ideal
      (((integralSectionDerivedEquivalence l E X).functor ⋙
        Scheme.integralDetailedTransport X l E ⋙
        Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
          (Scheme.pbcIntegralDatum l E)).hom).obj M) := by sorry

end AlgebraicGeometry.ProEtale
