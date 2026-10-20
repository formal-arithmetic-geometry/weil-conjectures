/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Paper.PbcCohomologySheaves
public import WeilConjectures.SixFunctors.Etale.Perverse.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # The support condition on the actual adic Qbar coefficient category

Source: blueprint def-per-support-condition (blueprint: def-per-support-condition).
The finite-torsion support/cosupport definitions remain publicly imported. This
specialization supplies the support predicate consumed by the Qbar Tate-twist lemma;
it uses the same dimension inequalities on the actual adic cohomology fibres.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (X : Scheme.{u})
  [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Closed support is the closure of the locus of nonzero adic geometric fibres.
Source: blueprint support convention, used verbatim by the support-preservation proof
(blueprint: def-per-support-condition). -/
def pbcQbarCohomologySupport (M : pbcQbarCategory l Ω X) (a : ℤ) : Set X :=
  closure {x | ¬ IsZero (pbcQbarCohomologyFibre l Ω X M
    (AlgebraicClosure (X.residueField x)) (X.algClosurePoint x) a)}

/-- The support inequalities for the actual finite-stage Qbar category. The guard
makes empty support satisfy every bound, including negative i; for nonempty support
negative i is impossible. This is precisely the convention dim(empty) = minus infinity.
Source: blueprint def-per-support-condition
(blueprint: def-per-support-condition). -/
def PbcSupportCondition (M : pbcQbarCategory l Ω X) : Prop :=
  ∀ i : ℤ, (pbcQbarCohomologySupport l Ω X M (-i)).Nonempty →
    0 ≤ i ∧ topologicalKrullDim (pbcQbarCohomologySupport l Ω X M (-i)) ≤
      (i.toNat : ℕ∞)

end AlgebraicGeometry.Scheme
