/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperPushforwardKernel

/-!

# Proper pushforward compatibility of the trace class

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper map of fixed
loci `h`, the Borel–Moore pushforward of the trace class of `u` is the trace class of the pushed
correspondence: `h_* Tr_c(u) = Tr_b([f, g]_! u)` (blueprint `thm-trf-trace-proper-compatibility`,
`sk-p-proper`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y) (Fc : c.FixedLocus)
  (Fb : P.pushforward.FixedLocus)

/-- **Proper pushforward compatibility of the trace class** (blueprint
`thm-trf-trace-proper-compatibility`, `sk-p-proper`; Varshavsky 1.2.5): for a proper pushforward
diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper map of fixed loci `h`,
`h_* Tr_c(u) = Tr_b([f, g]_! u)`. No properness over `s` and no cartesian leg square are needed.
The special case `f = 𝟙` is blueprint `lem-trf-proper-pushforward-trace-class`. The proof in the
blueprint goes through the exchange of the trace maps (`lem-trf-trace-map-exchange`) and of the
trace-class sources (`lem-trf-trace-source-exchange`), coherences of the compactification data
which are not among the stated axioms (blueprint `rem-sf-trace-coherence`). -/
theorem traceClassPushforward_eq :
    P.traceClassPushforward Fc Fb = P.pushforward.traceClass Fb :=
  sorry

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
