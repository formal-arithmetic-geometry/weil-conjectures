/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Triangularization of a single endomorphism

Over an algebraically closed field every endomorphism of a finite dimensional vector space
can be put in upper triangular form. Equivalently, it preserves a *complete flag*: an
increasing chain of subspaces starting at `⊥`, ending at `⊤`, whose `i`-th member has
dimension `i`, so that all graded pieces are one dimensional.

## Main results

- `Module.End.exists_invariant_flag`: the existence of such a flag (blueprint
  `sk-p-linear-triangular`).
-/

@[expose] public section

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Blueprint `sk-p-linear-triangular`: Triangularization.

A single endomorphism `f` of a finite dimensional vector space `V` over an algebraically
closed field `K` admits a full flag of invariant subspaces with one dimensional graded
pieces: there is a monotone family `F : Fin (n + 1) → Submodule K V`, where
`n = finrank K V`, with `F 0 = ⊥`, `F (Fin.last n) = ⊤`, each `F i` mapped into itself by
`f`, and `finrank K (F i) = i`. A basis adapted to such a flag puts `f` in upper triangular
form, with the eigenvalues of `f` on the diagonal.

The flag is indexed by `Fin (n + 1)` rather than by `ℕ` so that the dimension condition
pins it down completely; the successive quotients are one dimensional by the dimension
condition alone, so they are not recorded separately.

Mathlib has the generalized eigenspace decomposition `Module.End.iSup_maxGenEigenspace_eq_top`
over an algebraically closed field, but no flag statement; indeed its
`Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` lists triangularizability as a
`TODO`. -/
theorem exists_invariant_flag [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ F : Fin (Module.finrank K V + 1) → Submodule K V,
      Monotone F ∧ F 0 = ⊥ ∧ F (Fin.last _) = ⊤ ∧
      (∀ i, (F i).map f ≤ F i) ∧ ∀ i, Module.finrank K (F i) = (i : ℕ) :=
  sorry

end Module.End
