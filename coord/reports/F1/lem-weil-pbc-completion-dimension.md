## Worker report

The module states `RingTheory.completion_dimension` for a commutative Noetherian
local ring `A`. `IsNoetherianRing A` renders the Noetherian hypothesis and
`IsLocalRing A` renders locality; `AdicCompletion (IsLocalRing.maximalIdeal A) A`
renders the maximal-ideal completion. The conjunction's first clause is equality
of Krull dimensions, and the two `< ⊤` clauses render finiteness of both dimensions.
The proof is `sorry`, with the documented route through the flat local dimension
formula, residue-field closed fibre, and Noetherian finiteness.

Dependencies used: `IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs` and
`AdicCompletion` from `Mathlib.RingTheory.AdicCompletion.Basic` (with its local and
Noetherian instances from `Mathlib.RingTheory.AdicCompletion.LocalRing` and
`Noetherian`).

Edge cases checked: the maximal ideal is used uniformly, including the zero ring's
local instance; `ringKrullDim` is retained as `WithBot ℕ∞`, so zero-dimensional and
finite cases are included; no finite-generation or characteristic hypothesis is
added.

Searches: `msearch.py leanfinder` for completion dimension (no match); `msearch.py
loogle` for `ringKrullDim (AdicCompletion _ _)` (none); grep of Mathlib AdicCompletion
and KrullDimension (no completion-dimension theorem); `rg` over WeilConjectures and
lean/Sheaf (no existing declaration).

## Earlier second reading (a previous round; superseded)

The node and module were read together. The Noetherian and local hypotheses map to
explicit typeclass binders, the completion uses the node's m-adic completion at the
canonical maximal ideal, and all three conclusion clauses (equality and finiteness
of each dimension) are present. No mismatch was found.

## Second reading by F1

Independent reading of the sandbox node, both statement dependencies, their Mathlib
source declarations, and the module. The mathematical statement is correct and the
Lean conclusion has exactly its three clauses; no node statement correction is needed.
There are no new definition nodes or dependency modules in this delivery.

Source checked on the server (the local literature checkout omits Stacks sources):
more-algebra.tex lines 10610–10641, including the section's standing conventions and
Lemma 07NV. It assumes a Noetherian local ring and uses its maximal-ideal completion;
no characteristic, field, completeness of A, domain, or extra finiteness hypothesis
is assumed. The alternative proof points to Algebra 00ON, read at lines 27420–27434:
the going-down dimension formula for Noetherian rings applies to flat maps.

Object/hypothesis/conclusion checklist, with verdicts:

- A commutative ring: `(A : Type u) [CommRing A]`; exact. Stacks' ring convention is
  commutative, and u is explicitly declared and arbitrary.
- A Noetherian: `[IsNoetherianRing A]`; exact. Read Noetherian/Defs.lean lines 62,
  196–204: this is every A-submodule of A, equivalently every ideal, finitely generated,
  precisely `def-weil-pbc-noetherian-ring`'s recorded declaration.
- A local with unique maximal ideal m: `[IsLocalRing A]` and
  `IsLocalRing.maximalIdeal A`; exact. Read LocalRing/Defs.lean lines 14–34 and
  LocalRing/MaximalIdeal/Defs.lean's maximalIdeal construction. Its nontriviality follows from
  having a maximal ideal; it is not an added hypothesis.
- The m-adic inverse limit A^: `AdicCompletion (IsLocalRing.maximalIdeal A) A`;
  exact. Read AdicCompletion/Basic.lean lines 167–173: compatible families over
  natural powers, with M = A, so I^n • top is I^n. Algebra.lean supplies its canonical
  commutative ring structure. This uses `def-weil-pbc-adic-completion`'s recorded
  notion, rather than a private completion.
- The parenthetical Noetherian/local nature of A^ and its extended maximal ideal
  describe the completion, rather than add assumptions. Mathlib LocalRing.lean
  lines 85–98 gives locality and `maximalIdeal_eq_map`; completion Noetherianity is
  the proof's cited node `lem-weil-pbc-adic-completion-noetherian`.
- Krull dimension: `ringKrullDim`, read KrullDimension/Basic.lean lines 27–31,
  is the dimension of the prime spectrum ordered by inclusion; exact.
- Equality dim A^ = dim A: the first conjunct, verbatim
  `ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = ringKrullDim A`;
  exact, with no special case or extra quantifier.
- Finiteness of dim A^: the second conjunct
  `ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) < ⊤`; exact.
- Finiteness of dim A: the last conjunct `ringKrullDim A < ⊤`; exact.
  These dimensions live in WithBot ENat; locality ensures the spectrum is nonempty,
  so excluding top means finite nonnegative dimension, not a spurious bottom case.

Edge cases: fields (m = 0) and zero-dimensional nonreduced local rings are covered;
there is no positive-dimension or domain assumption. The n = 0 inverse-limit
component is the quotient by the unit ideal, harmless and already included by
Mathlib. Arbitrary characteristics and arbitrary universe u are allowed. Empty
schemes and arbitrary index sets do not occur here. The zero ring has no maximal
ideal and is not local under Stacks' definition (algebra.tex lines 3311–3320);
Mathlib's IsLocalRing extends Nontrivial. Thus its exclusion is exact. The worker
report's claim about a zero-ring local instance is incorrect and superseded by this
check. No hollow definitions or unbound parameters occur; the sole theorem has
only `sorry` as its proof.

Independent searches (2026-10-11), using words different from the first worker:
`msearch.py leanfinder "The maximal ideal completion preserves the dimension of a
local Noetherian commutative ring"` returned eight results on local Krull dimension
and finiteness, none on completion equality. `msearch.py loogle "AdicCompletion,
ringKrullDim"` returned zero hits. `msearch.py grep "completion_dimension|dimension.*
completion|completion.*dimension|07NV|AdicCompletion.*ringKrullDim|ringKrullDim.*
AdicCompletion" RingTheory` returned zero hits. A separate rg search for those
names/concepts over WeilConjectures, the repository lean/Sheaf, and Mathlib/RingTheory
also returned no declaration. Both dependency notions already exist and are used.
No existing theorem replaces this module.

Mismatches repaired: moved the pure ring-theory module from AlgebraicGeometry to
RingTheory and updated its module/file record; added the conventional copyright
header and source-bearing module docstring; expanded the theorem docstring to
all four node proof steps, including contraction, localization, closed fibre and
the generator bound with their dependency ids; replaced imports with the definition
modules used in the signature; synchronized lean.statement with the exact multiline
signature (the prior record omitted a line break before IsLocalRing). The theorem's
binders and conclusion, node statement, and dependencies were already right and
are unchanged. The original Worker report remains above.
