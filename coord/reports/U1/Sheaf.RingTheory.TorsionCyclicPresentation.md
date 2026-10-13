## What changed

Replaced the sole hole in `Sheaf.RingTheory.TorsionCyclicPresentation` with a complete
proof of `Ideal.exists_torsion_cyclic_presentation`, keeping its signature and all
four public imports unchanged. The proof uses `Nat.find` for the least positive
annihilating exponents, `Submodule.liftQ` and `LinearMap.toSpanSingleton` for the
cyclic maps, and `DirectSum.toModule` to assemble the surjection. Direct-sum induction
proves torsion with exponent 1 at zero, the defining exponent on a summand, and
`max` for sums. Subtype extensionality transfers torsion to the kernel;
`LinearMap.shortExact_shortComplexKer` gives the final short exactness.

Updated the existing node's proof, proof dependencies and proof origin to match.
Read the unit record `sk-thm-p1`: this node realizes none of its fixed steps,
and the unit route is unchanged. The source text is absent in this machine's
literature directory, so the source was read at
[Stacks Tag 05E8](https://stacks.math.columbia.edu/tag/05E8), proof, first two sentences.

Searches actually run: LeanFinder for an ideal-power torsion module as a quotient
of a direct sum of ideal-power quotients (no direct match); Loogle for
`LinearMap.shortExact_shortComplexKer` (exact matching final clause); grep and
local ripgrep for the cyclic presentation, direct-sum API, quotient lifting,
ideal-power monotonicity, and kernel short exactness. No new theorem is needed.

## Proved and sorry left

Closed: `Ideal.exists_torsion_cyclic_presentation`
(node `lem-weil-pbc-torsion-cyclic-presentation`). One of one original holes proved.
No holes remain in the module; no holes or declarations were added elsewhere.
Local compilation completed without warnings. The delivery dry run also checks
axioms against the permitted three.

## No longer needed

The proof does not need node `lem-weil-pbc-ring-modules-grothendieck-abelian`
(Mathlib module `Mathlib.Algebra.Category.ModuleCat.AB`); it was removed from
this node's proof dependencies. Short exactness follows directly from Mathlib's
surjective-linear-map kernel lemma. No imports were removed: each of the four
existing public imports supplies the statement's direct sum, ring quotient,
ideal powers, or kernel short complex. The direct-sum, quotient-module and
exact-sequence definition nodes are still used. No other planned nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan invoked Grothendieck abelianity for short exactness,
which is unnecessary. Its finite-support maximum argument can be implemented
more directly by induction on direct sums, using the maximum of two exponents
in the addition case. Neither adjustment changes the statement or the unit route.
There are no statement disputes, interface changes, or forced adaptations.

## Second reading by U1

1. Compared the delivered Lean module with the repository version using a full diff
   and asserted byte-for-byte equality of the existing theorem signature. Only its
   proof and proof-description docstring differ; there are no added declarations,
   changed definitions, hypotheses, conclusions, or visibility changes. Pass.
2. Independently compiled the delivered module with lcompile.py: no errors or
   warnings. Compiled a scratch copy with `#print axioms
   Ideal.exists_torsion_cyclic_presentation`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry or prohibited declaration occurs
   in the delivered module. The exponents are Nat.find values determined by the
   supplied torsion hypothesis, not witnesses of an unproved existence theorem. Pass.
3. No statements were split off and no new holes were added. Checked the argument
   at zero, the zero ideal, the unit ideal (where the torsion hypothesis forces Q
   to be zero), and the zero ring: positive exponents and the quotient/kernel
   construction remain valid in every case. Pass.
4. Read the construction from the theorem downwards: quotient lifts give the
   cyclic maps, the image of one gives surjectivity, direct-sum induction proves
   torsion, and subtype extensionality proves kernel torsion. A fresh LeanFinder
   search using “killed elementwise by powers of an ideal” and local searches
   found no shorter matching presentation theorem; returned adic-completion and
   PID results have different hypotheses/conclusions. All four public imports
   supply entities in the existing signature: direct-sum module structure, ideal
   quotient, ideal powers, and the kernel short complex/ShortExact predicate.
   No proof-only import is public. The old proof dependency omitted by the new
   proof is exactly `lem-weil-pbc-ring-modules-grothendieck-abelian`, already
   listed above. Read sk-thm-p1's realized statement and steps: this item is in
   none of them, and the unit route is preserved. Pass.
5. Compared both node versions: only proof, proof_deps, and proof_origin change.
   The union of the steps' uses equals the three retained proof dependencies,
   and the text accurately follows the Lean construction. No new node or
   change record is required. Pass.

Second reading changed only this report by adding the independent review.
The Lean proof and DAG update were correct and needed no repair.
