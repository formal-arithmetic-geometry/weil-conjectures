## What changed

Proved `Algebra.desingularization_inverted_quotient_equiv` without changing its
signature or either public import. Added two private, fully proved helpers in the
assigned module: `remove_redundant_localized_relations` constructs inverse maps
between the localized iterated quotient and the localized substituted quotient;
`localized_affine_presentation_quotient_equiv` constructs inverse maps eliminating
the affine auxiliary variables. The latter works for arbitrary polynomial shifts
and every nonnegative exponent. The public proof specializes it to exponent three
and the stated quadratic shift. Updated the existing node's proof and proof
 dependencies to follow these explicit constructions.

Read Stacks Tag 07CR, particularly the equations `h_i` and the identification of
`B_pi` with `A_pi[v]`, at https://stacks.math.columbia.edu/tag/07CR. The source text
and unit blueprint files are absent from this machine; the unit record was read.
The proof stays below the unit level and follows the source's route. Searches in
Mathlib and both library roots found ingredients rather than a direct theorem;
LeanFinder, Loogle and grep searches were run through msearch.py.

## Proved and sorry left

Closed the sole original hole, `Algebra.desingularization_inverted_quotient_equiv`
(node `lem-weil-pbc-popescu-desingularization-inverted-quotient`). Both private
helpers are completely proved. No holes remain and no holes were added; no new
public declarations or modules are delivered. The file compiles cleanly through
lcompile.py. The proof covers empty variable and relation index sets, zero rings,
and nilpotent parameters: it uses units only in localizations and never assumes
that such localizations are nonzero. All objects and maps are explicit constructions
from the given presentation and universal properties, with no arbitrary witness
chosen from an unproved existence theorem.

## No longer needed

Removed the proof-only import `Mathlib.RingTheory.Localization.Ideal`. Removed
`lem-weil-pbc-localization-quotient-commute` from this node's proof dependencies:
the proof directly constructs the quotient and localization maps and checks their
composites. No Sheaf or WeilConjectures proof dependency is needed. The polynomial
ring and presentation definition nodes remain. This does not claim that the
localization-quotient node is unnecessary to other targets or modules.

## Where the brief, the DAG or earlier work was wrong

No statement or source error was found. The planned localization-quotient
commutation route is unnecessary for this proof. During proof development,
explicit changes of the displayed goal followed by rewriting were needed to avoid
unnecessary unfolding of polynomial algebra structures. All such issues were
resolved in the delivered proof, without changing definitions or signatures.

## Second reading by K2

1. Compared the delivered module with the repository version. The public theorem signature and all existing declaration signatures are byte-for-byte unchanged; only proof text and a proof-only import were changed. Verdict: pass.
2. Compiled the module with lcompile.py. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The target's axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. The two private helpers are true, strictly intermediate constructions: explicit localization and quotient inverse maps, followed by the affine-variable equivalence. They do not restate the target, and no duplicate library theorem was found. Verdict: pass.
4. The proof follows the unit route through quotient and localization maps, while pruning the unused localization-quotient theorem import and dependency. Empty index sets and zero localizations are covered by the constructions. Verdict: pass.
5. The DAG proof and proof dependencies match the delivered Lean proof: the removed localization-quotient node is no longer used, and the two explicit constructions are recorded in the proof steps. Verdict: pass.

Changed only the proof implementation, removed the unused `Mathlib.RingTheory.Localization.Ideal` import, and updated the existing node's proof metadata to remove `lem-weil-pbc-localization-quotient-commute`.
