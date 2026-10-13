## What changed

Replaced the hole in `exists_adjoin_singleton_splitting_polynomial_cover` by a complete
Lean proof using a finite split coefficient algebra before maximal localization.
Added proof-only imports of `AdjoinSingletonFiniteSplitAlgebra`,
`FiniteAwayMaximalLocalization`, and `Mathlib.Algebra.BigOperators.Fin`.
The existing theorem signature and docstring are unchanged.

The new generic theorem `exists_finite_away_maximal_localization` is fully proved:
construct the canonical localization map, establish injectivity and module finiteness,
contract maximal ideals through the integral map to the unique maximal ideal of the
local ring, and deduce maximality of the contraction to the finite extension.
The target proves its denominator monoid consists of nonzero divisors, enumerates the
roots with multiplicity using `f.roots.toList.get`, proves positive length from the
degree, and evaluates the monic factorization to obtain membership simultaneously
for all maximal ideals. No roots or rings are defined by choosing an arbitrary witness
from an unproved existence theorem; existential witnesses are eliminated in proofs only.

Read Stacks Tag 0334, Step 5, at https://stacks.math.columbia.edu/tag/0334.
The local literature file named by the DAG is absent on this machine, so the official
source was read online. The two new statements retain the source's residue polynomial,
principal localization, splitting extension, and finite integral closure route.
The item's node is not one of the unit's `realized` statement or step nodes.

Validation: all three sandbox modules compile together without warnings using
`lcompile.py --all`. The original target proof needs a local heartbeat allowance for
elaboration of its existential ring structures and localization algebra; its compile
still takes less than 60 seconds. LeanSearch was unavailable (HTTP 500); actual
LeanFinder, Loogle, and grep searches are recorded in `searches.jsonl`.

## Proved and sorry left

Closed the original hole `exists_adjoin_singleton_splitting_polynomial_cover`
(node `lem-weil-pbc-monogenic-splitting-polynomial-cover`) by decomposition, rather
than claiming a sorry-free proof of the entire construction.

Added one hole: `exists_adjoin_singleton_finite_split_algebra`, node
`lem-weil-pbc-monogenic-finite-split-algebra`, in
`Sheaf.RingTheory.AdjoinSingletonFiniteSplitAlgebra`. Its whole proof is `by sorry`.
It supplies the finite injective extension of a principal localization and the split
polynomial evaluation in the extended ideal. It makes no maximal-localization or
maximal-contraction assertion and is strictly a part of the original argument.

Added and fully proved `exists_finite_away_maximal_localization`, node
`lem-weil-pbc-finite-away-maximal-localization`, in
`Sheaf.RingTheory.FiniteAwayMaximalLocalization`. No hole remains in this helper.
Original holes closed: 1. New holes added: 1. Net hole reduction: 0.

Edge cases: when the original coefficient ring is a field and x belongs to it,
a degree-one residue polynomial works. When s = 1 the generic localization theorem
reduces to localization of a finite extension at the complement of m. The proof uses
s outside m to exclude s = 0. Positive degree excludes the empty root product.
Repeated roots are retained by the multiset/list enumeration. No separability or
perfectness assumption is introduced. The generic theorem accommodates different
universes for S and T; module localization finiteness does not require equal universes.

## No longer needed

No existing imports were removed. No previously planned node is globally pruned:
the residue-polynomial and finite splitting construction still requires the first
two steps of the original plan. Those dependencies now belong to the new construction
node rather than directly to the item's node.

The following old proof dependencies are no longer direct dependencies of the item:

- `lem-weil-pbc-zariski-lemma`
- `lem-weil-pbc-nagata-localization`
- `def-weil-pbc-nagata-ring`
- `def-weil-pbc-japanese-domain`
- `lem-weil-pbc-integral-closure-finite-extension-normal`
- `lem-weil-pbc-finite-over-nagata-nagata`
- `def-weil-pbc-integral-closure`
- `def-weil-finitely-generated-module`
- `lem-weil-pbc-finite-algebra-is-integral`
- `lem-weil-pbc-integral-maximal-contracts-maximal`
- `lem-weil-pbc-integral-prime-over-maximal-maximal`
- `def-weil-pbc-localization-at-prime`

The construction dependencies remain below the finite-split-algebra node; the three
integrality/maximality lemmas and localization definitions are used by the proved generic
helper via their Mathlib matches. None is claimed globally unreachable.

The generic localization proof uses Mathlib directly for the finite algebra,
contraction, and localization facts; no unproved Sheaf localization helper is imported.
No unit statement or step is bypassed. The target's proof dependencies are now exactly
the two new nodes. The existing normal/Nagata/localization definition imports remain
public because its unchanged statement requires them.

## Where the brief, the DAG or earlier work was wrong

The DAG plan had no Lean interface combining the residue-polynomial lifting,
coefficient denominator localization, finite splitting extension, and finite monogenic
extension. These are isolated together in the new construction node. The generic
localization part and all polynomial enumeration/evaluation glue are now proved.
No false statement, interface change, or forced adaptation was needed.

## New nodes

`lem-weil-pbc-monogenic-finite-split-algebra` isolates Steps 1 and 2 before maximal
localization. Its statement, source, complete proof in words, searches, and matching
Lean module are included. It uses the original construction dependencies and excludes
the maximal contraction and root enumeration conclusions established in this delivery.

`lem-weil-pbc-finite-away-maximal-localization` records the fully proved generic
localization lemma used by the target. It is independent of normality, Nagata rings,
splitting fields, and polynomials. Its proof follows the localization paragraph of
Step 5 of Tag 0334 using Mathlib's universal property and integral ideal lemmas.
Blueprint searches for “finite splitting” and “localization maximal” found no matching
blueprint node; a broader polynomial search found no node stating this interface.
No change records are necessary: existing public signatures and visibility are preserved.

The required `deliver3.py --no-push` dry run printed OK: compilation and preflight pass,
with only the second reading intentionally deferred to the independent reader. Nothing
was pushed.

## Second reading by F2

1. Compared the delivered original module with the repository by `diff -u`.
   Its existing signature and docstring are byte for byte unchanged. Only its proof,
   three proof-only imports and a local heartbeat setting differ. No definition or
   existing interface changes, and no change record or forced adaptation is needed.
   Verdict: pass.
2. Independently compiled all three modules with `lcompile.py --all` (1.7, 2.6 and
   23.2 seconds), without warnings. A scratch copy printed the axioms of all three
   declarations: the generic localization helper uses only `propext`,
   `Classical.choice`, `Quot.sound`; the construction helper and original theorem also
   use `sorryAx`, exactly for the listed construction hole. There are no forbidden
   declarations or holed definitions. Existential data from the open construction
   theorem is eliminated only inside a theorem proof. Verdict: pass as decomposition.
3. Read both new statements and the construction docstring against
   [Stacks Tag 0334, Step 5](https://stacks.math.columbia.edu/tag/0334).
   The construction is strictly the residue-relation lifting and finite coefficient
   extension part; the localization and root-product conclusions are genuinely proved
   afterward. Tested the nonmaximal contraction case R a DVR, x inverse to a
   uniformizer: S is its fraction field and the residue relation can be lifted after
   inverting a denominator outside the zero ideal. Also checked field/degree-one,
   s=1 and repeated-root cases. No separability, perfectness, or maximality of m cap R
   is assumed. Independent LeanFinder search for a fractional monogenic algebra and
   lifted residue relation, Loogle `Polynomial.Monic, Polynomial.Splits`, and grep
   `exists.*splits|splittingField.*Finite|finite.*adjoin.*isIntegral` found useful
   splitting-field and polynomial lemmas but no complete construction. Local rg found
   only ancestors depending on this item, so using them would be circular. The remaining
   construction cannot be closed in a few minutes from those interfaces. Verdict: pass.
4. Read the proof top down: it uses the smaller construction, the fully proved generic
   localization lemma, and Mathlib root-factorization and finite-product identities.
   Public imports provide signature types; added target imports and generic-helper
   implementation imports are private. Every old direct proof dependency is now listed
   under No longer needed, with its retained indirect role explained. Checked
   dag/units/sk-thm-p1.json: none of these nodes realizes a unit statement or step, and
   its realized route is unchanged. No module is claimed globally pruned. Verdict: pass.
5. Compared the three nodes' Lean statement fields with their declarations, and their
   proof steps and proof_deps with the code and the Mathlib matches. New nodes have
   sources, searches, origin, creation, blueprint ancestry, chapter, unit and Lean
   records. Fixed spurious statement dependencies x, z and X caused by mathematical
   bracket notation, and rewrote that notation in the new node's prose to avoid
   treating variables as node citations. All remaining statement dependencies resolve.
   Verdict: pass after metadata repair.

Second reading changed only the new construction node's prose/dependency metadata and
completed the old-dependency accounting in this report. Lean proofs were retained.
One original hole closed, one smaller hole added: decomposition, net reduction zero.
