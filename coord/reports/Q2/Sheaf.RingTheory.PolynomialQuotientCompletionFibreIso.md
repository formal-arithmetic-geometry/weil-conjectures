## What changed

Proved `Polynomial.exists_quotient_completion_fibre_iso` with its existing signature and
existing docstring unchanged. The proof uses canonical residue-field maps, completion
base change, tensor cancellation, and localization tensor comparison.

Added the proved module `Sheaf.RingTheory.CompletionSurjectiveBaseChange`, with theorem
`AdicCompletion.nonempty_surjective_baseChange`. This general theorem identifies the
completion of a prime localization after a surjective base change with the base change
of the original completion. It uses the already proved
`AdicCompletion.exists_local_completion_quotient` and Mathlib quotient/tensor equivalences.
Every added proof import is plain `import`; public imports serve statement vocabulary.

Removed the first worker's proposed `PolynomialQuotientResidueFieldIso` and
`PolynomialQuotientFibreRingIso` modules and their two new node files from this delivery.
They were unlanded additions, so no existing declaration was removed or changed.

## Proved and sorry left

Closed one existing hole: `Polynomial.exists_quotient_completion_fibre_iso`.
Added no holes. Also proved the new auxiliary declaration
`AdicCompletion.nonempty_surjective_baseChange`, recorded by
`lem-weil-pbc-completion-surjective-base-change`.

The first worker's proposed holes `Polynomial.exists_quotient_residueField_iso` and
`Polynomial.exists_quotient_fibre_ring_iso` are both removed, rather than delivered.
There is no `sorry` in either delivered module. This is a proof, not a decomposition.

## No longer needed

Removed the direct proof imports `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and
`Sheaf.RingTheory.LocalCompletionQuotient` from the item's module. The latter is retained
and used transitively through the new completion base-change helper; it is not pruned
from the target closure.

The old direct dependency `lem-weil-pbc-localization-prime-residue-field-iso`, and its module
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`, are no longer needed by this proof:
Mathlib's canonical residue-field maps and their bijectivity suffice. Whether this module
leaves the whole target closure depends on other users and is for the maintainer's ledger.

The other old direct dependencies `lem-weil-pbc-localization-at-prime-of-quotient` and
`lem-weil-pbc-local-completion-quotient` remain necessary through the new helper. The former
is a Mathlib node realized by the localization kernel calculation; the latter is applied
by its existing Lean declaration. The target node now names the helper as its direct
proof dependency, with those two nodes in the helper's proof dependencies.

Neither proposed auxiliary module is delivered. The exploratory proof import
`Mathlib.RingTheory.Polynomial.Quotient` was also removed because it was unnecessary.
No whole-library module-pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The first split's fibre statement required compatibility with an arbitrary residue-field
ring equivalence. The cited quotient/localization construction supplies compatibility
with the canonical equivalence only; the proposed proof did not justify its stronger
quantification. Its statement and docstring also left almost the entire completion-fibre
comparison as a hole. The residue-field split was unnecessary because Mathlib already
proves bijectivity of the canonical residue-field map for a map surjective on stalks.

The original DAG route is feasible using the existing proved completion quotient theorem.
`FormalFibreQuotientIso` already illustrates the required completion/tensor construction
for a prime quotient. The new helper generalizes that construction to any surjective
base map, without restating a completion-fibre theorem.

## New nodes

`lem-weil-pbc-completion-surjective-base-change` records the proved general completion
base-change theorem in `Sheaf.RingTheory.CompletionSurjectiveBaseChange`. It is strictly a
part of the target argument: it involves no residue fields, no localized prime `s`, and
no semilinear fibre comparison. Its proof uses the original localization-quotient and
local-completion-quotient nodes. LeanSearch was attempted but returned Internal Server Error. LeanFinder, Loogle and grep searches found the tensor
components and module-completion results but no duplicate prime-localization B-algebra
statement. Source statements were checked at [Stacks 00CT](https://stacks.math.columbia.edu/tag/00CT)
and [Stacks 00MA](https://stacks.math.columbia.edu/tag/00MA).

No statement or definition change records are needed.

## Second reading by Q2

1. Compared the delivered target module with the repository by `diff` and a byte-for-byte
   signature assertion. Its existing theorem signature and docstring are unchanged; there
   are no definition changes or forced adaptations. Verdict: pass.
2. Compiled both delivered modules in import order with the prescribed `lcompile.py`.
   Both compile without warnings, errors, or local holes. Scanned for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, and `extern`: none. Scratch `#print axioms` checks
   cover both delivered declarations; results are recorded below. No object is chosen
   from an unproved existence theorem: the completion quotient theorem used here is proved,
   and the residue-field isomorphisms are constructed from explicit maps and bijectivity.
   Verdict: pass.
3. No split-off holes remain. Checked the new general theorem at identity base change,
   field quotients, and nonmaximal primes: the localizations are local at the stated primes,
   surjectivity identifies the target with the kernel quotient, and the maximal ideals
   correspond. A zero target ring has no prime and so supplies no spurious case. Searched
   with different queries via LeanFinder, Loogle, grep and repository `rg`; reused the
   existing completion quotient theorem and Mathlib residue-field/tensor lemmas. Verdict: pass.
4. The target is opened and reduced by a real tensor argument rather than by a renamed
   copy of itself. The residue-field hole is eliminated directly by Mathlib, and the new
   completion helper is proved. The old dependencies retained transitively and the one
   removed dependency are all accounted for above. Read `dag/units/sk-thm-p1.json`:
   no changed node realizes a unit statement or step, and all `realized` entries and the
   curve-calculations route remain untouched. Verdict: pass.
5. Read the target and new node against the Lean: statements and `lean.statement` records
   agree; `proof`, `proof_deps`, and `proof_origin` describe the actual canonical map,
   quotient completion, and tensor constructions. The new node has its source, three
   search kinds, creation/blueprint/chapter/unit/Lean records and a complete argument.
   Verdict: pass.

Second reading changed: replaced the two proposed holed auxiliaries with a proved general
completion base-change lemma and an explicit canonical residue-field/tensor proof of the
unchanged target; corrected and completed dependency records, pruning report, and hole count.

Axiom check results: `#print axioms AdicCompletion.nonempty_surjective_baseChange` and
`#print axioms Polynomial.exists_quotient_completion_fibre_iso` both report exactly
`[propext, Classical.choice, Quot.sound]`; neither depends on `sorryAx`.
