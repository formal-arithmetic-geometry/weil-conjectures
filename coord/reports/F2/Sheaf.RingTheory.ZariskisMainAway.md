## What changed

Proved `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` in
`Sheaf.RingTheory.ZariskisMainAway`, with its signature and visibility unchanged.
The fibre-spectrum homeomorphism transports the hypothesis to Mathlib's
`quasiFiniteAt_iff_isOpen_singleton_fiber`. Mathlib's proved
`ZariskisMainProperty.of_finiteType` then gives exactly the requested conclusion.
Removed five unused proof imports and updated the node's proof route. Retained both
public imports, which supply the existing statement's definitions. No interface changes.

## Proved and sorry left

Closed: `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`
(node `lem-weil-pbc-integral-closure-zariski-main-away`). One original hole closed;
zero new holes; no `sorry` remains in the delivered Lean module. This is a proof,
not a decomposition. The single-file compile passes without warnings. The delivery axiom probe passes. The independent second reading also compiled a
scratch copy with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed proof imports:

- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePermanence`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization`
- `Sheaf.RingTheory.QuasiFiniteFourRings`
- `Sheaf.RingTheory.QuasiFiniteMonogenicIntegralClosure`

The following former proof-dependency nodes are no longer needed by this proof:

- `def-weil-finitely-generated-module`
- `lem-weil-pbc-finite-of-integral-generators`
- `lem-weil-pbc-finite-algebra-is-integral`
- `lem-weil-pbc-integral-transitive`
- `lem-weil-pbc-quasi-finite-at-prime-permanence`
- `def-weil-polynomial-ring`
- `lem-weil-pbc-conductor-radical-coefficients`
- `def-weil-pbc-strongly-transcendental`
- `lem-weil-pbc-reduced-strongly-transcendental-not-quasi-finite`
- `lem-weil-pbc-quasi-finite-four-rings`
- `lem-weil-pbc-quasi-finite-at-prime-principal-localization`
- `lem-weil-pbc-quasi-finite-monogenic-integral-closure`

These are removals from this item's route; some may remain reachable through other modules.
Mathlib itself already proves the conductor and polynomial induction argument, so no
unproved Sheaf version of those intermediate lemmas is used. No node realizing the
unit's own statement or proof steps is bypassed: this item is below that level in
`sk-thm-p1`, whose `realized` lists were checked.

## Where the brief, the DAG or earlier work was wrong

The planned inductive proof is mathematically appropriate, but unnecessary here:
Mathlib already proves precisely its conclusion. The only bridge needed is openness
through the canonical fibre homeomorphism, and that bridge is proved in this module.
The initial attempt to use the residue-field route ran into a contraction `LiesOver`
instance; using Mathlib's topological equivalence avoids that extra bookkeeping.
No statement error was found, and no signatures or definitions were changed.

Searches actually run through `msearch.py`: LeanFinder for the finite-type quasi-finite
integral-closure localization statement (found `ZariskisMainProperty`); Loogle for
`Algebra.ZariskisMainProperty.of_finiteType` (exact match); grep for the singleton-fibre
and residue-field bridges (found the topological equivalence). Also read the full
pinned Mathlib theorem module and the project definition of `IsQuasiFiniteAtPrime`.


## Second reading by F2

1. **Visible declarations: PASS.** Compared the complete Lean and node diffs with
   the repository. The sole existing theorem's signature, universe parameters,
   visibility and both public imports are byte-for-byte unchanged. Only its proof,
   proof docstring, five private proof imports, and the node's `proof`, `proof_deps`,
   `proof_origin` fields changed. No definition or statement changed; no change
   record is required.
2. **Proof and axioms: PASS.** Independently compiled the delivered module through
   `lcompile.py`, without errors or warnings. Compiled a scratch copy with
   `#print axioms Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Read the entire
   proof and the definition of `IsQuasiFiniteAtPrime`; the image-singleton rewrite
   transports precisely its canonical fibre point. No `sorry`, forbidden declaration,
   or data chosen from an unproved existence statement occurs.
3. **Split statements: PASS (none).** There are no new statements, new nodes or
   split-off holes. The only hole closed is the original theorem; none was added.
   The existing prime hypothesis excludes the zero target ring; no nontriviality,
   injectivity or domain hypothesis was silently added.
4. **Shortest route and pruning: PASS.** Read the pinned Mathlib definition of
   `ZariskisMainProperty`, `ZariskisMainProperty.of_finiteType`, and both singleton
   fibre lemmas. The conclusion is definitionally the requested bijective awayMap.
   Independently searched `lean/Sheaf` and `lean/WeilConjectures` for
   `preimageHomeomorphFiber` and `isOpen_singleton_fiber`; no shorter project bridge
   was needed. Both retained public imports serve the existing signature. Checked
   the full old/new `proof_deps` set difference: all twelve removed nodes and all
   five removed proof imports are reported above. Read `dag/units/sk-thm-p1.json`:
   neither this node nor any removed dependency realizes its statement or steps.
   The unit and chapter route remain intact.
5. **DAG agreement: PASS.** The two recorded proof steps follow the Lean proof:
   transport singleton openness to obtain `QuasiFiniteAt R q`, then apply Mathlib's
   finite-type Zariski main theorem. Their uses have union exactly `proof_deps`;
   `proof_origin` names the actual Mathlib declarations and the homeomorphism.
   The node statement, source, Lean signature record, chapter and unit are unchanged.

Second reading changed only this report: added the independent checks and replaced
its pending-review validation sentence. No Lean or DAG repair was needed.
