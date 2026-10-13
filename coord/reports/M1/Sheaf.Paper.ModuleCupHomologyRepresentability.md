## What changed

Repaired the stale-base return for `Sheaf.Paper.ModuleCupHomologyRepresentability`.
The current server tree and freshly fetched delivery base contain neither the item
module nor its node: the N4 delivery that introduced them was withdrawn after a
red global build. Read its saved rollback patch in
`coord/repair-notes/Sheaf.Paper.ModuleCupEqualDerivedMapsClass.json` and restored the
item's original declarations and four public imports exactly. No other module from
that withdrawn delivery is restored or adapted.

Reapplied the proof using the concrete `cupHomologyEvaluation` linear map and
`LinearEquiv.ofBijective`. The equivalences are now constructed directly in the
structure literal. Functor composition proves naturality; cycles-map inclusion,
its injectivity, and homology-factorization naturality prove the cocycle formula.

Retained three supporting modules from the returned sandbox:
`Sheaf.Paper.ModuleCupHomologyFunctorLinear` (proved linearity),
`Sheaf.Paper.ModuleCupHomologyEvaluation` (explicit linear map), and
`Sheaf.Paper.ModuleCupHomologyEvaluationBijective` (the remaining hole).
The item imports the last module privately for its proof.

Since the original node is absent on the current base, restored it as an M1 node
with the real proof route, preserving its statement and source, and removed obsolete
N4 review stamps. Documented restoration of the public interface in
`coord/changes/cupHomologyRepresentability-restoration.md`. This is a restoration
against the current tree, not an unchanged rebase of the returned delivery.

## Proved and sorry left

Reduced the original withdrawn module's sole hole:
`AlgebraicGeometry.Scheme.Modules.exists_cupHomologyRepresentability`, node
`lem-sc-module-cup-homology-representability`. Its proof is complete from the
supporting statements. Also proved
`AlgebraicGeometry.Scheme.Modules.cupHomologyFunctor_linear`, and constructed
`AlgebraicGeometry.Scheme.Modules.cupHomologyEvaluation` without postponed proofs.

The sole remaining hole is
`AlgebraicGeometry.Scheme.Modules.cupHomologyEvaluation_bijective`, node
`lem-sc-module-cup-homology-evaluation-bijective`, in its own module, with its source
and full proof in its docstring. It asserts only bijectivity of the specified map;
linearity, naturality, normalization, and structure assembly are already proved.
No sorry remains in the item module and none occurs in any definition.

Relative to the withdrawn original, closed 1 and split off 1: a decomposition with
net 0, not a sorry-free proof of representability. Relative to the current fetched
base, the item and its original hole are absent, so this restoration adds one
supporting hole and does not claim a baseline hole closure. The ledger, rather than
these historical counts, determines progress in the targets' current closure.

## No longer needed

No original public import was removed. In particular, ShortComplex.ModuleCat
preserves the concrete module-homology API of the withdrawn original interface.
No project module is claimed pruned from the targets' closure.

The original direct dependency `def-weil-derived-category-cohomology-functor`
remains used. `lem-pc-ring-derived-map-representative` is needed only below the
bijectivity node, which imports Mathlib's KProjective module; it is no longer a
direct dependency of the item. The K-projective route is preserved.

The earlier sandbox-only splits `exists_cupHomologyEquivNatural` and
`cupHomologyEquivOnCycles` and their nodes remain removed. No new proof bypasses
any unit step. The unit `sk-prop-av-cube` and its realized fields are unchanged.

## Where the brief, the DAG or earlier work was wrong

The return describes a changed module, but the current base has subsequently lost
that module and its node in red-build recovery. Restoring the unchanged interface
therefore requires new-node ownership metadata and a public-interface change
record, as the first repair dry run explicitly reported. All four reported points
were repaired: created/group and lean.by are M1, the change record is supplied,
and the restored node is named below. No withdrawn review stamp is claimed valid
for this repair; the second reader must review the restored delivery afresh.

The first attempt's normalization of an arbitrary natural equivalence was false:
over the integers, negating a normalized natural equivalence preserves linearity,
bijectivity and naturality while negating the generator class. The replacement
constructs the canonical generator and evaluation map, and proves normalization
for that map. It leaves only the strictly smaller bijectivity claim. Zero rings,
zero cycles, every integer degree and unbounded targets are included.

The rollback's original global failure concerned duplicated instances in other
modules of N4's larger delivery. This delivery restores only the assigned module
and its three supporting modules, all using ModuleCat and Mathlib infrastructure;
it does not reintroduce those other instance-producing modules.

## New nodes

`lem-sc-module-cup-homology-representability` is restored because it is absent from
the current base. Its original statement, source and declaration signatures are
preserved; its proof and dependencies describe the delivered canonical-evaluation
reduction. Removed its old N4 review stamps and recorded M1 ownership.

`lem-sc-module-cup-homology-functor-linear` records proved linearity of derived
module homology by localization descent, in
`Sheaf.Paper.ModuleCupHomologyFunctorLinear`.

`def-sc-module-cup-homology-evaluation` records the explicit generator and linear
map in `Sheaf.Paper.ModuleCupHomologyEvaluation`. No data is chosen from an
unproved mere-existence theorem.

`lem-sc-module-cup-homology-evaluation-bijective` records the sole postponed proof,
in `Sheaf.Paper.ModuleCupHomologyEvaluationBijective`. Its K-projective localization
dependency is already a Mathlib/DAG declaration.

The three supporting nodes retain the real recorded searches from the returned
sandbox. The restored item's searches likewise retain their original actual
results. The change record is
`coord/changes/cupHomologyRepresentability-restoration.md`.

## Second reading by M1

1. Compared every delivered Lean module with the current repository tree. The item and its original node are absent from the fetched base, as documented in the restoration change record; the restored public declarations retain the reported signatures. Verdict: restoration is explicit and no accidental existing declaration change was found.

2. Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named theorem `cupHomologyEvaluation_bijective`, with its node and proof docstring. No forbidden declarations or hollow definitions occur.

3. Checked the split statement and node: `cupHomologyEvaluation_bijective` asserts exactly bijectivity of the concrete evaluation map and is strictly smaller than representability. Its source, proof sketch, imports, and DAG metadata agree; no duplicate declaration was found in the repository.

4. Read the proof top-down. Representability is assembled from `LinearEquiv.ofBijective`; naturality and the cocycle formula are proved directly. The canonical evaluation map is constructed explicitly. The unit route and realized fields are preserved, and no unnecessary project import was identified.

5. Checked the node Lean records and proof dependencies against the imports and proof. The restoration node and three supporting nodes carry M1 ownership and the recorded proof routes. The only change made in this reading is this section of the report; no Lean proof or statement required repair.
