## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectLocalDegreeZeroUnit.lean` from its
quarantine archive under the current rework assignment. Replaced its withdrawn
public `Sheaf.AlgebraicGeometry.DerivedPullback` import with the adopted
`WeilConjectures.AlgebraicGeometry.DerivedPullback`. Added the explicit additive
instance for sheaf evaluation, inferred through `SheafOfModules.forget` composed
with `PresheafOfModules.evaluation`, so the negative-fibre zero-object argument
elaborates with the current API. The theorem signature and all three proof
dependencies are preserved. Updated only the node's proof provenance.

The proof derives zero negative Betti numbers, obtains the rank-minimal finite
free affine representative, proves its negative terms zero and its degree-zero
term rank one, and applies the existing fixed-model stalk theorem. The unit's
route is unchanged. The zero-rank free term uses the empty generator type; the
rank-one conclusion uses the actual residue isomorphism, so no nonvanishing or
extra fibre hypotheses are introduced.

`lcompile.py` compiled the restored theorem without errors or warnings. Current
source copies of its three dependencies were compiled unchanged in the sandbox
to avoid the published build's mixed old/new `PerfectComplex` imports; these copies
are byte-identical to the repository and introduce no delivery changes.

Change record: `coord/changes/perfect-local-degree-zero-unit-restore-N3.md`.

## Proved and sorry left

The restored complete theorem is
`AlgebraicGeometry.surjective_stalk_homology_of_perfect_local_unit`, attached to
`lem-sc-perfect-local-degree-zero-unit`. This is a zero-hole quarantine repair:
the archived source already had a complete proof. Holes closed: 0 of 0. Holes
added: 0. Holes left in the item: 0. No statements were split off and no new
nodes were created. Imported dependencies retain their existing proofs.

## No longer needed

Removed the empty withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback` import and
replaced it by its canonical adopted module. No mathematical node or module is
pruned: the three declared proof dependencies
`lem-sc-perfect-finite-free-residue-model`, `lem-sc-derived-residue-unit-betti`,
and `lem-sc-connective-rank-one-model-stalk` are all used. The Lean attachment and
the dependency from the quarantined proper-flat stalk-surjectivity parent remain.

## Where the brief, the DAG or earlier work was wrong

The module is an assigned zero-hole restoration repair, rather than a currently
present module with a local `sorry`. The rework archive supplies the complete
proof. The archive's old derived-pullback import has since been withdrawn, and
current evaluation additivity must be supplied through its defining composite.

The first compile also exposed mixed published artifacts: importing the current
finite-free model with the published fixed-model stalk theorem duplicated
`Scheme.IsPerfect` from the old `Sheaf.PerfectComplex` and adopted
`WeilConjectures.PerfectComplex`. Recompiling the unchanged current dependency
sources removes that conflict. No source signatures or source-library bodies
were changed to address it.

Searches run in this session: LeanFinder for the local residue-unit stalk
criterion returned only ordinary residue/stalk surjectivity results; Loogle
confirmed `Module.finrank_zero_of_subsingleton`; msearch grep found that dimension
lemma and no perfect-complex stalk criterion. Local `rg` confirmed that the three
existing declarations provide precisely the planned argument. Sources read:
Stacks `perfect.tex`, `lemma-proper-flat-h0` (0E62), and `more-algebra.tex`,
`lemma-lift-perfect-from-residue-field` (0BCD).

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
