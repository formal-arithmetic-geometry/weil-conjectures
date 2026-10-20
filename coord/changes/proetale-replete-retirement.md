# AlgebraicGeometry.Scheme.isReplete_proEtale

## Reason

Retirement assignment in coord/retire-items.tsv and coord/queue.tsv, following
coord/changes/retire-sheaf-twins-20261020.md. The assigned Sheaf module already
has zero holes. Its adopted source twin proves precisely the same theorem.
Retire the duplicate and retain the actual mathematical result, rather than
withdrawing the result because its current consumers are quarantined.

## Old

Module: Sheaf.AlgebraicGeometry.ProEtaleReplete.

```lean
theorem isReplete_proEtale (X : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology.IsReplete.{u + 1, u, w} (ProEt.topology X)
```

The node det-pe-replete-epimorphism points to that module. The three archived
consumers listed below have this private proof import:

```lean
import Sheaf.AlgebraicGeometry.ProEtaleReplete
```

## New

Retain the adopted theorem verbatim in
WeilConjectures.AlgebraicGeometry.ProEtaleReplete:

```lean
theorem isReplete_proEtale (X : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology.IsReplete.{u + 1, u, w} (ProEt.topology X)
```

Withdraw lean/Sheaf/AlgebraicGeometry/ProEtaleReplete.lean via deleted.txt.
Reattach det-pe-replete-epimorphism to the source theorem, with its mathematical
statement and dependencies retained. The proof uses the source affine covering
theorem, weak contractibility, sectionwise sequential lifting, and image-sieve
downward closure. It retains both steps of unit sk-prop-pe-replete.

There are no current Lean importers: tools/downstream.py reports zero, and
searching both library roots confirms this. The three old consumers are absent
from lean/ and preserved under quarantine/, as coord/rework.tsv records. Their
archives and attachments are preserved. On restoration, each must replace the
private import above with:

```lean
import WeilConjectures.AlgebraicGeometry.ProEtaleReplete
```

They contain no occurrence of isReplete_proEtale, IsSiteForCoverings, or
exists_wContractible_affine_cover; their unfinished proofs have not used those
interfaces yet. This packet neither restores those unrelated quarantined
clusters nor treats their absence as authorization to withdraw their results.
The source theorem is the actual replacement of the retired duplicate.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedTateRealization | unclaimed; quarantined | No active importer; replace private import on restoration. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed; quarantined | No active importer; replace private import on restoration. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed; quarantined | No active importer; replace private import on restoration. |

No active module is adapted. No definition, target, source declaration, source
attribute, or source public import changes. The current source module's project import
traversal, stopping at Mathlib leaves, visits 225 project modules, zero Sheaf
modules, and no missing project modules.
Its complete proof and exact theorem type compiled through lcompile.py in
1.5 seconds; #print axioms reports only propext, Classical.choice, and Quot.sound.

For the return of head 13030976d9, revalidated this retirement against current
sheaf-dag a151094fa9, including the live source proof, DAG parents, retirement
assignment and quarantine rows. The missing ScalarExtCupInverseImage path in the
failed landing belongs to a separate quarantined rework item and is absent from
this theorem's project dependency closure. Its archive remains untouched. The
resubmission is rebuilt by deliver3.py on freshly fetched sheaf-dag.

## Status

landed 20261020T154936-L-3174297 2026-10-20 (merge of deliver/E8/Sheaf.AlgebraicGeometry.ProEtaleReplete)
