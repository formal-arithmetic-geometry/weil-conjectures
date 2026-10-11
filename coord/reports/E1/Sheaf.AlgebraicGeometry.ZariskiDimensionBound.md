## What changed

Proved `AlgebraicGeometry.isZero_zariskiCohomology_of_dimension_bound` by constructing
`AlgebraicGeometry.IsNoetherian X` from the existing `CompactSpace X` and
`IsLocallyNoetherian X` instances, then applying
`TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound`. Added the proof-only
import `Sheaf.Topology.NoetherianTopologicalCohomologyVanishing`. Updated the sandbox DAG
copy to record this direct route.

## Proved and sorry left

The local proof of `AlgebraicGeometry.isZero_zariskiCohomology_of_dimension_bound`
is closed (1 of 1 local sorries). No `sorry` remains in the delivered module, and no
new statement is split off. The theorem still depends on the existing open theorem
`TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound`
(node `lem-sc-noetherian-topological-cohomology-vanishing`); it is not yet proved
without `sorryAx`. The axiom check reports precisely `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`.

## No longer needed

The following five old `proof_deps` entries are removed as separate proof obligations:

- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`: replaced by Mathlib's
  `AlgebraicGeometry.IsNoetherian.noetherianSpace` instance.
- `def-kun-topological-krull-dimension`: the signature already uses Mathlib's
  `topologicalKrullDim`; no separate lemma is needed.
- `def-sc-zariski-site`: the signature already uses `Opens.grothendieckTopology X`.
- `def-sc-topological-abelian-cohomology`: both sides use the same `Sheaf.H'`.
- `def-sc-zariski-cohomology`: both sides use the same `Sheaf.H'`.

These definitions remain meaningful statement dependencies where appropriate; only
their separate proof-dependency entries are pruned. No existing import was removed,
and no separate Sheaf module for these five nodes was imported by the old file.
The only new import is private to the proof and is used by its final application.

## Where the brief, the DAG or earlier work was wrong

The planned proof was longer than necessary: the theorem assumptions already provide the
parents of `IsNoetherian`, and the Zariski site notation is definitionally the opens site.


## Second reading by E1

1. Compared the delivered module with the repository using `diff -u`. The existing
   theorem signature, universe, assumptions, conclusion, and docstrings are byte for
   byte unchanged. There are no definitions or other declarations changed. PASS.
2. Compiled through `lcompile.py`. There is no local `sorry`, prohibited declaration,
   or hollow definition. A scratch copy's `#print axioms` gives only `propext`,
   `Classical.choice`, `Quot.sound`, and the permitted `sorryAx` from the existing
   topological vanishing dependency. The Noetherian-space instance itself has only
   the three standard axioms. PASS, conditional on that documented open dependency.
3. No new statements or split-off nodes were introduced. The existing topological
   theorem applies to all spaces, not just schemes; this is a genuine specialization
   using Mathlib's proved Noetherian-space instance. Empty schemes and dimension zero
   introduce no additional assumptions: the same application works uniformly. PASS.
4. Read the imported theorem, Mathlib's class and instance, and searched Mathlib sites,
   topology, upstream `lean/WeilConjectures`, and `lean/Sheaf` by Noetherian/cohomology
   and dimension/vanishing terms. No shorter proved general vanishing result was found.
   The one added proof-only import is required. Existing public imports support the
   signature's schemes, opens, dimension, cohomology and inferred categorical instances.
   All five removed old proof dependencies are now explicitly listed above.
   `dag/units/sk-prop-sf-cbc.json` has empty realized statement and steps lists; this
   delivery preserves its record and the existing route through topological vanishing.
   PASS.
5. Compared both node versions: `proof`, `proof_deps`, and `proof_origin` describe the
   constructor plus the direct specialization actually used in Lean. No node statement
   or statement-dependency change is delivered, and there are no new nodes. PASS.

Changed `letI` to `let` to remove the Lean style warning. Expanded the report to name
all pruned dependency entries and to distinguish local closure from an axiom-free proof.
The mathematical proof was otherwise retained.
