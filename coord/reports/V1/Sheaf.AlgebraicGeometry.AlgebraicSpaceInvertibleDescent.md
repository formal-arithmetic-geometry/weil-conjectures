## What changed

Replaced the sole sorry in
`AlgebraicGeometry.AlgebraicSpace.exists_lineModule_of_etale_descent` with a complete
assembly proof, preserving its signature and `InvertibleAtlasDescentDatum` verbatim.
Only the item module, two new theorem modules, their new nodes and the item node change.
No existing shared module, public import, definition or instance changes.

The private lemma `atlas_coversTop` constructs the covering sieve from the precise
scheme-test joint-surjectivity assumption, including the representing Yoneda maps
and the etaleness of all necessary scheme projections. The private lemma
`atlas_hom_descent` works over an arbitrary ringed site and proves existence and
uniqueness of descended maps for arbitrary module sheaves, without assuming either
is a line module. Keeping the ring sheaf abstract avoids costly unfolding of the
algebraic-space structure-ring implementation during the scalar-linearity check. It glues additive maps
using Mathlib's sheaf Hom and CoversTop APIs, proves scalar-linearity by separatedness,
and checks both the prescribed local restrictions and uniqueness.

For object descent, the first new theorem supplies a module with the specified
ordinary identifications and transition equations, without any covering or line-module
conclusion. The second supplies local frames from a single ordinary identification,
without any atlas or overlap datum. The item composes their covering sieves using
`GrothendieckTopology.bind_covering`, proving the actual `IsLineModule` condition.
Both split statements are strict parts of the original argument. Neither is the
original theorem under a different name, and the covering and morphism arguments
are complete Lean proofs in the item.

All new holes are standalone public theorems, each in its own module with a source,
complete natural-language proof and DAG node. No data is chosen into a definition
from an unproved mere-existence theorem. No new definitions or axioms are added.

## Proved and sorry left

Original hole closed:

- `AlgebraicGeometry.AlgebraicSpace.exists_lineModule_of_etale_descent`
  (`lem-trf-algebraic-space-invertible-descent`): complete proof from the two
  strictly narrower statements below. Its morphism-descent conjunct and covering
  composition are proved without any new sorry.

New holes, exactly two:

- `AlgebraicGeometry.AlgebraicSpace.exists_ordinary_atlas_tuple_realization`,
  in `Sheaf.AlgebraicGeometry.OrdinaryAtlasTupleRealization`, node
  `lem-trf-ordinary-atlas-tuple-realization`. This is ordinary tensor-section
  realization and graph evaluation, with u-small section values, no joint
  surjectivity and no assertion that the resulting module is locally free.
- `AlgebraicGeometry.AlgebraicSpace.ordinary_etale_identification_local_frames`,
  in `Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentificationLocalFrames`, node
  `lem-trf-ordinary-etale-identification-local-frames`. This is the local
  comparison of a single ordinary invertible module with its localized module
  sheaf, not effective descent or gluing.

There are zero sorries in the delivered item module. The packet closes one original
hole and adds two, so this is a decomposition, not a net reduction or a fully
sorry-free proof. The existing tuple and scheme-comparison dependencies retain
precisely the proofs and holes already present in the shared library.

Validation: `lcompile.py --all` compiled the two new modules in 3.9 s and 2.8 s.
After the final repairs, `lcompile.py` compiled the item cleanly in 9.2 s. Every
file is below the 60-second limit; final probe results are recorded by the delivery
tool. Existing public signatures are unchanged. The
new statements were checked on empty schemes, the empty atlas, a noncovering atlas,
and self-overlaps with distinct lifts: the tuple realization uses zero for an empty
family; local frames assert nothing outside the given chart; the item uses the
covering hypothesis only to cover each test scheme; no off-diagonal identity is
assumed for a self-overlap.

## No longer needed

Removed proof-only imports from the item:
`Mathlib.CategoryTheory.Sites.Limits`, `Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison`.
The first three are unnecessary direct imports for this proof; the algebraic-space
public interface already supplies the site and module API. The scheme comparison
is needed only in the planned proofs of the new realization/local-frame items.
The replacement imports are the two new statement modules, Mathlib SheafHom and
CoversTop.Basic, and AlgebraicSpaceRepresentableEtaleSchemeTests.

The old direct proof dependencies
`lem-trf-scheme-etale-invertible-comparison`,
`lem-trf-space-etale-module-tuple-sheaf`, and
`lem-trf-space-etale-tuple-graph-isomorphisms` move below the new statements;
they are not claimed to be mathematically pruned. The item no longer directly
uses `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, so its obsolete item-level
`tool_uses` approval is removed. Its role in the tuple construction remains.
The size convention and ordinary-invertibility definition are encoded by the
unchanged universes and hypotheses rather than separate proof invocations.
No existing module is withdrawn and no whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and the unit route are retained. The typed tuple and
graph lemmas do not directly specialize to this item: their local modules have
section universe `max (u + 1) v`, whereas `F.Modules` and the ordinary
identifications in this item have section universe `u`. This is an interface gap,
not a reason to change the item's statement or to assume the space is a scheme.
The new realization statement isolates the missing ordinary-to-localized,
u-small construction. Its proof plan uses the existing tuple and graph
construction, with u-small indexed products instead of raising the section universe.

The previous DAG's full-faithfulness step can be proved directly with Mathlib's
`Presheaf.IsSheaf.hom`,
`Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section`, and
`presheafHomSectionsEquiv`. There is no need to split another morphism-gluing
hole or assume ordinary-to-etale equivalence for this conjunct: its hypotheses
already give maps in the correct localized module categories.

Searches: LeanFinder for module-sheaf descent; Loogle for
`"SheafOfModules", "over"` (12 localization/adjunction hits); LeanSearch for
ordinary-identification local frames (8 foundational module/free-sheaf hits);
and msearch grep plus rg of Mathlib, WeilConjectures and Sheaf. No direct theorem
was found for either new statement. Blueprint search for local frames found no
hit; compatible tuples found one unrelated open-curve residue-sequence node.
The existing tuple and graph nodes were read in full and remain in the proof plan.
The inherited unit has no realization entry for this auxiliary descent node;
its statement and route are unchanged. No source-library declaration is edited.

## New nodes

`lem-trf-ordinary-atlas-tuple-realization`, in
`dag/nodes/sec-trace-formula/lem-trf-ordinary-atlas-tuple-realization.json`, realizes
old argument steps 1 through 6: ordinary localized section modules, the actual
compatible-tuple module and its graph identifications. Its statement does not
assume a cover and does not assert a line module or morphism descent.

`lem-trf-ordinary-etale-identification-local-frames`, in
`dag/nodes/sec-trace-formula/lem-trf-ordinary-etale-identification-local-frames.json`,
is the single-chart local-frame part of old step 7. The item itself proves
covering composition across the atlas. Both nodes inherit the item's chapter,
unit and blueprint ancestor, record three kinds of library searches and give
verbatim Lean statements and source-based proof plans. No change record is
required because no existing interface changes.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
