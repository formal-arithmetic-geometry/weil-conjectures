## What changed

Proved `WeilConjectures.purityFiniteOpenIntervalDescent` with its full signature unchanged.
Only the assigned Lean module and DAG records change. Three proved private helpers
transport constructibility and zero detection through the existing constant-scalar
encoding. The fixed-module helper descends etale origin for a degree-zero sheaf using
an existing proved open-cover comparison theorem, descends etale constructibility,
and transports it back. Exact pullback commutes with homology. Fixed-interval support
is contained in the displayed finite integer interval; for differing local intervals,
global support lies in the finite union of local supports. The empty cover proves the
empty-scheme clause by homology conservativity.

New proof imports:

- `Sheaf.Paper.ProEtaleConstantModuleConstructibility`
- `Sheaf.Paper.ProEtaleConstantModulePullbackEncoding`
- `WeilConjectures.ConstructibleSheaf.OpenCover`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover`
- `Mathlib.AlgebraicGeometry.Noetherian`

Single-file lcompile passes without errors or warnings. Delivery preflight also compiles
with its axiom probe. No global build was run. The proof uses the existing fixed-module
constructible-origin theorem, whose source proof still has a sorry: this is a retained
stated dependency, not a new hole or an etale-origin hypothesis on F.

## Proved and sorry left

Closed 1 of 1 item holes: `WeilConjectures.purityFiniteOpenIntervalDescent`
(node `lem-pur-finite-open-interval-descent`). Added 0 holes; split off 0 holes.
No sorry remains in any delivered Lean declaration. The new node attaches existing
proved source theorems and adds no Lean module or declaration.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`
- `Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore`
- `Sheaf.Paper.ProEtaleFiniteModelStalks`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`
- `Sheaf.Paper.SfCommonStageWeilCohomology`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `Mathlib.Topology.Constructible`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Properties`

The assigned proof no longer directly needs these planned dependency nodes:

- `def-weil-constructible-subset`
- `def-weil-pbc-proetale-site`
- `def-weil-proetale-locally-constant-sheaf`
- `lem-cbc-proetale-stalk-conservative`
- `lem-exc-proetale-pullback-locally-constant`
- `lem-pe-constant-left-module-inverse-image`
- `lem-pur-proetale-inverse-image-stalk`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sfb-proetale-object-inverse-image-restriction`
- `lem-weil-pbc-affine-opens-basis`
- `lem-weil-pbc-etale-stratification-local-gluing-core`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-proetale-finite-model-stalks`
- `lem-weil-pbc-site-morphism-composition`
- `lem-weil-proetale-constant-sheaf-stalk`
- `lem-weil-proetale-weakly-etale-localization`

These are pruned from this item's proof route only; no module or declaration is
withdrawn. Some remain transitive dependencies of the coefficient-encoding and
constructible-origin theorems, so no claim is made that they leave the targets' import
closure. All corresponding obsolete tool_uses approvals are removed from this node;
the finite-type-over-Noetherian tool approval remains. The unit route is unchanged:
this is still the open-locality step needed by general admissibility.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The planned explicit finite affine refinement,
finite-stalk transport and global immersed refinement can be replaced below the unit
level by existing coefficient-encoding and etale open-locality theorems. The finite
union argument also handles empty J directly and avoids separate endpoint choices.
The original theorem docstring is preserved; the updated DAG records the actual proof.
New generic tool uses are the coefficient encoding, pullback and constructibility
comparisons, fixed-module constructible origin, etale open locality, and the existing
source open-cover comparison descent. Their use does not replace any unit statement.

## New nodes

`lem-pur-proetale-open-cover-comparison-descent` records the existing proved source
open-cover counit theorem and the two accompanying sheaf/derived zero-detection
lemmas in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover`.
It adds no statement, no proof hole, and no source-library change. Its primary Lean
statement is recorded verbatim with the source's inherited notation and variables.
No change record is needed: public signatures, definitions, attributes and imports
are unchanged, and all added helpers and imports are private to proofs.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
