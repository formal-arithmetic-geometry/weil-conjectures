## What changed

Proved `CategoryTheory.Abelian.SpectralObject.exists_pageTwoMap_data` in
`Sheaf.CategoryTheory.SpectralObjectPageTwoMapExistence`, preserving its statement.
Private helpers construct the maps on three-term complexes, cycles, opcycles and
homology. Their naturality equations prove compatibility with the page differential,
the successor-page homology isomorphism and the first-page comparison. The resulting
spectral-sequence morphism supplies the required witness explicitly.

Added the proof-only import
`import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence`: the canonical
homology-data construction has private proof constants in its dependent type. No
public import, existing signature, definition or consumer changed. The original
node's two-step proof plan and its dependencies remain accurate.

The conservative interface check flags the helper context commands. They are
documented in
`coord/changes/spectral-object-page-two-map-private-construction.md`; no existing
public declaration or consumer requires adaptation.

## Proved and sorry left

Closed the single hole in
`CategoryTheory.Abelian.SpectralObject.exists_pageTwoMap_data`
(node `lem-sp-spectral-object-page-two-map-existence`). One hole closed, zero holes
added, zero split off. No `sorry` remains in the delivered module; all private
helper declarations are fully proved or explicitly constructed.

## No longer needed

None. No original imports, nodes or modules were removed. The proof follows both
steps of the original node and uses the existing spectral-object and
spectral-sequence definitions; no additional statement modules are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The missing functoriality construction is
implemented directly from Mathlib's homology-map and kernel/cokernel APIs, including
the successor-page compatibility; no further split is necessary.

## Second reading by H4

1. **Statement preservation.** Compared the delivered module with the repository version. The
   signature of `CategoryTheory.Abelian.SpectralObject.exists_pageTwoMap_data` is byte-for-byte
   unchanged; no target or existing public declaration was weakened or given extra hypotheses.
   Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`. A scratch `#print
   axioms` reports only the permitted foundational axioms plus `sorryAx` inherited from still-open
   imported declarations. All private helper constructions are explicit and fully proved.
   Verdict: pass.

3. **Split statements.** No split-off theorem was added. The proof uses Mathlib's homology-map,
   kernel/image, and spectral-sequence APIs directly; searches and repository inspection found no
   existing declaration that supplies this construction. Verdict: pass; zero holes added.

4. **Pruning and route.** The proof follows both DAG steps: three-term-complex homology maps,
   then page differential/successor-page compatibility and the page-two comparison. The proof-only
   `import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence` is necessary because the
   canonical homology-data type contains private proof constants; no original import, node, or
   module became unused. Verdict: pass; nothing pruned.

5. **DAG agreement.** The existing node's statement, proof dependencies, and source remain
   accurate for the delivered proof. No new node or change to a target statement was needed. The
   unit route and realized steps are preserved. Verdict: pass.

Changed only the proof implementation and its required proof-only import; the existing change
record documents the scoped helper contexts flagged by the conservative interface check.
