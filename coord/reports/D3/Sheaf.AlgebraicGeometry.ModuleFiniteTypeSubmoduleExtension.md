## What changed

Closed `AlgebraicGeometry.Scheme.Modules.exists_quasicoherent_finiteType_submodule_extension`
without changing its signature or public imports. Extend the prescribed map by
`exists_quasiCoherent_extension_of_quasiCompact_open`, approximate its source, then
use the quasi-coherent finite-type image and the abelian image factorization.
The restriction isomorphism and its compatibility with the inclusion are constructed in Lean.

Added `Sheaf.AlgebraicGeometry.ModuleFiniteTypeApproximation`, whose theorem
`exists_finiteType_global_approximation` is proved by induction over a finite affine cover.
Its proved private helpers handle compact finite unions, restriction of isomorphisms to
smaller opens, and descent of finite local generators from the top slice site.
Added `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineEnlargement` for the remaining
single-affine finite-generation and gluing step. Updated the three DAG records.
The unit `sk-thm-p1` realized statements and steps are not bypassed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_quasicoherent_finiteType_submodule_extension`
(node `lem-weil-pbc-module-finite-type-submodule-extension`), 1 of 1 original holes.
Also proved: `AlgebraicGeometry.Scheme.Modules.exists_finiteType_global_approximation`
(node `lem-weil-pbc-module-finite-type-global-approximation`); all its private helpers are proved.

Hole added and the only sorry in the delivery:
`AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_enlargement`
(node `lem-weil-pbc-module-finite-type-affine-enlargement`). Its docstring gives the complete
single-affine argument. This is a decomposition (one upper hole closed, one smaller hole
added), not a claim of a sorry-free target. The existing quasi-coherent extension theorem
is still an imported hole; its module is not modified. The image theorems are already proved.

The new hole is strictly local: it assumes only a quasi-separated scheme and a single
added affine open, starts from an already global module, and claims finite type only on
W union V. It does not state the assigned theorem under another name. The finite-cover
induction, initial extension, finite-type transport, and image compatibility are proved.
Edge cases checked mathematically: W empty (zero submodule), V contained in W
(take H), empty scheme, zero H, and non-quasi-compact X. The latter is allowed because
only the compact union needs extension; no global finite-type conclusion is made there.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
from the assigned module. Its node `lem-weil-pbc-quasi-coherent-finite-type-affine` remains
needed by the single-affine enlargement theorem and is imported there, so this does not
prune that module from the transitive closure.

Pruned the spectral detour: `lem-weil-pbc-qcqs-scheme-spectral` and
`def-weil-spectral-space` are not proof dependencies of any delivered theorem.
QuasiSeparatedSpace directly supplies compact intersections of compact opens.
The affine basis and affine compactness are used by the proved approximation theorem.
The tilde/global-sections adjunction, tilde sections, principal localization,
finite-type affine criterion, restriction, and quasi-coherence/finite-type definitions
remain needed in the affine step. No additional Sheaf module is claimed globally pruned.
The ideal-sheaf-only modules `WeilConjectures.Compactification.FiniteTypeExtension` and
`WeilConjectures.Compactification.FiniteTypeDirected` were searched and not imported.

The complete list removed from the assigned node's old direct `proof_deps` is:
`lem-weil-pbc-affine-opens-basis`, `def-weil-pbc-quasi-compact-scheme`,
`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-qcqs-scheme-spectral`,
`def-weil-spectral-space`, `def-weil-affine-spectrum`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, `lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-principal-localization-open-immersion`,
`lem-weil-pbc-quasi-coherent-finite-type-affine`, and `pqf-def-coherent`.
The affine-cover dependencies move into approximation; the affine module and local
properties dependencies move into affine enlargement. The spectral detour is unused.
`def-weil-affine-spectrum` is supplied by Mathlib's affine-open/tilde infrastructure,
not invoked as a separate project declaration. Removed direct dependencies do not
by themselves imply that their modules leave the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The DAG's use of spectrality is unnecessary: the given
quasi-separatedness already proves compactness of the intersections. The library's
complete 01PF proof for IdealSheafData does not cover arbitrary O_X-modules.
The original source outline remains valid; its one-affine part is now isolated, and
its finite-cover induction is actual Lean. Source checked against Stacks Tag 01PF,
https://stacks.math.columbia.edu/tag/01PF, including its reduction to one affine open.

## New nodes

`lem-weil-pbc-module-finite-type-global-approximation`, in
`dag/nodes/sec-proper-base-change/`, records the proved finite-cover induction.
It imports the next node and has no sorry of its own.

`lem-weil-pbc-module-finite-type-affine-enlargement`, in the same directory, records
steps 2--6 of the source proof specialized to an already global H, followed by 01PE(3)
and image to realize a global subsheaf. This is the single remaining item. Both new
nodes have logged leanfinder, loogle and grep searches; their required LeanSearch
queries returned HTTP 500 and are recorded as unavailable, not as no match; blueprint searches found no
arbitrary-module approximation/enlargement match (ideal-only nodes were excluded).
No signatures, definitions, held modules, or targets were adapted; no change record is needed.

The resumed worker recompiled all three modules successfully, checked the remaining
affine-enlargement statement against Tags 01PF and 01PE, and updated the assigned
theorem's docstring to match its actual extension/approximation/image proof.

## Second reading by D3

1. Interface check: PASS. Compared the assigned module and node against the
repository versions. The existing theorem signature is byte for byte unchanged;
all existing public imports and visibility are unchanged. No definitions or target
statements change, and no forced adaptation or change record is needed. The two
new modules contain one public theorem each and only proved private helpers.

2. Proof and axioms check: PASS as a decomposition. All three delivered modules
compile locally in import order (5.6, 27.7, and 25.8 seconds). Independently compiled
scratch copies with `#print axioms` for each public theorem: each reports only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected
from the named remaining affine-enlargement hole and imported open theorems.
The delivered sources contain exactly one `sorry`, in
`exists_finiteType_affine_enlargement`; no forbidden declarations and no hollow
definitions occur. Existential witnesses are destructured inside theorem proofs;
no public object is defined by arbitrary choice from an unproved existence theorem.
Read the local-generator transport, finite-cover induction, restriction equivalence,
and image factorization and inclusion-compatibility cancellation individually.

3. Split-off check: PASS. The affine-enlargement lemma is strictly one local step:
it starts from an already global H, adds one affine V, and asks for finite type
only on W union V. It does not restate the assigned arbitrary-submodule extension.
Its docstring explains the finite principal cover, numerator submodule, overlap
isomorphism, gluing, and 01PE extension followed by image. Checked these against
Stacks Tags 01PF and 01PE directly (the literature TeX is absent on this machine):
https://stacks.math.columbia.edu/tag/01PF and
https://stacks.math.columbia.edu/tag/01PE.
Small cases: for V contained in W take H; for W empty take zero; zero H and empty
X also admit zero. For non-quasi-compact X the union remains quasi-compact and
quasi-separatedness makes its open immersion quasi-compact; the lemma imposes no
finite-type condition outside that union. New independent leanfinder query:
"quasi coherent subsheaf generated by finitely many sections agreeing on a compact
open subset"; loogle query `SheafOfModules.GeneratingSections`; grep query
`exists.*(subsheaf|submodule)|finiteType.*(union|sup)`, plus source searches in
lean/Sheaf and lean/WeilConjectures. Candidates concern local generators or
structure-sheaf sections, or IdealSheafData only. None supplies the arbitrary-module
step. This hole requires substantial affine/gluing formalization and has no quick
closure from the available candidates.

4. Route and pruning check: PASS after reporting repair. The proof proceeds from
the assigned theorem through the existing quasi-coherent extension and image
results, with a proved finite-cover reduction to the one-affine hole. Read the
unit sk-thm-p1 `realized` statement and all four steps: none is bypassed. Imports
needed only for proofs are plain imports; statement infrastructure remains public.
The only removed assigned-module import is QuasicoherentFiniteTypeAffine, retained
below in affine enlargement. Completed the explicit list of every removed old
direct proof dependency under No longer needed, distinguishing moved dependencies
from the unused spectral detour. No whole-library module pruning is asserted.

5. DAG agreement: PASS after metadata repair. Each node's proof-dependency list is
exactly the union of its proof steps' uses. The new nodes have source, complete
proof plans, searches, created/blueprint/chapter/unit fields, and exact verbatim
Lean statements. The existing node's Lean statement differed only in whitespace;
updated it to the exact unchanged multiline Lean signature. Its mathematical
statement is unchanged and its proof records the extension/approximation/image
route actually used.

Second-reading changes: completed the No longer needed dependency list, synchronized
the existing node's lean.statement formatting, and added this independent review.
No Lean proof or signature required repair. Net delivered hole change is zero:
one original hole closed and one strictly smaller hole added; this is decomposition.
