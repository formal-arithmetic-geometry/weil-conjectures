## What changed

Repair of returned head e47c86c6c2c (reviewer C-e47c8). The mathematical
review passed; landing rejected the reviewer-side change-record fix filename.
The corrected packet documents the exact .change.md fix alias in the change
record, includes that record directly, and refreshes its consumer table for
the current source, including SystemTensorShiftCoherence. The delivery tool
rebases the retained work onto the current sheaf-dag before checking and pushing.

Replaced the single sorry in
WeilConjectures.DiagramPullbackShift.diagramPullbackMonoidalShiftModels with a
complete Lean assembly of simultaneous models and all nine coherence fields.
The unchanged presentation definitions move to the publicly reexported
Sheaf.SixFunctors.DiagramPullbackShiftData to permit acyclic imports of three
strictly smaller proof obligations. No existing definition body or theorem
statement changes; no source-library file is edited.

The main module directly proves finite simultaneous K-flat resolutions, chain
signed coherence, the two unsigned action-unitor summand formulas, both termwise
compositor formulas, both derived compositor shift compatibilities, and equality
shift compatibility. Its new proof imports expose no new public hypotheses.

Change record: coord/changes/F7-diagram-pullback-shift-interface-extraction.md.

## Proved and sorry left

Original holes: 1. Original hole closed by decomposition:
WeilConjectures.DiagramPullbackShift.diagramPullbackMonoidalShiftModels,
node lem-pur-diagram-pullback-monoidal-shift-models.

Three holes added, each a public theorem with source, full proof in words and node:

- WeilConjectures.DiagramPullbackShift.diagramTensorShiftConstraints,
  node lem-pur-diagram-tensor-shift-constraints: normalized constraints and intrinsic
  tensor shift laws at one scheme, without geometric inverse images.
- WeilConjectures.DiagramPullbackShift.diagramGeometricTensorPresentations,
  node lem-pur-diagram-geometric-tensor-presentations: geometric model and normalized
  tensor-comparison existence, without any Models.Coherence conclusion.
- WeilConjectures.DiagramPullbackShift.diagramTensorPullbackShiftDescent,
  node lem-pur-diagram-tensor-pullback-shift-descent: only the chain and derived
  pullback/tensor shift squares for given presentations and constraints.

This is a decomposition, not a net hole reduction (1 closed, 3 added). The item
module itself has zero remaining sorry. The extracted definition module has zero.
The six direct private helpers are fully proved. There are no sorry fields of
any definition, no new axioms, and no data construction chosen from a merely
existential unproved theorem. The existential selections are local to the main
proposition proof. All five delivered modules compile through lcompile.py.
Repair validation: the fresh five-module import-order compile passed, including
the final assembly in 57.5 seconds. The data module and all three split
statements also returned compiled status; there were no compiler messages.
The final delivery reruns the mechanical packet preflight against its freshly
fetched sheaf-dag base before pushing.

## No longer needed

No mathematical dependency is pruned. The original approved tool dependencies
remain needed either directly or in the three subordinate arguments. In particular
RingedTopoiCanonicalTensorPullbackOfUniverses is no longer a direct proof import
of the main file, but its theorem remains a proof dependency of geometric
presentation and pullback shift descent, so that module is not claimed pruned.
All six original public imports live unchanged in DiagramPullbackShiftData and
are publicly reexported. The direct Mathlib proof imports ExactFunctor and
BifunctorShift are supplied by that public interface and the exact-functor shift
proof import. KFlatResolutionIndependentCoefficients remains a direct proof import.
TensorColimitsIndependentCoefficients is a new direct proof import for its proved
siteSheafTensorRightIso, used to convert the resolution theorem's flatness
conclusion to IsFlatOnSite. Its existing node
lem-weil-pbc-independent-sheaf-tensor-colimits is recorded in the assembly proof.

The main node now cites only the dependencies the assembly and direct helper
proofs use. The remaining former parent proof dependencies occur in the new
nodes at the steps that use them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The return was a packet filename error: --apply-fixes accepts
F7-diagram-pullback-shift-interface-extraction.change.md, while the failed
merge passed F7-diagram-pullback-shift-interface-extraction.md. No Lean
compiler failure was recorded. The record now states both its repository path
and its supported reviewer-fix filename.

Compared with current source, all 26 original signatures and all 25
non-theorem bodies are preserved. The refreshed downstream list contains
BasicSystemShiftResolutionCalculus, BasicRealizationShiftSquare and
SystemTensorShiftCoherence; none requires adaptation.

No mathematical statement error was found. The existence theorem originally
bundled several long subarguments whose named dependencies provide ingredients
but do not directly construct the full geometric presentation or its normalized
derived coherence. The delivery makes those residual arguments explicit while
proving the remaining fields directly. The interface extraction is required by
the module import graph. Unit and chapter routes remain unchanged.

Edge checks: Fin 0 requires no inputs; the resolution choice argument remains
valid. Zero rings and zero complexes use the same definitions. Negative and
zero shifts obey the integer bifunctor laws; the symmetry parity difference is
2bp for all integers. Arbitrary coefficient maps, including quotient maps,
are kept on the whole system site. The geometric presentation lemma prescribes
only its constraints field and does not assume or conclude the original full
coherence theorem. The descent lemma assumes given presentations and omits
all existence, compositor and intrinsic tensor-coherence assertions.

## New nodes

- def-pur-diagram-pullback-shift-data records only the unchanged interface moved
  to the data module, including all existing declarations from rings to
  Models.Coherence. It has no proof hole.
- lem-pur-diagram-tensor-shift-constraints realizes the intrinsic tensor part of
  original steps 1, 4, 5 and 6.
- lem-pur-diagram-geometric-tensor-presentations realizes geometric inverse-image,
  section-normalized compositor and resolving comparison existence from original
  steps 1, 2 and 6.
- lem-pur-diagram-tensor-pullback-shift-descent realizes original step 3 and the
  pullback part of step 6.

The three theorem nodes use the same generic resolving/site tools already
approved at the parent node. Their use is inherited from the original argument;
no replacement unit route is proposed. Blueprint searches for normalized tensor,
geometric inverse image and tensor shift found no matching blueprint theorem.
Change record: coord/changes/F7-diagram-pullback-shift-interface-extraction.md.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
