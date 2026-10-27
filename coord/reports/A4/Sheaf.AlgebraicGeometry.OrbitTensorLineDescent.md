## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.orbit_tensor_line_descent` to the three
actual steps of its existing local-frame argument. Its signature is byte-for-byte
unchanged. The complete Lean proof constructs the local-frame input from a frame
of L, applies the two normalization formulas to that same frame, invokes general
invariant-frame descent, and retains all six coherence and normalization clauses.

`OrbitTensorLocalFrames.exists_orbit_tensor_local_frames` is proved. It applies the
existing finite-upstairs trivialization theorem, transports its isomorphism through
the over-category equivalence, compares the normalized tensor-pullback adjunction
with ordinary pullback to transport free generators, and inducts on the orbit list
and tensor power. The unit section proves both empty-tensor base cases.

Extracted the seven existing definitions to `OrbitTensorLineSections`, retaining
all signatures and data bodies, with a public reexport from the item. Added the two
remaining proper steps as separate modules, `OrbitTensorPermutationLinearizations`
and `InvariantFrameLineDescent`. The latter concerns any module with given invariant
local frames, not the orbit construction or its linearization. It requires neither
finiteness nor surjectivity of q, nor even a group structure on the index type.

All five modules compiled individually in import order in 13.7--14.6 seconds per
file. After removing redundant direct imports, the item was compiled again.
Checked exact preservation of the original theorem signature and all seven data
bodies, and the 100-character line limit. No existing direct importer of the item
exists in the current library. No target or source-library module was changed.
The change record is `coord/changes/A4-orbit-tensor-proof-interface.md`.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Scheme.Modules.orbit_tensor_line_descent`
(node `lem-per-orbit-tensor-line-descent`) by a complete compiling assembly.

This is a decomposition, not a completed proof of the original mathematics:
one upper hole closed and two lower holes added, for net minus one hole closed.
The local-frame construction is fully proved with no new holes. Its five private
helpers, including the normalized pullback-generator comparison, are also proved.

The two remaining holes, both exactly `:= by sorry` in their own public theorems:

- `AlgebraicGeometry.Scheme.Modules.exists_orbit_tensor_linearizations`
  (`lem-per-orbit-tensor-permutation-linearizations`): construct the permutation
  action and its coherent tensor-power comparisons; no quotient-ring hypothesis
  and no invertibility of L are assumed.
- `AlgebraicGeometry.Scheme.Modules.invariant_frame_line_descent`
  (`lem-per-invariant-frame-line-descent`): construct the invariant subsheaf from
  given local invariant generators, prove its coefficient descriptions, and build
  evaluation and tensor-power maps. It does not supply the local generators or
  construct the permutation action.

There are zero sorries in the item or in the extracted definition module, zero in
OrbitTensorLocalFrames, and exactly two in the full delivery. Both remaining
statements have complete proof docstrings and matching nodes. Neither has the
original hypotheses and conclusion under a new name.

## No longer needed

Removed the direct public imports of TensorPullbackSectionAdjunction,
AmpleCurveTwoSectionPencil and TensorSection from the item: these are reexported by
OrbitTensorLineSections and still needed there. Removed the direct public imports
of RingedSiteModules and CochainTensorUniverses: the general-site abbreviation is
unused, and the latter remains available through AmpleCurveTwoSectionPencil.
Removed the direct proof imports of FiniteTrivializeInvertibleUpstairs (now used by
the proved local-frame module) and InvertiblePullbackTensor.

The bundled theorem `lem-weil-pbc-invertible-pullback-tensor` is unnecessary for the
new argument: the local-frame proof uses the proved free-generator APIs directly,
and the permutation step uses the more general existing
`lem-weil-pbc-module-pullback-tensor`. The latter works for arbitrary L. The other
old dependencies remain used by the corresponding proper steps, rather than by
the assembly itself. The node's proof_deps records the three actual steps.

No existing module is withdrawn. In particular, AmpleCurveTwoSectionPencil still
privately imports InvertiblePullbackTensor; removing our direct import does not
remove that source declaration or its dependencies. No whole-module pruning is
claimed. The unit route and the parent's dependency on this item are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or target mismatch was found. The previous DAG marked the
invariant-subsheaf, coefficient, evaluation and tensor-power construction as
"elementary" while no reusable Lean invariant-frame descent theorem exists.
Those steps are now exposed together as a proper, general theorem with a precise
local-generator hypothesis. The existing bundled invertible pullback/tensor
result is not needed to prove the explicit frame step.

Checked the edge cases before stating the new results: empty schemes and opens,
the trivial group, nonfaithful and wild-characteristic actions, and tensor degree
zero. The local-frame theorem actually needs only a finite indexing type, not a
group. The general descent statement also allows an empty indexing type: its
ring-image condition then says q.app is surjective, and with injectivity it is
an isomorphism, exactly what the coefficient proof needs. No group-order scalar
is inverted. The degree-zero map is required on all scalars, not merely on 1.

Whole-blueprint searches found no existing orbit-tensor, invariant-frame,
permutation-linearization or invariant-coefficient statement to reuse. The
related norm-frame tensor-section gluing theorem assumes a multiplicative norm
on all scalars and only produces global norm sections; it does not supply the
invariant subsheaf, evaluation, or sectionwise tensor-power identifications here.

## New nodes

`def-per-orbit-tensor-section-comparisons` records the seven unchanged real-data
section and comparison constructions now in OrbitTensorLineSections. Their
existing ownership is transferred out of the original node's declarations list;
no object is chosen from an existence theorem.

`lem-per-orbit-tensor-local-frames` records the proved finite-upstairs frame and
all-power generator step, in OrbitTensorLocalFrames.

`lem-per-orbit-tensor-permutation-linearizations` records the canonical orbit
permutation construction and its four coherence and two normalization clauses,
with no quotient or descent assertion.

`lem-per-invariant-frame-line-descent` records effective descent by fixed sections
from given invariant local frames, including evaluation and every tensor power.
It is the coefficient-and-gluing part of the original argument, independent of
the orbit tensor and the finite-group construction.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
