## What changed

Replaced the sorry in
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_coordinate_data`
with a complete Lean reduction. The public signature is unchanged. Added a proof-only import of
`Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData`.

The three private helpers `tensorDegreeIso`, `tensorDegreeIso_tmul`, and
`exists_tensorComplexIso` are proved without sorry. They construct the tensor equivalence from
compatible ring equivalences and a chain isomorphism, establish linearity after restriction of
scalars by tensor induction, and verify differential compatibility using `q.hom.comm`.
The main proof takes b=1 in the tensorMap compatibility formula, applies these constructions,
and assembles all four required compatibility clauses. No choice is made from a mere
unproved existence theorem inside a definition: the private degree isomorphism is an explicit
TensorProduct.congr construction applied to input equivalences.

The remaining geometric construction is stated in its own module and DAG node. Its docstring
explains the four stalk-map identifications and the scalar-compatible input-stalk comparison.
Small cases checked mathematically: the construction has no nonzero-ring, flatness, boundedness,
or nonzero-complex assumption; zero complexes obey the same formulas; an empty spectrum has
no z0. Both modules compile within the existing limits.

The initial assembled proof exhausted heartbeats by expanding the large stalk-complex types.
Introducing the statement's let bindings, and applying the generic helper to Q and Q0 rather
than unfolding them again, fixes elaboration. The private helpers live outside the original
section so that its instance variables and public commands remain unchanged. No shared definition
or interface changes. The unused-variable linter is disabled only on the
original theorem: its preserved signature contains i and the unused homology-coordinate lets,
which are absent from its Lean conclusion. Other linters remain enabled.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_coordinate_data`
(node `lem-pc-affine-spectrum-tensor-coordinate-data`). Its proof contains no sorry.

Added one hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_stalk_coordinate_data`
(node `lem-pc-affine-spectrum-stalk-coordinate-data`, module
`Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData`). This asserts only compatible
stalk-ring equivalences and the input stalk-complex isomorphism; it does not supply the tensor
complex isomorphism or its pure-tensor formula. Those are proved in the original module.

Thus this is a decomposition: one original hole closed, one strictly smaller hole added,
net holes zero. It is not a sorry-free proof of the geometric coordinate construction.
The three private scalar-transport helpers add no holes.

## No longer needed

No imports removed. Both existing public imports are required by the unchanged signature:
`IsoPullbackStalkCohomology` supplies the shared stalk and pullback API, and
`TensorPullbackCompositionIso` occurs in the retained alpha let binding.

The new scalar-transport proof requires neither derived tensor cohomology transport nor
homology compatibility, and does not import their modules. The original direct proof-dependency
edges to `def-pc-scheme`, `def-pc-derived-category`,
`def-pc-single-complex-base-change-stalk-condition`,
`lem-pc-iso-pullback-stalk-cohomology`, and
`def-pc-tensor-pullback-composition-iso` are replaced by the stalk-coordinate node. The first four
remain needed below that node; the fifth remains needed by the original public signature.
No existing dependency module can be declared globally pruned on this delivery.

## Where the brief, the DAG or earlier work was wrong

The existing node's prose includes an additional ordinary homology equation that is absent from
this module's Lean conclusion. That equation is handled separately by
`affineSpectrum_tensor_coordinate_homology_transport` in
`Sheaf.AlgebraicGeometry.AffineSpectrumTensorCoordinateTransport`. I preserved both the existing
Lean signature and the existing node statement and changed only its proof route.

The existing proof plan lists definition nodes and the additive stalk-cohomology isomorphism,
but none supplies a scalar-compatible stalk-complex coordinate theorem. The new node records
that remaining step rather than assuming the additive comparison is already semilinear.

`tools/blueprint_refs.py ancestor lem-pc-affine-spectrum-tensor-coordinate-data` returns no
ancestor because earlier created.item fields name Lean modules, not node ids. The new node
records that broken chain explicitly; the unit realization has empty statement/steps lists,
and this reduction does not bypass any realized unit step.

Mathlib searches were run through msearch.py and are recorded. LeanFinder and Loogle returned
component facts; grep found stalk isomorphism APIs. LeanSearch returned Internal Server Error
and is recorded as unavailable, not as a negative result. A further repository search found
`exists_inverseImage_stalk_scalar_transport_beta`: its fixed target ring does not supply the
simultaneous target-ring equivalence needed here, but its proved TensorProduct.congr pattern
helped the private construction. The Stacks pages for Tags 0098 and 0096 were read directly.

## New nodes

`lem-pc-affine-spectrum-stalk-coordinate-data` states the ring and input-stalk-complex part of
the affine-spectrum coordinate construction in a new module. Its complete proof in words,
source, actual searches, edge cases, and verbatim Lean statement are recorded in the node.
This is strictly smaller than the parent because the parent must additionally construct an
isomorphism of extension-of-scalars complexes with a specified formula in every degree.
There are no change records or forced adaptations.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered tensor-coordinate module with the repository version. The public theorem signature is unchanged byte for byte; the only existing declaration change is its proof, and the added stalk-coordinate declaration is in a new module and node.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds with no errors. The tensor-coordinate theorem has no `sorry`, while the explicitly split stalk-coordinate theorem is the sole named remaining hole. No forbidden declarations or hollow definitions were added; the private tensor helpers are constructive.
3. Checked the new stalk-coordinate statement against its intended affine-spectrum stalk construction and edge cases (zero complexes and empty spectra). It is strictly smaller than the parent because it omits the tensor-complex isomorphism and generator formula, and its docstring and node give the construction and sources.
4. Read the proof top down. It uses the new stalk-coordinate node, then constructs the extension-of-scalars tensor equivalence with `TensorProduct.congr`, proves differential compatibility by tensor induction and `q.hom.comm`, and assembles the required data. The retained public imports are needed by the signature; the stalk theorem is proof-only imported. The unit route remains represented by the existing node and its new reduction.
5. Verified that the existing and new DAG nodes match the Lean declarations, proof dependencies, origins, and split status. No old proof dependency is silently retained beyond the imports required by the public signature.

Changed during second reading: added this review record only; no Lean proof or statement changes were needed.


## Second reading by H4

1. PASS: Read the full diff against the repository. A byte-for-byte comparison of the
   existing theorem header through its conclusion succeeds. No existing definition,
   signature, visibility, or docstring changed. The only new public statement is in its
   own module; no change record or forced adaptation is needed.
2. PASS: Independently compiled both delivered modules in import order using
   `lcompile.py --all` (3.2 and 7.2 seconds, no warnings or errors). A scratch copy with
   `#print axioms` reports only propext, Classical.choice and Quot.sound for each of
   tensorDegreeIso, tensorDegreeIso_tmul and exists_tensorComplexIso. The original
   theorem and the split stalk-coordinate theorem additionally depend on sorryAx.
   The sole textual hole is the named split theorem. No forbidden declaration or
   hollow definition appears. tensorDegreeIso constructs its data from its explicit
   equivalence arguments, not from an unproved arbitrary existence statement.
3. PASS: The new statement is the ring/input-complex part of the original, omitting
   both t and its tensor-generator formula. It is strictly smaller and actually used.
   Its complete docstring explains stalk-map point transport, scalar compatibility
   on common-neighborhood germs, inverse maps and differential naturality. Checked
   zero complexes, vacuity of an empty source spectrum, and identity affine coordinates;
   no flatness or boundedness assumption is needed. Independent Loogle search for
   restrictStalkNatIso, LeanFinder search for semilinear stalk equivalence under a
   ringed-space isomorphism, and grep for stalkMap_comp/stalkMap_congr_hom found
   components, not the complete result. Repository searches also inspected
   affineModelStalkAddEquiv_smul and exists_inverseImage_stalk_scalar_transport_beta:
   the former concerns a tilde model and coordinate-ring action, and the latter
   fixes the target ring; neither supplies these four compatible ring equivalences
   and the input complex. Closing the geometric split requires more than a short repair.
4. PASS: Read from the public theorem down through all three helpers. Setting b=1
   gives the exact A-to-D compatibility; TensorProduct.congr constructs the degree
   equivalence, tensor induction proves restricted D-linearity, and q.hom.comm proves
   the differential squares. No shorter complete route was found. The two original
   public imports are required by the unchanged header; the new geometric theorem
   is imported privately. No longer needed lists all five old proof-dependency edges
   and correctly distinguishes replaced edges from globally pruned modules.
   Read sk-thm-picard-semicon: its realized.statement is empty and realized.steps
   is [[]]; no realized unit node or step is bypassed or removed.
5. PASS with the already reported pre-existing limitation: the parent node prose also
   states a homology equation absent from its Lean declaration. That mismatch is
   preserved and explicitly reported, not silently claimed proved here. Its new proof
   steps match the actual Lean reduction. Both nodes have proof_deps exactly the union
   of their proof-step uses. The new node has the required source, searches, split
   status, creation, blueprint, chapter/unit and Lean fields; its recorded Lean
   statement is byte-for-byte identical to the file. No node statement was changed.

Changed during this second reading: appended this independent review and its axiom/search
results only. No Lean repair was required. The delivery remains a decomposition: one
original hole closed, one smaller hole added, net zero; no module globally pruned.
