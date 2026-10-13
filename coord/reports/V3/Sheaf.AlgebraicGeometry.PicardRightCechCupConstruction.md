## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.Modules.picardRightCechCup_exists
by construction of a natural transformation from natural-index cochain components,
followed by extension by zero. Every existing declaration has its original signature
and visibility. Added a proof-only import of PicardExternalCechCupNaturality.

Separated the single-coefficient construction and coordinate naturality into
PicardExternalCechCupComponent and PicardExternalCechCupNaturality. The component
predicate writes the same canonical-unit formula inline to avoid an import cycle;
it agrees definitionally with the original formula, using proof irrelevance for
intersection inclusions. The witnesses are chosen only inside an existential proof.
No definition chooses data from an unproved existence theorem.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.Scheme.Modules.picardRightCechCup_exists
(node lem-sc-picard-right-cech-cup-construction). This is a decomposition, not a
sorry-free proof of the target's import closure.

Added AlgebraicGeometry.Scheme.Modules.picardExternalCechCupComponent_exists
(node lem-sc-picard-external-cech-cup-component), the fixed-right-coefficient
cochain construction. This is strictly smaller: it has no coefficient naturality,
no natural transformation, and no integer-degree extension.

Proved AlgebraicGeometry.Scheme.Modules.picardExternalCechCupComponent_naturality
(node lem-sc-picard-external-cech-cup-naturality) directly: total-summand and tensor
extensionality reduce the equality to tuple coordinates. Scalar Cech coefficient
naturality, tensor-section naturality, restriction naturality, and adjunction-unit
naturality close that equality. Its private scalarCech_map_apply helper is proved.
There are no sorries in the item's module or the naturality module. Closed one
original hole and added one strictly smaller hole: net zero, a decomposition.

## No longer needed

No existing imports removed: all three public imports support the unchanged
statements or definitions. The planned proof dependency
 def-sc-cech-refinement-cochain-map (Sheaf.Paper.CechRefinementCochainMap) is not
needed in this route. Its map is additive after forgetting scalars; the new
component construction uses the k-bilinear external tuple formula directly.
The other old proof dependencies, def-sc-cech-cup-product and
lem-pc-module-pullback-adjunction, remain used through the component predicate
and naturality proof; they are not pruned. No module is claimed pruned: the
refinement dependency was a DAG edge, not an import removed from this file. No unit realization or unit route changes.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies do not provide an external k-linear total cochain map:
CechCupProduct gives a same-scheme cohomological cup over global sections,
and CechRefinementCochainMap gives an additive refinement map. A combination
would require additional scalar and total-complex compatibility. The split
makes the required cochain construction explicit instead of assuming those
interfaces already supply it. No original statement was changed or disputed.

The local literature source files named by the node are absent on this machine.
Read the official Stacks pages 0BED and 07MB, which the existing node also records
as read. Empty families and zero modules require no additional assumptions:
the formula uses only projections and bilinear operations, and the naturality
argument uses the same tensor/product/coproduct extensionality.

## New nodes

lem-sc-picard-external-cech-cup-component records the fixed-coefficient cochain
construction with the full tuple formula. Module:
Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent.

lem-sc-picard-external-cech-cup-naturality records coordinate-based right-coefficient
naturality. Module: Sheaf.AlgebraicGeometry.PicardExternalCechCupNaturality.
No change records or forced adaptations: existing signatures and visibility stay
identical, and the new imports in the item's module are proof-only.


## Second reading by V3

1. Compared the entire original module with the repository using diff. PASS:
   the only changes are a plain proof-only import and the body of
   picardRightCechCup_exists. All four existing declarations retain their exact
   signatures, visibility, definitions and docstrings. There are no forced
   adaptations or statement changes. The two other modules are new.
2. Read all three delivered modules, including the private scalarCech_map_apply
   proof. Checked that the sole explicit sorry is the public named theorem
   picardExternalCechCupComponent_exists, with its source, full proof in words,
   and matching node. No forbidden declarations or hollow definitions occur.
   The component choices are local to an existential proof; they do not define
   data from an arbitrary unproved existence assertion. Compilation and axiom
   checks are recorded below after running the launcher.
3. PASS: the split construction fixes both coefficients and only constructs a
   natural-index cochain map; it omits naturality and integer extension. The
   original theorem has a real reduction assembling its witnesses into a natural
   transformation, using a separately proved naturality theorem. This is a
   strict decomposition rather than a restatement. Degree (0,0) gives the tensor
   of the two restricted sections. In degrees (1,0) and (0,1), the usual
   alternating differences have the stated Leibniz sign. Repeated indices are
   allowed; an empty factor index set gives no target tuples and zero complexes,
   and zero coefficients give zero pairings. No covering, affine, or exactness
   hypothesis is needed for the construction. Independently searched for a
   total-tensor-to-diagonal Alexander--Whitney map using leanfinder, for
   mapBifunctorDesc using loogle, and for Alexander/Whitney and external cup in
   Mathlib and the upstream/project sources. No complete existing construction
   was found. CechCupProduct does provide a proved same-scheme cochain Leibniz
   lemma; applying it here still requires pullback/refinement and scalar-linear
   total-map interfaces, so this is not a short closure of the remaining hole.
   Read the official Stacks sources https://stacks.math.columbia.edu/tag/0BED
   and https://stacks.math.columbia.edu/tag/07MB for the construction route.
4. PASS: the proof opens the original hole, uses the fixed-coefficient
   construction, proves naturality by total-summand/pure-tensor/tuple
   extensionality, and uses extendMap_comp for extension. All public imports
   provide names used in signatures or definition bodies; the new import in
   the original module is plain import. The component module has the same
   necessary signature imports; naturality imports its predicate publicly.
   All old proof dependencies are accounted for under No longer needed.
   dag/units/sk-prop-av-cube.json is unchanged, including its realized fields;
   no statement or step of the unit is bypassed by this local decomposition.
5. PASS: the existing node changes only proof, proof_deps and proof_origin.
   Its two dependencies are exactly the two lemmas used in the new proof.
   Both new nodes have matching verbatim Lean signatures, chapter/unit,
   provenance, source, proof steps, searches, creation and Lean records.
   Their predicates and proofs use the recorded cup faces and canonical
   pullback adjunction units. The naturality node is proved; its component
   dependency supplies the coordinate predicate, without using the component
   existence theorem in that naturality proof.

Second reading changes: clarified the disposition of every original proof
 dependency and that no module has been pruned; added this independent review.
No Lean repair was necessary. The remaining construction entails scalar
linearity and a full alternating-differential computation and cannot be closed
by a few-minute application of a theorem found in the searches.

Validation: lcompile.py --all compiled all three delivery modules without errors
or warnings. An independent scratch file imported the compiled delivery and ran
#print axioms on all seven public declarations. The naturality theorem and both
coordinate predicates, picardCechPullSection, and picardProductCechFace use only
propext, Classical.choice and Quot.sound. The original existence theorem and the
single split-off existence theorem additionally use sorryAx, as expected from
that sole remaining hole. The scratch file was removed before delivery.
