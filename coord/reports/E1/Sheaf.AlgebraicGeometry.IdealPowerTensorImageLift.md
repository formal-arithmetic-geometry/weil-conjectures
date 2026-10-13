## What changed

Replaced the sorry in
AlgebraicGeometry.Scheme.Modules.ideal_power_tensor_image_lift by a complete Lean
proof from three strictly separate intermediate theorems. All existing signatures,
definitions, universes and visibility are unchanged. The four original public
imports remain. Added ordinary proof imports for the three new modules and for
CoherentFiniteTypeLocallyNoetherian.

The proof obtains coherence and kernel annihilation, chooses an exponent using a
fixed-power Artin-Rees intersection bound, and proves sectionwise injectivity of
the restricted multiplication. A section mapping to zero belongs to the kernel;
the intersection bound and the zero ideal product make its inclusion zero, and
injectivity of the product inclusion makes the section zero. Differences give
injectivity, which gives categorical monicity. The final lift is the image
comparison followed by Mathlib's canonical imageMonoIsoSource and the product
inclusion. Its multiplication identity follows from imageMonoIsoSource_hom_self.

All four delivered modules compile together with lcompile.py --all. The assigned
module has no sorry. The remaining theorem statements were checked at exponent
zero, zero and unit ideals, the zero module, and the empty scheme in their proof
in words. No data definition or arbitrary witness construction was introduced.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.ideal_power_tensor_image_lift
(lem-pc-ideal-power-tensor-image-lift).

Added three named public theorem holes, each in its own new module:

- AlgebraicGeometry.Scheme.Modules.ideal_tensor_multiplication_kernel_control
  (lem-pc-ideal-tensor-multiplication-kernel-control).
- AlgebraicGeometry.Scheme.Modules.coherent_kernel_ideal_intersection_bound
  (lem-pc-coherent-kernel-ideal-intersection-bound).
- AlgebraicGeometry.Scheme.Modules.ideal_tensor_restricted_multiplication_image
  (lem-pc-ideal-tensor-restricted-multiplication-image).

This is a decomposition, not a sorry-free proof of the mathematical result:
one upper hole closed and three lower holes added, net minus two before any
closure changes from the dependency graph. No sorry remains inside the assigned
proof or any private helper. The three remaining proofs are exactly by sorry.

## No longer needed

No original import removed and no mathematical node or module pruned.
The old dependencies lem-weil-pbc-coherent-artin-rees,
lem-weil-pbc-coherent-kernel-cokernel-locnoeth,
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, and
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections leave the assigned
node's direct proof_deps, but remain in the intermediate nodes' argument plans.
The coherence criterion pqf-lem-coherent-ft-locnoeth remains a direct dependency.
No mathematical dependency is claimed as pruned. The final image
identification also needs the existing quasi-coherent cokernel/image node.
The full CoherentArtinRees statement is not directly imported by this delivery,
because doing so closes the source import cycle described below. The smaller
intersection theorem isolates the exact consequence used by this proof.

## Where the brief, the DAG or earlier work was wrong

The plan's instruction to import CoherentArtinRees cannot be followed directly:
tools/import_direction.py may reports NO. The source path back to this item is:
CoherentArtinRees -> ArtinReesAffineComparison ->
Modules.IdealTimesQuasiCoherentAffineSections ->
WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex ->
IntegralIdealProperCohomology -> IntegralIdealComparisonFiltrations ->
IntegralIdealCommonSubmodule -> RankOneGenericIdealInclusion ->
GenericIdealStalkEmbeddingExtension -> LocalClosedIdealMapExtension ->
ClosedStructureAmbientIdealExtension -> IdealPowerTensorImageLift.
Unrelated closed-immersion/cohomology proof imports must eventually be pruned or
interfaces separated by their holders before the existing sheaf Artin-Rees proof
can be directly reused here. No module outside the assigned item was adapted.

The fixed-power intersection theorem is a proper substep, not a renamed lift:
it has an arbitrary coherent source and arbitrary target, assumes only a
quasi-coherent kernel, and concludes an intersection containment without any
annihilation or lifting conclusion. The kernel-control theorem does not assert
any high-power restriction or image comparison. The image comparison holds for
every pair of exponents on any scheme, without Noetherianity or coherence, and
does not assert injectivity. Their combination in the assigned module is real
Lean and proves the original statement unchanged.

The unit's route is unchanged: these are substeps of the same second Artin-Rees
argument of Stacks Tag 01YB. The unit record has no realized statement/step node
bypassed by this delivery. Searches found no exact existing replacement; LeanSearch
was unavailable (HTTP Internal Server Error), which is recorded as unavailable.

## New nodes

lem-pc-ideal-tensor-multiplication-kernel-control: the coherent tensor source and
quasi-coherent kernel annihilated by the given power; source Tag 01YB, steps 1--2
of the old node. Its complete affine balancing proof is in the module docstring
and node steps.

lem-pc-coherent-kernel-ideal-intersection-bound: the fixed-power inclusion obtained
by setting m=c+n in Artin-Rees, for arbitrary maps with coherent source and
quasi-coherent kernel; source Tags 01YA and 01YB, old step 3. This is also where
the source import cycle must be addressed when using the existing Artin-Rees
module; the direct affine proof route is spelled out in the docstring.

lem-pc-ideal-tensor-restricted-multiplication-image: identification of the image
of I^m T -> H with the ideal-sheaf-data product I^(n+m)H; source Tag 01YB, old
step 4. It includes exponent zero and the inclusion identity needed to construct
the lift, and does not require the Artin-Rees bound or monicity.

No change record: no existing statement, definition or public interface changed.
The second reading removed unnecessary public imports of Coherent and
Mathlib.AlgebraicGeometry.Noetherian from the new image-comparison module.
Its two remaining imports supply everything in its statement.

## Second reading by E1

1. Interface preservation: PASS. Compared the delivered assigned module with the
repository using diff. The only changes are four ordinary proof imports and the
body replacing its sorry. The existing signature, universes, visibility,
docstring and all definitions are byte-for-byte unchanged. The only existing
node changes are proof, proof_deps and proof_origin. No forced adaptation or
statement-change record is needed.

2. Kernel proof and axioms: PASS as a decomposition. Independently compiled all
four delivered files in import order, including after import cleanup, without
errors or warnings. Scratch copies with #print axioms for all four public
statements report only propext, Classical.choice, Quot.sound and sorryAx.
The assigned theorem has no sorry; exactly the three named theorems listed
above have bodies := by sorry. Scanned the modules for forbidden declarations
and attributes. There are no new definitions or arbitrary witness choices.
Read the sectionwise kernel-range argument, passage from zero kernel to
injectivity by differences, categorical monicity, and canonical image-source
isomorphism composition. Each step proves the original conclusion.

3. Split statements: PASS. Read each complete natural-language proof and its
matching node. Kernel control combines coherence with the elementary balancing
identity a*(sum b_j tensor h_j)=a tensor(sum b_j*h_j). The intersection lemma
is the fixed-power containment for an arbitrary coherent source and a
quasi-coherent kernel, without an annihilation assumption or lift conclusion.
The image lemma is an image identification for all exponents, without monicity
or Noetherianity. Each is strictly a part of the argument, and none restates the
assigned item. Checked exponent zero, the zero and unit ideals, zero modules
and the empty scheme; none supplies a counterexample. Membership on every open
in the intersection lemma follows from the subsheaf containment because local
preimages through a monomorphism uniquely glue. Compared with Stacks Tags 01YA
and 01YB, including the latter's omitted annihilation calculation and displayed
restricted multiplication isomorphism. Independent LeanFinder search for
annihilators of ideal tensor multiplication kernels, Loogle search for image
and monomorphism lemmas, Mathlib grep with annihilator/mulMap terminology, and
repository searches with intersection/kernel/tensor terminology found no
usable replacement for these three full sheaf statements. The Mathlib image
lemma already used is the shortest final categorical step. Existing affine
comparison and stalk lemmas are ingredients rather than replacements.

4. Route and pruning: PASS after import cleanup. Independently traced the source
import path from CoherentArtinRees back to this item, verifying the cycle
reported above. Thus the existing full Artin-Rees theorem cannot simply be
imported to close the smaller intersection theorem in this delivery. The
unit sk-thm-picard-coherence has empty realized statement and step arrays;
no realized node is bypassed, and the same second Artin-Rees argument is kept.
The No longer needed section now names every old direct dependency moved into
an intermediate argument, and distinguishes those edges from mathematical
pruning. Removed unused public imports of Coherent and
Mathlib.AlgebraicGeometry.Noetherian from the newly introduced image-comparison
module. All imports remaining in that module and the other modules supply
names occurring in their statements or actual proofs.

5. DAG agreement: PASS. All four node lean.statement fields exactly match their
Lean signatures. The assigned node's three proof steps describe the actual
kernel control, intersection-based injectivity, and image-isomorphism lift.
Its proof_deps are exactly the three new declarations plus the coherence
criterion used to obtain quasi-coherence of H. New nodes have their source,
complete proof steps, dependency union, proof_origin, three search records,
status, creation, blueprint provenance, chapter, unit and Lean attachment.
The intermediate nodes retain the original mathematical dependencies in their
planned arguments rather than falsely marking them pruned.

Second-reading changes: removed two unnecessary public imports from
IdealTensorRestrictedMultiplicationImage and clarified the old direct
proof-dependency edges in this report. No proof or statement was changed.
No additional split statement was closed: closing them requires the affine
comparison constructions or resolution of the source import cycle, rather
than a short application available in the permitted import graph. This remains
one original hole closed and three strictly smaller holes added (net -2),
not a sorry-free mathematical proof.
