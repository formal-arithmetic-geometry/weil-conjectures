## What changed

Replaced the sorry in
`HomologicalComplex₂.coneHorizontal_quotient_iso_exists` with a complete proof
from a kernel equality and an epimorphic projection. The proof derives the
zero composite, forms an exact short complex, makes its second map a cokernel,
evaluates the filtration cokernel, and compares the two cokernels with Mathlib's
canonical isomorphism. Its cocone equation is exactly the required equation.
The existing signature and public imports are unchanged. Two new proof-only
imports supply the following modules.

`Sheaf.Algebra.Homology.ConeHorizontalProjectionEpi` proves
`HomologicalComplex₂.coneHorizontal_projection_epi` completely. It constructs
the extended column inclusions, proves their projection equations, proves
that their images lie in the horizontal tail, assembles the signed section,
and factors it through the actual degreewise monic arrow of `F.step p`.
The source sign squares to one. Mathlib's `SplitEpi.epi` finishes the proof.
The private inclusion definition contains real data and no sorry.

`Sheaf.Algebra.Homology.ConeHorizontalProjectionKernel` states the remaining
kernel calculation as an equality of subobjects of `(F.step p).X n`.
It has a source, a complete natural-language proof and a matching new node.
Both new modules follow the project module format. The parent node's proof
and proof dependencies now describe the implemented cokernel argument.
No existing definition or statement was changed; no adaptations are required.

Repair of the landing refusal: removed the private theorem
`HomologicalComplex₂.factors_image_of_le` from ConeHorizontalProjectionEpi.
Its two call sites now apply the existing public Mathlib theorems
`Subobject.factors_of_le` and `imageSubobject_factors_comp_self` directly.
The matching `factors_image` in ConeHorizontalStepStable is private, so it
cannot be referenced by an ordinary importer. The already present import
provides the public Mathlib API; no import or existing module needs changing.

## Proved and sorry left

Closed the original hole:
`HomologicalComplex₂.coneHorizontal_quotient_iso_exists`
(node `lem-sp-cone-horizontal-quotient-iso-exists`). Its proof contains no sorry.

Also proved the new declaration
`HomologicalComplex₂.coneHorizontal_projection_epi`
(node `lem-sp-cone-horizontal-projection-epi`), including every private helper.

One new hole remains:
`HomologicalComplex₂.coneHorizontal_projection_kernel`
(node `lem-sp-cone-horizontal-projection-kernel`), in its own new module,
with proof exactly `by sorry`. There are no other delivered sorries.
Thus this is a decomposition with substantial surjectivity work completed:
one original hole closed, one lower hole added, net zero holes. The original
result is not yet an axiom-free proof because it depends on this kernel lemma.

Edge cases: the extended inclusion/projection identity is proved in Lean both
for `m >= p` and `m < p`; the latter source is zero. Consequently the section
construction covers `n = p-1` (source only), `n < p-1` (both objects zero),
`p = 0`, and all negative degrees. The kernel statement was checked on these
same cases and on the zero bicomplex. It does not assert compatibility with
differentials, nor does it need stability beyond the supplied filtration.

Repair validation: all three modules compile in import order with lcompile.py,
without warnings. The landing import_prune_check.py passes for each of the
three delivered modules, including ConeHorizontalProjectionEpi, which caused
the return. The delivery dry run printed OK; nothing was pushed. The original module compiles without an additional direct
Mathlib.CategoryTheory.Abelian.Exact import: that API is already available.
The delivery dry run is the final check; nothing is pushed by this worker.

## No longer needed

The duplicate private helper `HomologicalComplex₂.factors_image_of_le` is
removed; its factorization argument is supplied by existing public Mathlib
lemmas at both call sites. No original import or module is pruned. Two original proof dependencies are no
longer used directly by the parent proof: `def-sp-cone-horizontal-projection`
and `lem-sp-cone-horizontal-step-stable`. They remain statement dependencies,
and their modules remain imported for `coneHorizontalProjection` and
`coneHorizontalStep`; the new epi and kernel lemmas also use those definitions.
Thus neither node leaves the target closure. The third old proof dependency,
`def-sp-filtered-complex-subquotients`, remains used by the cokernel argument.
The three original public imports
are required by the unchanged statement: they define the projection, the
explicit step and the filtration/subquotients respectively. The stability
theorem `coneHorizontal_step_stable` is not applied by this objectwise proof;
its module remains necessary because it also defines `coneHorizontalStep`.
No differential-compatibility, generator-differential or graded-complex
isomorphism module is imported. A redundant direct import of
Mathlib.CategoryTheory.Abelian.Exact tried during development was removed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private image-factorization helper
`HomologicalComplex₂.factors_image` already in ConeHorizontalStepStable.
The repair removes that duplicate and uses public Mathlib declarations.
The second-reading section below records the earlier delivery review;
the repaired proof must be read again by the next worker.

The original proof dependency declarations provide definitions and stability,
not a finite-tail kernel identification; the residual calculation therefore
needs a new statement. Mathlib has `kernelBiproductToSubtypeIso` and
`kernelBiproductπIso`, but their application still requires identifying the
image-supremum tail and the evaluated filtration representative with the
appropriate diagonal sub-biproduct. This identification is included in the
remaining kernel lemma's proof in words.

The source read was Stacks Tag 012X, the first-filtration display before
Lemma 12.25.1 (label lemma-double-complex). That lemma's proof is omitted in
the source; the detailed cone refinement here is written by V1 and recorded
as agent-origin work, following the parent node's column calculation.

The inherited unit is `sk-prop-av-pqf-finite`, whose record is about proper
quasi-finite morphisms and has empty realized lists. Also, blueprint_refs.py
finds no imported blueprint ancestor for this generated item. Neither
inherited metadata issue is repaired by this proof delivery. The new nodes
keep the parent's chapter/unit and record a null ancestor with the precise
parent proof step. Blueprint searches for horizontal projection, cone
horizontal and column found no duplicate of either new statement.
LeanSearch returned Internal Server Error and is recorded as unavailable;
LeanFinder and source grep were run successfully and recorded verbatim.

## New nodes

`lem-sp-cone-horizontal-projection-epi`:
`dag/nodes/sec-abelian-varieties/lem-sp-cone-horizontal-projection-epi.json`.
Its new module proves that the restricted signed projection is epic; it does
not mention the graded quotient, a quotient isomorphism or the desired
projection equation. This is the surjectivity part of the original argument.

`lem-sp-cone-horizontal-projection-kernel`:
`dag/nodes/sec-abelian-varieties/lem-sp-cone-horizontal-projection-kernel.json`.
Its new module identifies the next-tail image with the restricted projection
kernel. It asserts no surjectivity or quotient isomorphism, and is strictly
the exactness part of the original argument. This is the sole new open item.

No change records were needed because all existing signatures, definitions
and public visibility remain identical.

## Earlier second reading (a previous round; superseded)

1. Interface comparison: PASS. Read all three delivered modules and diffed the
   existing module against the repository. The existing theorem signature is
   byte for byte identical, including its ambient instances, filtration
   equality, indices, existential conclusion and projection equation. Its
   only changes are two ordinary proof imports and the theorem body. The two
   other modules and two other nodes are new; no existing data definition,
   target, public import or visibility is changed. No change record is needed.

2. Proof and axioms: PASS as a decomposition. Independently compiled the three
   files in import order with lcompile.py: no errors or warnings. Read the
   constructed extended inclusion, its retraction, image factorizations,
   signed section, and transport to the actual filtration representative.
   All data are explicit; no arbitrary witness of an unproved existence
   theorem is chosen. The parent uses exactness plus epi, evaluation of the
   cokernel and canonical uniqueness of colimits. A scratch module's
   `#print axioms` gave only propext, Classical.choice and Quot.sound for
   `coneHorizontal_projection_epi`; the parent and kernel additionally have
   sorryAx, as reported. Exactly one delivered sorry remains, the named
   kernel theorem. No forbidden declaration or compiler bypass is present.

3. Split statements: PASS. The kernel equality is true for the actual
   subobjects, not just for abstractly isomorphic objects. Finite diagonal
   coordinate inclusions generate the defined image supremum; discarding
   index p gives exactly the next tail, and multiplying its source coordinate
   by (-1)^p does not affect its kernel. Evaluation preserves the monic step
   arrows, so transport through hF gives the claimed equality inside F.step p.
   Checked the zero bicomplex, p=0, n<p-1, n=p-1, and a degree with both
   index-p and higher coordinates. The kernel statement is strictly the
   exactness part: it asserts neither surjectivity nor a quotient isomorphism.
   Its docstring supplies source and complete coordinate proof, with a
   matching node. Independently searched with Loogle for imageSubobject and
   kernelSubobject (zero hits), LeanFinder for exactness of complementary
   direct-summand inclusion/projection, and grep for biprod exactness and
   image-supremum formulas. The hits are general APIs or module-specific
   results, not this filtration kernel calculation. Read the local biproduct
   subtype kernel constructions and searched the Sheaf homology modules;
   there is no duplicate or immediate specialization that closes the hole.
   Checked the first-filtration display in Stacks Tag 012X; the cone refinement
   is correctly recorded as agent-origin work, not claimed as a quoted proof.

4. Route and pruning: PASS after reporting correction. The parent follows the
   short Mathlib exact-epi/cokernel route; it does not restate its conclusion
   as the remaining hole. Its three public imports serve its unchanged
   signature, and the two new imports serve only the proof. The new modules'
   public imports likewise serve their signatures. The inherited unit has
   empty realized lists, so this change bypasses no realized statement or
   step. The pre-existing unrelated unit assignment is disclosed in the
   report and unchanged. Expanded No longer needed to name both old parent
   proof dependencies now used only through signatures and helper lemmas;
   their modules remain necessary and no module is pruned.

5. DAG agreement: PASS. The existing node differs only in proof, proof_deps
   and proof_origin. Its steps match the actual exactness, epi, evaluated
   cokernel and colimit-comparison proof. Each new node has statement
   dependencies, source, proof steps and their dependency union, origin,
   three search records, split status, creation metadata, blueprint ancestry,
   inherited chapter/unit, and a Lean record whose signature occurs verbatim
   in its module. The epi node describes a finished construction; the kernel
   node describes precisely the one remaining hole.

Second-reading changes: corrected the pruning report and added this review;
no Lean proof, statement or node required repair. The original hole is filled
conditionally on the kernel lemma: one original hole closed and one new hole
added, net zero. The newly proved epi lemma is axiom-free apart from the three
standard axioms. This is a decomposition, not a completed axiom-free proof of
the original theorem. Removed the temporary axiom-inspection source before
delivery.


## Second reading by V1

1. Interface comparison: PASS. Independently diffed the existing module and
   parent node against the read-only repository. The original signature,
   ambient instances, hF, indices, existential map, IsIso condition and
   quotient-projection equation are byte for byte unchanged. Only two plain
   proof imports and the theorem body changed. The parent node changes only
   proof, proof_deps and proof_origin. Both helper modules and nodes are new;
   no change record or forced adaptation is needed.

2. Proof and axioms: PASS as a decomposition. Compiled all three modules in
   import order with lcompile.py, without warnings. Independently compiled a
   scratch axiom inspection: coneHorizontal_projection_epi uses only propext,
   Classical.choice and Quot.sound; coneHorizontal_projection_kernel and
   coneHorizontal_quotient_iso_exists additionally use sorryAx. The scan found
   exactly the reported kernel sorry and no forbidden declarations. Read the
   repaired factorization call sites: Subobject.factors_of_le and
   imageSubobject_factors_comp_self replace the duplicate private helper.
   extendedColumnInclusion is explicit data; the section is constructed before
   factoring through the monic step arrow, with no arbitrary data selected
   from an unproved existence theorem. In the parent, image/kernel equality
   gives the zero composite and exactness, epi gives gIsCokernel, evaluation
   preserves the filtration cokernel, and colimit uniqueness gives the exact
   required equation at WalkingParallelPair.one.

3. Split statements: PASS. Read the actual projection, image-supremum tail,
   filtration/subquotient definitions and both new node files. The kernel
   statement asserts equality inside the actual F.step p representative;
   monicity and hF transport the next-tail image there. On each finite
   diagonal, deleting the p-th source and target coordinates leaves exactly
   the indices at least p+1; the source coefficient (-1)^p is invertible.
   Checked zero objects, p=0, n<p-1, n=p-1 (only the source p-coordinate),
   n=p (source and target p-coordinates), and higher degrees with later
   coordinates. No differential claim is smuggled into this objectwise result.
   The kernel claim is strictly the exactness part and does not assert epi
   or a quotient isomorphism; the epi part is already proved. Read Stacks
   Tag 012X, the first-filtration display and Lemma 12.25.1, whose proof is
   omitted: the cone refinement is correctly attributed to the agent.
   Repeated search with different wording: LeanFinder for the image of
   complementary direct-summand inclusions returned kernelBiproductToSubtypeIso
   and kernelBiproductπIso, and grep for image/kernel equalities and subtype
   inclusions returned the generic ImageToKernel and biproduct APIs. Read
   Biproducts.lean lines 837–936, including its kernel universal properties.
   These do not identify the concrete image-supremum tail; closing that
   identification is substantial work rather than a few-minute specialization.
   Loogle's unqualified kernelSubobject query failed identifier resolution,
   so it was not treated as evidence of absence. Searches of lean/Sheaf and
   the upstream WeilConjectures and Comparator found no duplicate calculation.
   The kernel docstring has the source, coordinate argument and representative
   transport needed to take over the hole.

4. Route and pruning: PASS. The parent takes the short exact-epi/cokernel
   route using the two strictly smaller helper statements. Each of its three
   public imports is required by its unchanged signature; the two helper
   imports are ordinary proof imports. The helper public imports likewise
   provide definitions in their statements. No unused original module can
   be removed. No longer needed names both old proof dependencies now used
   through definitions and helper lemmas, and retains the subquotient node.
   Opened dag/units/sk-prop-av-pqf-finite.json: its realized statement and
   step lists are empty, so no realized unit route is bypassed. Its unrelated
   geometric metadata remains disclosed rather than silently rewritten.

5. DAG agreement: PASS. The parent's four steps follow hk, exactness and epi,
   evaluated cokernel, and canonical comparison in the Lean proof. The epi
   node follows the extended inclusion, signed retraction and tail
   factorization; the kernel node records the one remaining calculation.
   New nodes have self-contained statements, source, dependency unions,
   agent proof origin, three recorded searches including service failure,
   creation data, blueprint metadata, inherited chapter/unit and verbatim
   Lean theorem signatures. No new node restates the parent conclusion.

Second-reading changes: appended this independent review of the repaired
version. No Lean or node repair was needed. Removed the scratch axiom
inspection source. One original hole is closed and one lower hole is added:
net zero, a decomposition, not a completed axiom-free proof of the parent.
