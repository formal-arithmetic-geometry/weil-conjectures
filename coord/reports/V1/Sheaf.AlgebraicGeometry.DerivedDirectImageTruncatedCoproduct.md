## What changed

Replaced the sorry in AlgebraicGeometry.derivedDirectImage_truncated_cohomology_coproduct
with a complete Lean reduction to affine finite-support lifting. The original signature
and docstring are unchanged. Private, fully proved helpers establish the monomorphism
of a direct-sum map with component retractions, first for modules, then presheaves,
then sheaves via exact sheafification. Applying the additive functor H^q Rf_* τ≥a to
coproduct projections supplies these retractions. A finite-support representative gives
a preimage under the evaluated sheaf comparison; combining epi and mono gives an
isomorphism on each affine open. The affine-basis criterion and the conservative
underlying-sheaf functor conclude the original statement.

Added Sheaf.AlgebraicGeometry.TruncatedDirectImageAffineFiniteSupport, with its single
public surjectivity theorem, source, complete natural-language proof and DAG node.
Updated the original node's proof, proof_deps and proof_origin to follow this reduction.
All newly added imports in the original module are private proof imports. The new
obligation imports its planned spectral-sequence dependencies and the existing
quasi-coherent cokernel/image and extension lemmas. Its proof plan derives
quasi-coherence of the abutment by page induction and finite extension induction,
so exact affine sections do not require importing the bounded-below theorem.

Repair of the returned delivery: removed the finite-support module's private import
of Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh and replaced it with
Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage and
Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension. No shared declaration moved,
no existing module was adapted, and no signature or public import changed.
Updated the finite-support docstring and node to give the quasi-coherence argument
explicitly instead of invoking the cyclic dependency. The second reading below
records the earlier delivery; the repair requires a fresh second reading.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.derivedDirectImage_truncated_cohomology_coproduct
(node lem-pc-derived-direct-image-truncated-coproduct).
Added one strictly smaller obligation:
AlgebraicGeometry.truncated_directImage_affine_finiteSupport
(node lem-pc-truncated-direct-image-affine-finite-support), the surjectivity component
on affine sections. Its proof is exactly `by sorry` in its own new module.

This is a decomposition (one original hole closed, one lower hole added), not a net
hole reduction. The monomorphism half and the assembly from the remaining component
to the original isomorphism are proved in Lean. The two delivered modules compile in
import order without warnings through lcompile.py --all.

## No longer needed

Removed the following direct proof imports from the original module:
Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums;
Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum;
Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections;
Sheaf.CategoryTheory.TruncationHypercohomology;
Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum;
Sheaf.Paper.HigherDirectImagePresheaf;
Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful.

The original node now depends directly only on the new finite-support node. The
ambient sums, truncation hypercohomology, qcqs cohomology, presheaf higher direct image
and module sheaf colimit nodes remain needed in that new node's proof plan and imports; their
removal from the original module does not prune their mathematical obligations.

The binary-sum route lem-weil-pbc-quasi-coherent-module-direct-sum
(Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum) and the filtered-colimit route
lem-weil-pbc-quasi-coherent-module-colimit-affine-sections
(Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections) are not needed for
this argument: the already proved arbitrary-sum theorem
AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma, represented by
lem-pc-quasicoherent-module-coproducts, supplies quasi-coherence directly.
No claim is made that these modules are globally unreachable from other targets.

Also removed Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh
(node lem-pc-derived-direct-image-bounded-below-qcoh) from the finite-support module.
Its conclusion is derived within the remaining spectral-sequence argument using
page kernel/cokernel closure and finite extension closure. This prunes that direct
dependency, without claiming the bounded-below module is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The returned delivery had a transitive import cycle:
TruncatedDirectImageAffineFiniteSupport -> DerivedDirectImageBoundedBelowQCoh ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections ->
DerivedDirectImagePreservesDirectSums -> DerivedDirectImageCohomologyCoproduct ->
DerivedDirectImageTruncatedCoproduct. The earlier local compilation did not detect
this because it loaded compiled repository modules. The repair removes the first
edge and proves its needed quasi-coherence consequence within the lower proof plan.

No statement error found. The planned hypercohomology theorem gives a spectral sequence
for each bounded-below complex, but its signature does not package comparison of an
arbitrary sum of such sequences with the sequence of the sum. That naturality and
finite-filtration comparison still need substantial glue. The new node isolates the
surjectivity consequence, while the independent injectivity argument is fully proved.
The unit record has no realized statement or steps for this auxiliary item, and the
reduction retains the bounded-below spectral-sequence route below the unit level.

The cited literature source files are absent from this read-only clone. Read the
corresponding official Stacks pages https://stacks.math.columbia.edu/tag/08DZ and
https://stacks.math.columbia.edu/tag/015J. LeanSearch returned Internal Server Error;
LeanFinder and grep returned no exact theorem. No tool failure prevented compilation.

## New nodes

lem-pc-truncated-direct-image-affine-finite-support, in
 dag/nodes/sec-picard-framework/lem-pc-truncated-direct-image-affine-finite-support.json,
states surjectivity of the algebraic direct-sum section map on an affine open. It is
strictly the lifting half of the original comparison, without an injectivity or sheaf
isomorphism conclusion. Its edge cases q<a, empty index set and empty affine open are
zero-target cases; arbitrary negative lower bounds are allowed. The common lower bound
makes the abutment filtration finite. No new definition, target-signature change or
change record was needed.


## Earlier second reading (a previous round; superseded)

1. Compared the original module and existing node with the repository using diff.
   The original theorem signature and docstring are byte-for-byte unchanged.
   No existing definition or public import changed, and no change record is needed.
   The three added helpers are private theorems, not definitions or new public API.
   Verdict: no accidental change of the statement visible to other modules.

2. Compiled both delivered modules in import order with lcompile.py --all: no errors
   or warnings. Inspected every proof, including the DirectSum component identities,
   transport through exact sheafification and its invertible counit, the section lift
   through evaluated coprojections, and the affine-basis/forgetful-functor conclusion.
   A scratch copy with #print axioms for all five declarations confirms that all three
   private monomorphism helpers use only propext, Classical.choice and Quot.sound.
   The original theorem and the new finite-support theorem additionally use sorryAx,
   as expected from the explicitly remaining obligation. There is exactly one literal
   sorry, the complete proof of the new public named theorem; no forbidden declaration
   or hollow definition occurs. Verdict: the reduction is checked, not a complete proof
   free of pending obligations.

3. Read Stacks Tags 08DZ and 015J directly. The split-off assertion is the surjectivity
   half on affine sections, strictly smaller than the original sheaf-isomorphism claim.
   Quasi-coherence of bounded-below direct image allows exact affine sections and makes
   finite-support lifting valid; qcqs of inverse images follows from both morphism
   hypotheses and affineness of U. The common lower bound gives finitely many relevant
   filtration steps even when a is negative. Checked q<a, empty I, empty U, zero
   summands and singleton I: respectively zero targets or the expected identity map.
   Repeated LeanFinder with a different bounded-below pushforward/finite-support query,
   msearch grep for derived preservation and surjectivity, and rg on the repository
   for affine lifting and cohomology sum comparisons. No replacement found: the existing
   moduleCohomology_directSum_bijective applies to individual sheaves, and the general
   derived-preserves-sums theorem depends back on this item, so cannot be used here.
   The spectral-sequence comparison glue is not a few-minute closure. Verdict: retain
   one true, sourced, documented lower obligation and count this as a decomposition.

4. The proof first constructs projections by the coproduct universal property, then
   uses additivity and exact sheafification for mono without any quasi-coherence lemma.
   It calls the pending lower theorem only for surjectivity and proves the remaining
   assembly explicitly. Every old proof_deps entry is accounted for in No longer needed:
   five remain in the lower node, while the binary-sum and filtered-colimit alternatives
   are replaced by isQuasicoherent_sigma. Inspected sk-thm-picard-duality.json: its
   realized statement and step lists are empty; none is bypassed or modified. The new
   obligation retains the bounded-below spectral-sequence route and its proof imports.
   Verdict: pruning is complete for this local reduction; no global unreachability claim.

5. Checked the existing node's three proof steps against the Lean proof: projections
   and mono, affine lifting and epi, then the basis/reflection argument. Its proof_deps
   is exactly the new finite-support node. Checked all nine proof-dependency declarations
   of the new node and their imports; its Lean record matches the new theorem signature,
   chapter/unit/blueprint ancestry are inherited, and its creation record names this item
   and V1. Verdict: nodes agree with the reduction and the remaining proof plan.

Second reading changed the new node's informal statement to explicitly introduce I,
D_QCoh, the ambient coproduct, F_q, canonical truncation and its definition-node citations.
This clarifies the same assertion without changing Lean. No proof repair was necessary.
Added this review and the independent search records. Holes closed: one original named
hole; holes added: one finite-support hole; net zero. No extra hole was closed on review.

## Second reading by V1

1. Compared the delivered original module and node against the read-only repository
   with diff. The existing theorem signature and docstring are byte-for-byte unchanged;
   only private proof imports, three private theorem helpers and the proof body changed.
   No existing definition, public import or target statement changed. Verdict: pass.

2. Independently compiled both modules in import order through lcompile.py --all.
   Independently compiled a scratch copy printing axioms of all five declarations.
   The three private helpers use only propext, Classical.choice and Quot.sound; the
   original theorem and finite-support obligation also use sorryAx. Inspected the
   component retraction proof, exact sheafification transport, evaluated section lift,
   affine basis criterion and reflection of isomorphisms. The sole literal sorry is
   the complete proof of the named public finite-support theorem. No new definition
   or forbidden declaration occurs. Verdict: valid conditional reduction, not a
   completed axiom-free proof of the original theorem.

3. Read Stacks Tags 08DZ and 015J again. The affine-section surjectivity obligation is
   true for qcqs morphisms and strictly isolates the lifting half; the separate mono
   argument and global assembly are fully proved. Checked q<a, empty I, empty U,
   singleton I and zero summands: zero targets or the expected identity comparison.
   Searched independently with LeanFinder for orthogonal retractions and additive
   coproduct comparisons, msearch grep for bounded-below sums and finite support, and
   rg for cohomology localization and higher-image quasi-coherence. No usable shorter
   replacement appeared. The ordinary higher-image theorem in DirectImage.Sections
   imports the route back through this item, and cannot repair the cycle by reuse.
   The spectral-sequence comparison still requires substantial formal glue; it is
   not a few-minute closure. Verdict: retain one true sourced lower obligation.

4. Rechecked all seven original proof dependencies against No longer needed. Five
   remain in the lower obligation, and the binary-sum/filtered-colimit alternatives
   are replaced by the proved arbitrary coproduct quasi-coherence theorem. The removed
   bounded-below quasi-coherence import is absent from the repaired lower module.
   Inspected the unit's realized record: statement [] and steps [[]], unchanged.
   The lower argument keeps the spectral-sequence route. Proof imports of the pending
   obligation are its stated plan, rather than imports used by the literal sorry.
   Verdict: the local pruning and the unit route are accounted for.

5. Read the original node's three proof steps against the actual Lean proof and the
   lower node's full statement, signature, ancestry and planned dependencies. Found
   that kernel closure was imported and used in the repaired plan but omitted from
   proof_deps. Added lem-weil-pbc-quasi-coherent-module-kernel to both uses and
   proof_deps. Clarified the new theorem docstring and node proof: the second-page
   quasi-coherence assertion needs localization compatibility, proved from affine
   acyclicity and finite Mayer--Vietoris gluing on qcqs preimages, not just a pointwise
   affine cohomology description. Kernel/cokernel closure and finite extensions then
   give quasi-coherence of the abutments without the cyclic bounded-below import.
   Verdict: node and Lean now agree, with the remaining mathematical work explicit.

Second reading changed only the new obligation's proof documentation, its missing
kernel dependency, and this report. No existing signature or Lean proof changed.
Closed AlgebraicGeometry.derivedDirectImage_truncated_cohomology_coproduct;
added AlgebraicGeometry.truncated_directImage_affine_finiteSupport; net zero holes.
This remains a decomposition. No additional hole was closed during this reading.
