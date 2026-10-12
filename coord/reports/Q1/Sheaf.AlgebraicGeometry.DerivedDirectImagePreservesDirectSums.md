## What changed

Replaced the sorry in `AlgebraicGeometry.derivedDirectImagePreservesDirectSums` by a
complete Lean proof, with its statement unchanged. The private, proved helper
`exists_ambient_coproduct` chooses representatives using essential surjectivity of
`DerivedCategory.Q` and applies `derivedAmbientDirectSums` to construct the target
coproduct and its cohomology comparisons. The main proof constructs the comparison
using the coproduct universal property, verifies its cohomology by extensionality on
coprojections, cancels the ambient cohomology isomorphism, and applies Mathlib's
`DerivedCategory.isIso_iff`. It then transports the colimit structure along the
comparison and writes the universal property of the actual mapped cocone explicitly.

Added `Sheaf.AlgebraicGeometry.DerivedDirectImageCohomologyCoproduct`, containing the
remaining sheaf-valued comparison in one fixed cohomological degree. This isolates the
affine-local truncation and spectral-sequence part of the plan. It does not assert that
a derived comparison is invertible, or supply PreservesColimit: those steps are the
proved outer argument. Its docstring and node give the complete source proof, including
naturality of the comparison, finite filtrations, and empty-family and negative-degree
cases. Updated the main node's proof, proof_deps and proof_origin accordingly.

Both delivered modules compile without errors or warnings using lcompile.py --all.
No existing public signature, definition, or target was changed. The original target
module's declaration docstring remains intact; the updated DAG records the implemented
allocation of its steps to the new lemma and the proved outer argument.

## Proved and sorry left

Proved (relative to the explicitly stated dependencies):
`AlgebraicGeometry.derivedDirectImagePreservesDirectSums`, the only original sorry.
Also proved the private helper `exists_ambient_coproduct`.

The delivery leaves exactly one new sorry:
`AlgebraicGeometry.derivedDirectImage_cohomology_coproduct`, in
`Sheaf.AlgebraicGeometry.DerivedDirectImageCohomologyCoproduct`, node
`lem-pc-derived-direct-image-cohomology-coproduct`.
There are no sorries in the item's module. The imported ambient-coproduct theorem and
the planned prerequisites of the new lemma remain their existing separate proof items;
this delivery does not claim an axiom-free transitive closure.

## No longer needed

Removed direct proof imports from the item's module:
`Sheaf.AlgebraicGeometry.DerivedCategory` (already publicly available through
SchemeDerivedDirectImage), `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`,
`Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound`,
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum`,
`Sheaf.CategoryTheory.TruncationHypercohomology`, and
`Sheaf.Paper.HigherDirectImagePresheaf`.

`lem-pc-derived-direct-image-preserves-qcoh` and its module
`Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh` are no longer needed along this
proof route: the delivered signature concerns the ambient derived direct-image functor,
so no target-side quasi-coherent full-subcategory membership is needed to establish its
colimit universal property. This does not assert that the node is globally unreachable
from other targets or users.

The other removed proof imports are retained as prerequisites of the new cohomology
comparison module and are not globally pruned. Definition nodes
`def-pc-derived-category` and `def-pc-derived-direct-image` remain statement dependencies
and are available through the existing public imports. No unit statement or realized
unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was corrected. The main statement is preserved exactly.
There is no ambient derived-category HasColimit instance available for the family in
this statement. The existing `derivedAmbientDirectSums` theorem nevertheless explicitly
constructs the needed coproduct, so the proof uses its universal property rather than
assuming such an instance or adding an extra hypothesis. The final transport also
handles the distinction between a discrete cofan and the functor-mapped cocone.

The uniform-truncation theorem's second clause has an object-dependent eventual
threshold; it cannot alone supply a common threshold for all members of an arbitrary
family. The new lemma's proof uses the uniform upper-bound clause and the truncation
triangle on each affine target open. In particular it assumes neither compactness of
the whole target nor a globally uniform affine-cover bound. The empty family yields zero
objects, singleton families give identity comparisons, and arbitrary negative q is
covered by choosing the truncation sufficiently low for q and q+1.

The local literature checkout lacks perfect.tex. The source statements and proofs were
read on the official Stacks pages https://stacks.math.columbia.edu/tag/08DZ and
https://stacks.math.columbia.edu/tag/08D5; the repository's source identifiers are retained.
LeanFinder, Loogle, source/Mathlib grep, and the unavailable LeanSearch query are recorded
in the new node. No tool or repository process was worked around.

## New nodes

`lem-pc-derived-direct-image-cohomology-coproduct` records the canonical module-sheaf
coproduct comparison in a fixed degree q, for an arbitrary given ambient coproduct of
quasi-coherent derived objects. Its source is the cohomology comparison in Stacks Tag
08DZ with the bound from 08D5(2). The statement is a cohomological part of the argument;
the outer Lean proof constructs the derived comparison and proves its invertibility and
colimit preservation. Searches found the generic derived isomorphism criterion and the
existing ambient-sum construction, but no fixed-degree pushforward comparison. The
node retains the item's chapter and unit, records all prerequisites of the documented
proof, and has its own new Lean module. No change record is necessary.


## Second reading by Q1

1. Unchanged interface: compared the delivered main module with the repository using
   diff. The entire existing theorem signature and its docstring are byte-for-byte
   unchanged. Only proof imports, the proved private helper, and the theorem body
   differ. No existing definition or target was edited; no change record is required.
   The second delivered module is new and contains only its documented public theorem.
   Verdict: pass.

2. Proof and trust: independently compiled both files with lcompile.py --all, cleanly
   (2.8 s and 8.1 s). A scratch copy of the main module with #print axioms checked the
   main theorem, its private helper, and the imported new comparison theorem: each
   lists only propext, Classical.choice, Quot.sound, and sorryAx. The latter is expected
   from the named open comparison and existing ambient coproduct theorem. Read every
   proof step: essential surjectivity supplies representatives; the ambient sum gives
   the target cofan; Sigma.hom_ext and hs.fac identify its cohomology comparison;
   isIso_iff detects the derived isomorphism; ofPointIso and the explicit desc/fac/uniq
   fields supply the mapped cocone's universal property. Exactly one sorry remains in
   this delivery, the named public comparison theorem. No hollow definition or forbidden
   axiom, unsafe, opaque, implemented_by, or extern declaration occurs. Verdict: pass.

3. Split statement and source: read Stacks 08DZ and 08D5(2), and the imported ambient
   sum, uniform bound, K-injective restriction, quasi-coherent finite sum/filtered
   colimit, qcqs cohomology sum, and truncation spectral-sequence declarations. The new
   theorem concerns a sheaf map in one degree for a supplied ambient coproduct, rather
   than asserting derived invertibility or colimit preservation. Its hypotheses match
   the source: qcqs f, arbitrary quasi-coherent derived summands, arbitrary integer q;
   no compactness of Y or boundedness of the family is assumed. The upper-bound clause
   supplies a common truncation on each affine target open; the separate objectwise
   eventual clause is not incorrectly made uniform. The finite-filtration argument
   and its natural comparison are given in the docstring and node. Empty families give
   the zero comparison, singleton families give the cohomology of an isomorphism, and
   negative degrees are handled by a sufficiently low common truncation. Fresh searches
   used LeanFinder for higher-direct-image homology preserving arbitrary coproducts,
   Loogle for IsColimit.ofPointIso (unqualified name not found), and grep for
   homologyFunctor/colimit and higherDirectImage/sum, plus rg in the library. They found
   generic homological tools and the existing ambient theorem, but no theorem closing
   this comparison. Its spectral-sequence formalization is substantial, so it was not
   replaced by a speculative short proof. Verdict: pass.

4. Route and pruning: the outer proof takes the existing ambient coproduct theorem and
   Mathlib isomorphism detection directly; it does not merely apply a renamed copy of
   the target. All added proof imports are plain imports; original public imports stay
   unchanged. Proof imports of the new open theorem record its documented prerequisites.
   Checked sk-thm-picard-duality.json: its realized.statement is empty and its sole
   realized step is empty; this delivery changes neither the unit nor its route. The
   affine-local truncation and spectral-sequence route of 08DZ is retained in the new
   comparison. For completeness, every old main-node proof dependency removed from its
   direct proof_deps is accounted for: def-pc-derived-category and
   def-pc-derived-direct-image remain statement dependencies through public imports;
   lem-pc-derived-direct-image-uniform-truncation-bound, thm-sp-truncation-e2,
   lem-weil-pbc-qcqs-cohomology-direct-sum,
   lem-weil-pbc-higher-direct-image-presheaf, and
   lem-weil-pbc-module-sheaves-colimits-forgetful remain dependencies of the new lemma;
   only lem-pc-derived-direct-image-preserves-qcoh is pruned from this route, since the
   unchanged Lean conclusion concerns the ambient functor. Verdict: pass.

5. DAG agreement: compared the existing main node with the repository. Only proof,
   proof_deps, and proof_origin differ; the implemented proof uses precisely the ambient
   coproduct node and the new comparison node. The new node's proof_deps equals the
   union of its step uses, its source is 08DZ with 08D5(2), and its Lean statement matches
   the file. Checked its split status, search records, created item/group/date,
   blueprint ancestry, chapter/unit, and complete Lean record. No existing node
   statement is altered. Verdict: pass.

Second-reading changes: appended this independent review and explicitly accounted for
all removed old proof dependencies. No Lean or DAG repair was needed.
