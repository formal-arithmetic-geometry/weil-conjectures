## What changed

Replaced the sorry in `CategoryTheory.abutment_finite_page_comparison` by a proof with its
original signature unchanged. The proof constructs the specified alpha iterate and proves
its invertibility directly from exactness and negative-index E vanishing. It obtains the
canonical image lift from the new proved `finitePage_image_lift`, obtains the finite-page
quotient from `finitePage_graded_quotient`, and constructs the filtration transport and
stable-page comparison with Mathlib cokernel and epimorphism universal properties. All
projection equations are proved, and Theta is the stated composite by definition.

Added `Sheaf.CategoryTheory.FinitePageImageLift` (proved) and
`Sheaf.CategoryTheory.FinitePageGradedQuotient` (one named sorry). The image-lift proof
normalizes the families in the existing `pageCouple_image` using their recurrences,
proves composition of alpha iterates, splits the incoming iterate at index zero, and
uses `Subobject.isoOfMkEqMk` to construct the lift and its equation. It does not assume
D or E vanishing. No definition or existing statement changed; no forced adaptations.
Updated the item's proof DAG and supplied nodes for both new public statements.

Validation: all three modules compile together in import order with `lcompile.py --all`,
with no errors or warnings. `deliver3.py --no-push` printed OK: compilation and preflight
passed before the independent second-reading section was added.
Nothing was pushed.

## Proved and sorry left

Closed the item's sole syntactic hole:
`CategoryTheory.abutment_finite_page_comparison`
(node `lem-sp-abutment-finite-page-comparison`). No sorry remains in that module.

Also proved `CategoryTheory.finitePage_image_lift`
(node `lem-sp-finite-page-image-lift`) from the existing
`CategoryTheory.BigradedExactCouple.pageCouple_image`. The alpha, filtration transport,
and stable quotient helpers in the item are all proved.

Added exactly one hole, whose proof is exactly `:= by sorry`:
`CategoryTheory.finitePage_graded_quotient`
(node `lem-sp-finite-page-graded-quotient`, module
`Sheaf.CategoryTheory.FinitePageGradedQuotient`). This is only the quotient induced by
derived g after an invertible image lift has already been constructed. It has no limiting
subobjects, abutment, transported filtration, stabilization assertion, or Theta assertion.
Its docstring and node give the kernel-image computation, the lower-D vanishing argument
for epimorphicity, and the cokernel argument. The new statement was checked at p=0,
q<a, the zero couple, and arbitrary negative a: r>=p+1 and q-R+1<a continue to hold.
The statement does not assume q>=a or the extra negative-E support condition.

This is a decomposition: one original hole closed and one smaller hole added, so its
syntactic net is zero. The image-lift proof additionally depends on the already stated,
still-holed `pageCouple_image`; this delivery does not claim an axiom-free proof of the
full original theorem or of that existing dependency.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.ExactCouple` and
`Sheaf.CategoryTheory.Filtration`: their declarations are already available through the
unchanged public statement imports. Replaced the direct
`Sheaf.CategoryTheory.DerivedCoupleExact` import with the two new proof imports;
DerivedCoupleExact remains needed by the proved image-lift module. Its role has been
localized, not removed from the dependency closure.

The old direct proof dependency `lem-sp-derived-couple-exact` is replaced by
`lem-sp-finite-page-image-lift` and `lem-sp-finite-page-graded-quotient` in the item
node. It remains a transitive dependency of the image-lift proof. All other old
proof-dependency nodes are retained directly.

No entire node or module is pruned from the targets' import closure. The exact-couple,
convergence, filtration, image-filtration, derived-couple, and sharp-bounds nodes remain
needed, directly or through the new modules. The unit's realized statement and proof
steps are retained; no alternative unit route is used.

## Where the brief, the DAG or earlier work was wrong

The old node bundled the iterated-image identification, derived-g quotient, filtration
transport and stabilization into one prose step. The existing `pageCouple_image` interface
only supplies recursively specified existential families A and I, not the prescribed
incomingAlphaIter and inc families. The new proved normalization argument bridges that
interface explicitly rather than assuming those families coincide.

The pinned blueprint clause 6 in `thm-sp-truncation-e2.json` was read together with the
item's node and Lean docstring. The referenced literature Markdown file is absent in
this local checkout; no replacement source was invented. The new statements isolate the
same image-lift and derived-g quotient arguments recorded by that clause and the item's
existing source refinement. LeanFinder, Loogle and local grep returned only building
blocks; LeanSearch returned Internal Server Error and is recorded as unavailable.
Blueprint searches for incoming alpha, graded quotient, alpha and truncation were also
run; the broad spectral-sequence clauses do not state either new restricted interface.

## New nodes

`lem-sp-finite-page-image-lift`: the canonical isomorphism from the incoming-alpha
filtration step to the chosen derived-D term, including its equation with inc. Its new
module is `Sheaf.CategoryTheory.FinitePageImageLift` and it is proved. The node records
the recurrence normalization, alpha-iterate composition, and image-factorization proof.

`lem-sp-finite-page-graded-quotient`: the finite-page isomorphism induced by derived g,
assuming the already constructed invertible image lift and its equation. Its new module
is `Sheaf.CategoryTheory.FinitePageGradedQuotient`, containing the delivery's only added
sorry. It is a strict remaining part of the original argument, with a complete proof in
words and the same blueprint source. No change record is required: every existing
signature and public import is unchanged.


## Second reading by D3

1. Unchanged visible contract: PASS. Read the complete diff against the repository.
   The sole pre-existing theorem's raw signature is byte for byte identical, its
   docstring and visibility are unchanged, and both public imports are unchanged.
   Added imports are proof-only. There are no changed definitions, target statements,
   forced adaptations or interface change records.
2. Proof and trust: PASS as a decomposition. Independently compiled all three modules
   through `lcompile.py --all`, without errors or warnings. Scratch copies with
   `#print axioms` for all three public theorems report exactly propext, Classical.choice,
   Quot.sound and sorryAx. The latter is expected from the named new quotient theorem
   and existing open dependencies (including pageCouple_image). Read every private
   helper; none has a hole. There is exactly one delivered sorry, the entire proof of
   finitePage_graded_quotient. No forbidden declaration, hollow definition or arbitrary
   data choice is introduced. All constructed isomorphisms are fixed by their equations.
3. Split statements: PASS. The image-lift statement is proved using recurrence
   normalization and equality of represented subobjects. The remaining graded-quotient
   theorem is strictly part of the original theorem: it fixes lambda and lift and asks
   only for psi and its projection equation; it has no stabilization, limit objects,
   transport to H or Theta conclusion. Checked r>=p+1, u<=-1 and q-r-1<a, including
   p=0, q<a, negative a and the zero couple. The incoming derived-alpha image is the
   (r+1)-fold incoming image; splitting after p+1 steps leaves the same lambda.
   Its kernel is therefore the next filtration step. Derived f has zero target because
   its incoming image starts at D(p+R,q-R+1); exactness makes g epi and the cokernel
   argument gives psi. The source, complete prose proof and matching node are present.
   Independent LeanFinder search for iterated-image filtration quotients returned only
   exact-sequence/refinement building blocks. Local searches in Sheaf and upstream
   found no matching finite-page interface. HalfPlaneGradedCanonical and
   weakConvergence_comparison require convergence data and concern different canonical
   maps, so they do not prove the required finite derived-g equation. Mathlib provides
   the cokernel and epiDesc machinery already used by the proved helpers, rather than
   the missing image/kernel computation. Closing that computation is substantial work,
   not a short remaining tactic proof.
4. Top-down route and pruning: PASS. Read the proof from the original theorem through
   its helpers and new lemmas. Alpha invertibility follows directly from exactness;
   transport uses Subobject.isoOfMkEq and cokernel.mapIso; the stable comparison uses
   the existing sharp bounds and projection kernel/epi properties. All retained direct
   imports have a use. No proof-only import is public. The removed direct dependency
   and its continuing transitive use are now explicit under No longer needed.
   Read dag/units/sk-thm-properbasechange.json realized and the pinned truncation
   blueprint clause 6: the finite-page quotient and transport route is preserved,
   and no realized statement or step is bypassed or removed.
5. DAG agreement: PASS. Compared the existing node: only proof, proof_deps and
   proof_origin change. Its new steps follow the actual Lean constructions, and their
   uses have union equal to proof_deps. Checked both new nodes' statements and verbatim
   Lean interfaces, source, searches, status, created, chapter, unit and blueprint
   ancestry. Corrected the image-lift ancestry place from step 6 to step 5 to match
   its own docstring and the completeness/image-filtration argument.

Second-reading changes: corrected that new node's blueprint place, clarified the
removed direct proof dependency in No longer needed, and added this independent
review. No Lean proof or statement required repair. The delivery remains one original
hole closed and one strictly smaller hole added, net zero; it does not claim the full
original theorem is axiom-free.
