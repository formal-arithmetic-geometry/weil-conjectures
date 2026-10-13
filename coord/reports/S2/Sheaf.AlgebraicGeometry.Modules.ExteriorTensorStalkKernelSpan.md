## What changed

Closed `AlgebraicGeometry.Scheme.Modules.exteriorTensor_stalk_kernel_le_relationSpan`
by transporting through exterior and tensor stalk comparisons, applying a fully proved
ordinary-module quotient-kernel calculation, and representing each relation generator
by local sections. All original signatures, definitions, visibility and public imports
are unchanged. New imports in the assigned module are proof-only.

Added `ExteriorTensorQuotientKernel.lean`, with a proved private exterior quotient-kernel
lemma and the proved public `exteriorPower.tensor_quotient_kernel_le_span`.
The proof descends the alternating wedge modulo the relation span along a surjection,
checks lift independence coordinate by coordinate, and then applies tensor right exactness.
Added `ExteriorSheafStalkComparison.lean`, containing the sole remaining intermediate theorem.
It is independent of short exact sequences, q, tensor kernels and the local relation span.

Private helpers in the assigned module prove finite-tuple representation on a prescribed
neighborhood, stalk exactness by forgetting to abelian sheaves, and the tensor comparison
on wedge germs. For each algebraic generator, the local distinguished entry is replaced
by f of a representative of its preimage: the germ is preserved, and the section relation
then holds by construction. No equality-of-germs shrinking lemma is needed for this step.

All three delivery modules compile together in import order without warnings. The unit
record has empty realization lists and is unchanged; the determinant route is retained.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_stalk_kernel_le_relationSpan`
(node `lem-sc-exterior-tensor-stalk-kernel-span`). Its proof depends on the new comparison
hole, so this is a reduction, not an axiom-free completion of the original theorem.

Added and proved `exteriorPower.tensor_quotient_kernel_le_span`
(node `lem-sc-exterior-tensor-quotient-kernel-algebra`), including its private
`exteriorPower.quotient_kernel` helper. No sorry is left in the algebra module or in the
assigned module. The algebra proof permits r=0 and s=0, arbitrary commutative rings,
noninjective f, nonflat A, and zero modules. It uses a right inverse of a surjection
whose proof is complete, solely inside a proof; no data is chosen from an unproved theorem.

Added 1 hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_stalk_comparison`
(node `lem-sc-exterior-sheaf-stalk-comparison`). This is exactly `:= by sorry`, with a
complete presentation/common-neighborhood/sheafification proof in its docstring.
The degree-zero case is the empty wedge, zero stalk rings give zero modules, and
there are no local freeness hypotheses. Net holes closed minus holes added: 0.
The remaining problem is strictly the compatibility of exterior powers with stalks,
while the quotient-kernel algebra and the local representative argument are completed.

## No longer needed

No original imports or modules are pruned: all four original public imports occur in
unchanged definitions or signatures. The old proof dependencies
`def-sc-sheaf-exterior-power` and `def-weil-pbc-module-stalk` remain statement dependencies
or enter through the exterior comparison; they are not claimed as globally pruned.
The original plan's further shrinking to enforce c_j=f(d) is unnecessary because replacing
that coordinate by f(d) already preserves its germ.

During development, removed the unused proof imports
`Sheaf.Algebra.Homology.ModuleStalkExact` and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.
The final stalk exactness proof uses the existing module-to-abelian-sheaf finite-limit
and finite-colimit theorem and Mathlib's exact abelian stalk functor directly.
Tensor right exactness in the new algebra module is imported proof-only.

## Where the brief, the DAG or earlier work was wrong

The item's proof dependencies originally named only definitions; they do not supply an
exterior quotient-kernel theorem or an exterior-stalk comparison. The updated node records
the actual comparisons and the completed algebra calculation. No statement error was found.
The hypothesis s≠0 is retained verbatim, although the completed argument also handles degree
zero by the proved algebra lemma.

Searches: LeanFinder found exteriorPower.presentation and isPresentationCore, but no direct
quotient-kernel or exterior-stalk result. Loogle found exteriorPower.ιMulti, linearMap_ext
and ιMulti_span. Ripgrep in Mathlib and both library roots found only presentation and
right-exactness infrastructure and this item's downstream callers. Blueprint searches
for exterior stalk and exterior quotient returned no matches; exterior matches concern
representations, purity, or the Riemann-Roch ancestor. LeanSearch was unavailable with
Internal Server Error, which is recorded as unavailability, not a mathematical verdict.

The referenced blueprint source file is absent from this machine's literature tree;
a request for the file at its pinned raw GitHub path failed. The supplied node and its
complete source-attributed proof were read. The two new proof refinements are therefore
marked `proof_origin.by = agent`, rather than claimed as freshly verified against the
missing source text. The Mathlib implementations and the existing comparison/exactness
modules were read directly.

## New nodes

`lem-sc-exterior-tensor-quotient-kernel-algebra`: the ordinary-ring exterior tensor quotient
kernel calculation, in `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorQuotientKernel`.
It is fully proved from Mathlib and contains no sorry.

`lem-sc-exterior-sheaf-stalk-comparison`: the exterior-sheaf stalk equivalence and its
wedge-germ formula, in `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison`.
This is the single new hole, with an independent proof plan. Both new nodes inherit the
item's chapter, unit and blueprint ancestry. No existing interface changes and no change
records are required.

## Second reading by S2

1. Interfaces: PASS. Read the repository and delivered modules in full and inspected
   their diff. Independently compared the raw signatures of both relation-span
   definitions and the original theorem: byte-identical. Both definition bodies
   are byte-identical too. Original docstrings, visibility and public imports are
   preserved; the six added imports in the original module are proof-only. No
   declaration elsewhere is adapted and no change record is required.

2. Proof and trust: PASS as a decomposition. All three modules compile together
   without warnings (2.5, 3.9 and 11.2 seconds). Scratch copies with explicit
   `#print axioms` were compiled in import order. The algebra theorem and private
   quotient-kernel lemma use only propext, Classical.choice and Quot.sound.
   The finite-tuple representation and stalk-exactness helpers, and both unchanged
   relation-span definitions, have the same clean axiom set. The tensor/exterior
   comparison helper and original theorem additionally use sorryAx, consistently
   with the one named comparison hole. Scanning all delivered Lean finds exactly
   that `:= by sorry` and none of the forbidden declarations or kernel bypasses.
   Lift selection in the algebra proof uses the supplied surjectivity hypothesis
   inside a proof; the delivered code adds no data definitions and chooses no
   arbitrary object from an unproved existence theorem.

3. New statements: PASS. Read both new nodes, their Lean signatures and their
   docstring arguments. The sole split-off hole is exterior/stalk compatibility
   on wedge germs for arbitrary M and n, independent of S, q and relation spans;
   it is a strict part of the original argument, not its restatement. The
   sectionwise presentation and common-neighborhood construction prove the
   claimed equivalence without finite generation or local freeness. At n=0,
   the empty wedge gives the structure-ring comparison; at n=1, the comparison
   recovers ordinary module germs; zero modules and zero stalk rings introduce
   no exception. In the algebra statement, s=0 gives zero kernel and an empty
   generator set; r=0 still has the empty wedge. For s=1 it specializes to tensor
   right exactness. Noninjective f and nonflat A cause no problem: only the image
   equality and surjectivity are used. The implemented lift-independence argument
   and both span inductions have been read, not just compiled. Fresh LeanFinder,
   Loogle and msearch grep queries, plus rg over both library roots, found no
   existing replacement. The comparison has its source-attributed complete
   presentation/sheafification argument and its own DAG node. Closing it is a
   substantial missing construction, not a few-minute lemma application.

4. Route and pruning: PASS. The proof identifies q on pure wedges by representing
   both tuples on a common neighborhood, applies the completed algebra result,
   and realizes each relation by replacing its distinguished coordinate with
   f(d). This replacement preserves its germ and avoids an unnecessary further
   shrinking. The determinant route and the unit's empty `realized` lists are
   unchanged. All original public imports remain needed by the existing API.
   The two old proof dependencies are explicitly accounted for above: they remain
   statement dependencies, and the comparison uses them, although the original
   node's direct proof dependencies now name the actual intermediate theorems.
   Tried replacing FlatPullbackStalk with Mathlib's generic ModuleCat.Stalk in a
   scratch comparison file: it fails to synthesize the scheme-module stalk Module
   instance. Thus that public import is needed for the new statement. The Ab and
   Abelian imports supply the short-complex facts and exact stalk functor used in
   the stalk-exactness helper. No module is claimed globally pruned.

5. DAG: PASS after metadata repair. Each node's proof-dependency list equals the
   union of its proof steps' uses. The original node records exactly the two
   comparisons, forgetful exactness and completed algebra theorem used by Lean.
   New nodes have the required provenance, chapter/unit ancestry, searches and
   Lean records. Their source text is unavailable locally, as the first report
   states; this review confirms the arguments against the actual definitions and
   implementations and does not claim a fresh reading of that missing text.
   Existing statement and statement dependencies are unchanged.

Second-reading changes: replaced the two new nodes' normalized one-line Lean
statement records with verbatim multiline signatures, added the fresh independent
search results to those new nodes, and wrote this review. No Lean proof or API
change was needed. One original hole is replaced by one strictly smaller hole;
net closure progress is zero and the original theorem is not yet axiom-free.
