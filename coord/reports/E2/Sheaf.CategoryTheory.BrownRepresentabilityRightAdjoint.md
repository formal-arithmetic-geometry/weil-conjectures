## What changed

Proved `CategoryTheory.brownRepresentabilityRightAdjoint` with its signature unchanged.
The proof constructs `F.op ⋙ preadditiveYoneda.obj d`, proves product preservation
using opposite discrete diagrams and reflection through the forgetful functor, gets
its homological instance from the triangulated functor instances, and uses Mathlib's
`Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top` to construct the adjoint.
Added proof-only imports for these Mathlib APIs and the new universe-transfer module.
No existing dependency statement or public import changed. The added opposite
scope is recorded in `coord/changes/brown-right-adjoint-opposite-scope.md`, because
preflight treats added open commands conservatively as interface changes.

The Brown theorem already in the project has a common morphism/value/indexing universe.
The new helper assumes that common-universe Brown principle, transports the category
and functor to that universe, then transports the representing bijections back. The
main proof supplies the principle with `brownCohomologicalRepresentability`, so the
original Brown theorem remains a genuine dependency. This helper does not assume an
exact functor F, a second triangulated category D, or an adjoint, and does not reprove
Brown's generator/cone/telescope argument.

Both sandbox modules compile without warnings with lcompile.py. Source checks:
Stacks 0A8F and 0A8G were read from their official web pages because the read-only
clone lacks the regenerated literature files. The original unit route is retained.

## Proved and sorry left

Proved `CategoryTheory.brownRepresentabilityRightAdjoint`, the item's sole sorry.
One sorry added: `CategoryTheory.brownCohomologicalRepresentabilityUniverseTransfer`,
node `lem-pc-brown-representability-universe-transfer`. Its docstring and node give
all transport steps. The existing imported `brownCohomologicalRepresentability`
(node `lem-pc-brown-cohomological-representability`) remains unchanged and sorry.

## No longer needed

Removed the redundant proof-only import `Mathlib.CategoryTheory.Limits.Yoneda`
added by the first worker; the proof compiles without it.
None of the original imports, nodes, or modules is pruned. In particular the existing
Brown theorem, its compact-generator construction, and its compact-Hom telescope
input remain needed. Mathlib supplies the Hom/cohomological and Yoneda-to-adjunction
steps, so no additional project nodes for those steps are necessary.

## Where the brief, the DAG or earlier work was wrong

The existing cohomological Brown declaration fixes the morphism, value, generator,
and coproduct universes to one universe v. The right-adjoint criterion has independent
v₁ and v₂ and coproducts in max w v₁ v₂, so its Hom functor cannot be passed directly
to that declaration. The DAG did not account for this interface mismatch. The new
lemma isolates only that transport and takes the existing Brown theorem as a premise.
Neither existing statement was weakened or changed.

The new statement was checked on equal universes, vH smaller/larger than v, empty
coproducts, and the zero category: ULiftHom preserves the object universe and the
common maximum bounds all indexing sets and group elements. All these cases fit the
same equivalence transport, with no additional smallness or nonempty assumptions.

Searches: LeanFinder found the partial-adjoint API and final ULift representability
transport APIs; Loogle did not resolve the names; LeanSearch returned Internal Server
Error; local rg confirmed the exact API signatures and no existing Brown-universe
transfer node or theorem. The new node records the queries and limitations.

## New nodes

`lem-pc-brown-representability-universe-transfer`, in
`Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer`, isolates
transport of the existing common-universe Brown principle to independent universes.
It is a bookkeeping lemma about category equivalences and lifted abelian groups,
not a new Brown theorem or a renamed adjoint criterion. The scope-only change record is
`coord/changes/brown-right-adjoint-opposite-scope.md`; it lists all downstream users.


## Second reading by E2

1. Compared the delivered right-adjoint module with the repository using `diff -u`.
   The existing declaration signature and docstrings are byte-for-byte unchanged;
   only its proof, proof-only imports, and the recorded opposite scope changed.
   The new universe-transfer module has no existing interface to alter. The scope
   change record accounts for the added open command and downstream users.
2. Compiled both modules in import order with lcompile.py: no errors or warnings.
   There is exactly one new sorry, in the named universe-transfer theorem; no
   hollow definitions or forbidden declarations. Scratch-copy `#print axioms`
   reports only propext, Classical.choice, Quot.sound, and sorryAx for both
   declarations. The original Brown theorem and the transfer theorem remain open;
   the right-adjoint theorem is proved relative to these dependencies.
3. Read Stacks 0A8F and 0A8G at their official pages and checked the new theorem's
   full hypothesis list. Its hBrown premise is the original Brown declaration
   at V=max(w,v,vH), universally quantified over categories in the same object
   universe. ULiftHom keeps that object universe; lifting both Hom groups and H's
   values places them in V. The compactness comparison uses the same V-indexed
   families and finite-support Hom sums, so no smallness assumption is added.
   Group lifting preserves products of any existing diagram (also supplied by
   Mathlib.Algebra.Category.Grp.Ulift), and exactness transfers through the
   lift/down group equivalences. The representing component bijections descend
   to natural Hom_C(-,G) bijections. Equal universes, vH above/below v, empty
   families, and the zero category all satisfy this argument. The helper contains
   neither D, F, nor an adjunction conclusion: it is a genuine universe-transport
   part of the argument, not a renamed item. Its complete prose proof and matching
   node are present. Independent LeanFinder, Loogle, msearch grep, and local rg
   searches for representability transport, ULiftHom, and Brown found only the
   final representability/lift APIs, not an existing full transfer theorem.
   Loogle did not resolve `Functor.IsRepresentable`. Closing the transfer also
   requires explicit transport of triangulated structure and the project's
   compact generators, so it is not a short proof repair.
4. Checked the proof from the top: Mathlib's partial-adjoint criterion reduces to
   representability; opposite-colimit preservation and Yoneda give hH; opposite
   triangulated functor and homological composition instances give H.IsHomological;
   the transfer is supplied with the existing Brown theorem. Removing the new
   Limits.Yoneda import still compiled, so removed it. Separate removal probes
   showed Preserves.Opposites and Opposite.Functor are needed. All other imports
   support signatures or used declarations. The old proof_deps consisted solely
   of the Brown theorem and it is still used, so no old node is pruned. The
   sk-thm-picard-duality unit and its realized record are unchanged: the compact
   generator/cone/telescope Brown route remains through the original theorem.
5. Compared the old and new item nodes: only proof, proof_deps, and proof_origin
   changed. Their four steps match the Lean reduction, with both Brown and the
   transfer explicitly cited. The new node's statement matches its Lean signature
   verbatim, and its source, proof, searches, creation, blueprint, chapter, unit,
   and Lean records are present. Its proof_deps is empty because hBrown is an
   explicit premise, not an imported theorem. Verdict: passes with one open
   transfer lemma.

Changed in this second reading: removed one redundant proof-only Mathlib import
and corrected the pruning report; added this independent review. No theorem
statement, definition, or proof body needed repair.
