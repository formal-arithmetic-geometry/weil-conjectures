## What changed

Repair: removed the duplicate private `square_transport` theorem from
`Sheaf.CategoryTheory.ExactFunctorCouple` and changed the existing identical
`transport_square` theorem in `Sheaf.CategoryTheory.ExactFunctorHalfPlane` to
public visibility so the item can import and reuse it. All item call sites now
invoke `transport_square Φ`.

Proved `CategoryTheory.BigradedExactCouple.exactFunctor_couple` with its original
signature unchanged. Its private helpers explicitly construct the mapped exact
couple, functorial image/kernel/cokernel comparisons, all three derived-map squares,
the finite-page comparisons and their monic D inclusions, the normalized diagonal
colimit comparison, and the filtration-step and graded-piece comparisons.

Added the proved module `Sheaf.CategoryTheory.ExactFunctorHalfPlane`. It proves the
remaining infinite-page and explicit large-page comparisons from the finite-page
and filtration data. The finite g maps commute by induction. The cycle and boundary
towers stabilize under the required bound, and their quotient presentations give
all stable-page identifications. Weak convergence supplies the canonical graded
isomorphisms; their uniqueness and the filtration quotient square prove naturality.
For large pages, the inverse cocone map and the iterated-D image formula give lambda
and t. Exactness gives psi as a cokernel comparison. Cancellation proves its final
naturality square, including the endpoint transports.

Both modules compile cleanly in the sandbox (approximately four and five seconds).
`#print axioms` for both public theorems returns exactly `propext`,
`Classical.choice`, and `Quot.sound`. No time, heartbeat, or recursion limits were
raised. No existing definition, statement, or visibility was changed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.BigradedExactCouple.exactFunctor_couple`
(node `lem-sp-exact-functor-couple`).

The new theorem `CategoryTheory.BigradedExactCouple.exactFunctor_halfPlane`
(node `lem-sp-exact-functor-half-plane`) is also proved. Every private helper is
proved. No sorry remains in either delivered module; no hole is added anywhere.
Net holes closed minus added: one. This is a proof, not a decomposition with an
unproved remainder.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.CategoryTheory.DerivedCoupleExact`
- `Sheaf.CategoryTheory.ExactCouple`
- `Sheaf.CategoryTheory.ExactCoupleConvergence`
- `Sheaf.CategoryTheory.ExactCoupleMorphism`
- `Sheaf.CategoryTheory.Filtration`
- `WeilConjectures.Algebra.Homology.ExactCouple.Basic`
- `WeilConjectures.CategoryTheory.Abelian.Filtration`

Definitions remain available through the public statement import of
`HalfPlaneConvergence`. The iterated-image formula from
`lem-sp-derived-couple-exact` remains needed transitively for the large-page proof.

The planned node `lem-sp-couple-morphism`
(`Sheaf.CategoryTheory.ExactCoupleMorphism`) is not used by this proof.
The Mathlib preservation ingredients remain recorded under the existing leaf
`lem-sp-exact-functor-preserves-homology`.
Mathlib supplies preservation of exact short complexes, images, kernels and cokernels
directly, and the derived comparisons are constructed across the two categories.
No unit statement or realized unit proof step is bypassed. No other transitive
pruning is claimed.

The second reader also removed the redundant direct proof imports
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` from the item and
`Sheaf.CategoryTheory.FinitePageImageLift` from the new helper module. Image-lift
helpers remain available and used through `import all FinitePageGradedQuotient`.
The new module publicly imports `ExactCoupleConvergence`, which supplies its
statement vocabulary, instead of the larger `HalfPlaneConvergence` module.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated the helper theorem under a different private
name. The import-pruning checker correctly rejected that duplicate. The helper
theorem is now the single shared declaration.

## Forced adaptations

`lean/Sheaf/CategoryTheory/ExactFunctorHalfPlane.lean` (same C4 delivery):
the item could not reference its existing private `transport_square`, so its
visibility was changed from `private theorem` to `theorem`; the statement and
proof are unchanged. This is required for the item to reuse the existing
declaration after the duplicate is removed.

The planned same-category couple morphism route does not directly give comparison
across an exact functor between different categories. The explicit preservation
isomorphisms supply this bridge. No false statement or incorrect existing interface
was found. The large-page argument works uniformly for negative p by using the
cocone identity for incoming alpha iterates, avoiding a nonnegative-p restriction.

## New nodes

`lem-sp-exact-functor-half-plane`, module
`Sheaf.CategoryTheory.ExactFunctorHalfPlane`, records the proved infinite-page and
explicit large-page portion of original proof steps 4 and 6. It assumes the already
constructed finite-page and filtration comparisons, and proves their compatibility
with all limiting and large-page quotient identifications. Its public statement,
source and actual proof dependencies are recorded in its node. No new sorry or forced adaptation is needed.
`coord/changes/exact-functor-couple-helper-context.md` documents the private-helper
elaboration context commands flagged by the static interface checker; all existing
signatures and downstream behavior stay identical. LeanSearch was attempted and
reported unavailable; the other searches and source reads supplied the ingredients.

## Earlier second reading (a previous round; superseded)

1. Interfaces: compared the complete existing-module diff and mechanically compared
   the existing `exactFunctor_couple` signature byte for byte: identical. Its public
   import is unchanged; added imports are proof-only. No existing definition or
   declaration visibility changed. The new helper has its own module and node.
   The existing node differs only in `proof`, `proof_deps`, and `proof_origin`.
   Verdict: pass.

2. Proof: read both delivered modules and compiled them in dependency order with
   `lcompile.py --all`. No errors or warnings, no sorry, no forbidden declaration
   or compiler escape, and no raised limits. Scratch copies with `#print axioms`
   for both public theorems show only `propext`, `Classical.choice`, `Quot.sound`.
   The mapped couple, preservation isomorphisms, inclusions and filtration maps
   are explicit constructions. The chosen weak-convergence isomorphisms satisfy
   an existence-and-uniqueness theorem, and derived maps are fixed by their
   mono/epi restriction equations. No arbitrary witness of an unproved existence
   theorem is used as data. Verdict: pass.

3. New statement: the half-plane helper assumes the finite-page and filtration
   comparisons and proves only their limiting and large-page consequences; it is
   a strict part of the argument, not the original target renamed. It is fully
   proved, so there are no split-off holes. Checked page zero, negative p, p=0,
   q below the bound, and zero objects in the displayed inequalities and quotient
   argument. At r=0 the large-page bound forces p<=-1, so the graded quotient and
   E term both vanish. Its docstring explains the complete construction, and its
   node statement exactly matches the Lean signature. Independent LeanFinder,
   Loogle, Mathlib grep and repository searches found ingredients and existing
   private helpers, but no full transport theorem. Verdict: pass.

4. Route and pruning: finite comparisons use standard image, kernel and cokernel
   preservation. The infinite comparison is conjugated through the unique weak
   convergence comparisons; stable-page compatibility follows by cancelling the
   finite g epimorphism. The large-page proof uses cocone normalization and the
   prescribed incoming-alpha images, including negative p. Read
   `dag/units/sk-thm-properbasechange.json`: neither the item nor the removed couple
   morphism node is a realized unit statement or step, so the unit route stays.
   All old proof dependencies are accounted for: couple morphisms are unused,
   and derived-couple image formulas remain used transitively. Removed two
   redundant direct imports and narrowed the new module's public import.
   Verdict: pass after the simplifications below.

5. Nodes: checked sources, creation/blueprint metadata, the exact new Lean
   signature, and that each proof-dependency set is the union of its proof steps.
   Corrected the helper's dependency from the full half-plane convergence theorem
   to `lem-sp-half-plane-weak-convergence`, whose proved private helpers it uses.
   Recorded the new searches and reuse in its proof and proof origin.
   Verdict: pass after metadata repair.

Changes during second reading: removed the unused ExactFunctor import and the
redundant direct FinitePageImageLift import; replaced the new module's public
HalfPlaneConvergence import by ExactCoupleConvergence; deleted duplicate private
`page_zero`, `tower_stationary`, and `quotient_comparison` proofs and reused their
existing proved versions from HalfPlaneWeakConvergence, already accessible through
the proof-only `import all FinitePageGradedQuotient`; corrected the helper node
dependencies and updated this report. No existing public signature changed.

## Second reading by C4

1. **Interfaces and signatures.** I compared the delivered
`Sheaf.CategoryTheory.ExactFunctorCouple` module with the repository version. The
`exactFunctor_couple` declaration has the identical signature, including every
quantifier, equality, and bound. The new `ExactFunctorHalfPlane` module has a
separate declaration and the only visibility change is the required public
`transport_square` helper used by the item. No target statement or existing
repository declaration was weakened or otherwise changed. Verdict: pass.

2. **Proof and axioms.** Both delivered modules compile independently and in
sandbox import order with `lcompile.py --all`, without warnings, `sorry`, forbidden
commands, or raised limits. Scratch `#print axioms` checks for
`exactFunctor_couple` and `exactFunctor_halfPlane` show only `propext`,
`Classical.choice`, and `Quot.sound`. The constructions use explicit mapped
couples and image, kernel, cokernel, colimit, filtration, and stable-page
isomorphisms; no data is selected from an undetermined existence theorem. Verdict:
pass.

3. **Statements and nodes.** The helper node
`lem-sp-exact-functor-half-plane` is a strict limiting and large-page subargument,
with a statement matching its Lean declaration and no remaining hole. Its proof
steps and dependencies are true, needed, and recorded in the node. The original
node's statement is unchanged; its proof, dependencies, and origin now follow the
actual explicit construction. Existing searches found no duplicate full transport
theorem. Verdict: pass.

4. **Route and pruning.** The finite-page route constructs preservation through
images, kernels, and cokernels, then iterates the derived comparison. The helper
keeps the unit's convergence and filtration route, reuses the existing proved
weak-convergence and finite-page tools, and handles the stable and large pages,
including negative indices and zero cases. Removed direct imports and duplicate
helpers are unused by the final proof; the remaining proof-only imports are used.
No realized unit statement or step is bypassed. Verdict: pass.

5. **DAG agreement.** I checked that the original node's proof dependencies are
exactly the declarations used by the delivered proof, and that the helper node
contains the required source, proof, searches, creation metadata, Lean record,
and exact statement. The report names the one original hole closed, the helper
proved, and no holes added. Verdict: pass.

I changed only this report section during second reading; no Lean proof or node
content required repair after the checks above.
