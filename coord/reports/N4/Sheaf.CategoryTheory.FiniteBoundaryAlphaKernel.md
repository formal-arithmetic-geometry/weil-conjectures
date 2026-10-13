## What changed

Proved `CategoryTheory.BigradedExactCouple.finiteBoundary_alphaKernel` in
`Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel`, with its signature and public imports unchanged.
The proof constructs an epimorphism onto the derived D term from the existing iterated image
formula, uses the existing finite cycle formula and derived-g comparison, and inducts on the
boundary recursion. Private, proved helpers handle index transports, the incoming differential
image, epimorphic refinement, and the pullback/image kernel chase.

Added proof-only imports of `Mathlib.CategoryTheory.Abelian.Refinements`,
`Sheaf.CategoryTheory.DerivedCoupleExact`, `Sheaf.CategoryTheory.FiniteCycleDerivedComparison`,
`Sheaf.CategoryTheory.FiniteCycleFormula`, and
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`.
Updated the existing node's proof, proof_deps and proof_origin to match this route. The unit
record has no realized steps affected by this change; the finite-boundary induction is retained.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.BigradedExactCouple.finiteBoundary_alphaKernel`
(node `lem-sp-finite-boundary-alpha-kernel`). No sorry remains in the delivered module.
Added zero holes and zero new nodes; nothing was split off.

This is a proof from existing declarations, including the existing, still-holed
`CategoryTheory.BigradedExactCouple.finiteCycle_derived_comparison`
(node `lem-sp-finite-cycle-derived-comparison`), which is not changed by this delivery.
It is not a claim that all transitive dependencies are already proved.
The zero-page case is proved separately; the successor proof works for all integer bidegrees
and makes no nonzero-object, positivity, regularity, or tail assumption.

Validation: the single delivered module compiles with lcompile.py, with no warnings or errors.
The delivery dry run performs the additional declaration/axiom probe and static preflight.

## No longer needed

No dependency of the original node is pruned: its exact-couple, convergence, image-prefix,
and refinement nodes are all used. No original import was removed.

The earlier sandbox's proposed `Sheaf.CategoryTheory.IteratedGPresentation` module and its
unproved `iteratedG_presentation` are unnecessary: the latter is now a fully proved private
helper in the item, using existing declared results. That scratch module was deleted and no
node or hole for it is delivered. The earlier attempt's broad
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject` import was also removed in favor of
Mathlib refinements and the image-composition lemmas actually used.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped with a new hole for iterated-g presentation and did not provide
a node or report for it. Its categorical successor-boundary chase was valid and compiled;
this session completed the presentation using the existing `finiteCycle_derived_comparison`
and `finiteCycle_formula`, avoiding the proposed new hole. No statement was changed.
The original DAG omitted these existing reusable declarations from its planned dependencies;
the delivered proof now names them explicitly.

## Second reading by N4

1. **Visible interface: pass.** Compared the complete delivered module against the
   repository version with `diff`. The existing theorem signature and docstring,
   namespace, universes, public section and public import are byte-for-byte unchanged.
   Added helpers are private proved theorems; the five added imports are proof-only.
   No definition or statement change, forced adaptation, or change record is needed.
2. **Proof and axioms: pass.** Compiled the module locally with lcompile.py without
   errors or warnings. Static inspection found no sorry or forbidden declarations
   in the delivered source and no added definitions. A scratch copy with
   `#print axioms CategoryTheory.BigradedExactCouple.finiteBoundary_alphaKernel`
   reports only propext, Classical.choice, Quot.sound and sorryAx. The latter is
   inherited from existing open dependencies, including finiteCycle_derived_comparison;
   this delivery closes its own one original hole and adds zero holes.
3. **Split statements: pass, none.** Nothing is split off. Read all private helpers:
   the presentation constructs e from an image epimorphism and a canonical image
   isomorphism, and c from unique factorization through a mono. The existential
   image-prefix families are prescribed by their recurrences; no arbitrary witness
   of an unproved mere-existence theorem is used as public data. The pullback chase
   uses actual epimorphic refinements and cokernel cancellation. Its kernel
   containment hypothesis is established by the induction hypothesis. The zero
   page has an invertible alpha iterate and bottom boundary; all successor transport
   identities hold for arbitrary integer indices, including negative indices, and
   the same argument covers zero objects and zero maps.
4. **Route and pruning: pass.** Read the imported finite-cycle formula and comparison,
   the image-prefix statement and proof, and the tower/alpha definitions. Searched
   the library by image, pullback, kernel, factorization and alpha-iterate terms, and
   searched Mathlib with msearch grep and leanfinder using a commutative-square/kernel
   query. No reusable public theorem replaces this boundary induction or its chase.
   Removal tests for each added import fail on a needed declaration, so all five
   are necessary. Every original proof dependency remains used. No module is pruned.
   The assigned unit sk-prop-av-pqf-finite has empty realized statement/step lists;
   this delivery neither changes them nor bypasses a realized unit step.
5. **Nodes: pass.** Compared the existing node JSON against the repository. Only
   proof, proof_deps and proof_origin change. The dependency list is precisely the
   union of the proof-step uses and names the existing image-prefix, finite-cycle
   formula, derived-g comparison, refinement, exact-couple and convergence nodes
   used in the code. The statement and Lean signature record remain unchanged;
   no new nodes require review.

Second reading changed only this report by adding the independent review and
its verification results. The Lean proof and node edits needed no repair.
