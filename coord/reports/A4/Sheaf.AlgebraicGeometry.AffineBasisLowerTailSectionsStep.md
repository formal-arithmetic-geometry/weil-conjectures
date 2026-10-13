## What changed

Proved `AlgebraicGeometry.affineBasisLowerTail_sections_step_isIso` with its signature and
existing docstring unchanged in `Sheaf.AlgebraicGeometry.AffineBasisLowerTailSectionsStep`.
Added the proved private helper `evaluation_rightDerived_isZero`, which transfers vanishing
from source H on the restricted scheme to classical right-derived abelian sections.

The proof uses `OpenRestrictionModuleCohomology` and `ModuleCohomologySourceComparison`,
identifies the homology of the lower tail by the cutoff dichotomy, transports through the
single and shift comparisons, and applies the homology long exact sequence to the proved
lower-truncation step triangle. Added proof-only imports for open-restriction cohomology,
triangulated right derivation, unbounded/Plus compatibility, and derived t-structure homology.
Updated the existing node's proof route and dependencies. No definitions, interfaces, or
other modules changed. No new nodes or forced adaptations.

Read the source argument at Stacks [08D4](https://stacks.math.columbia.edu/tag/08D4), proof of
(2), and [0BKT](https://stacks.math.columbia.edu/tag/0BKT), along with the restriction
comparison [01E1](https://stacks.math.columbia.edu/tag/01E1). The shift endpoint calculation is
the N=1 calculation of 08D4, with the actual homology-sheaf hypothesis supplying acyclicity.
The unit's realized statement and steps are unaffected. Edge cases are covered directly:
when -n=a the zero branch applies, when n=1-i the first positive degree is 1, and empty V
uses the same comparison isomorphisms without any nonemptiness assumption.

Searches: LeanFinder on positive derived sections and the triangle endpoint criterion
returned generic complex/truncation facts, with no specialized theorem; Loogle on
isIso_homologyMap_mor₂ returned no hits; grep found no Mathlib rightDerived/truncLT theorem.
Local library search found the proved open-restriction comparison and the analogous
DerivedFunctorTruncationStabilization proof, whose single/shift transport was adapted.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.affineBasisLowerTail_sections_step_isIso`
(node `lem-sc-affine-basis-lower-tail-sections-step`). Added zero holes. No `sorry` remains in
the delivered module. The private helper `evaluation_rightDerived_isZero` is also proved.
This is a proof from existing library declarations, not a decomposition into new holes;
`#print axioms AlgebraicGeometry.affineBasisLowerTail_sections_step_isIso` reports only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` dependency.
Single-file compilation succeeds without warnings.

## No longer needed

Removed the proof-only import `Sheaf.Algebra.Homology.KInjectiveRestrictOpen` and the direct
proof dependency `lem-sc-derived-k-injective-restrict-open`. Its unbounded restriction
argument is unnecessary for this item: the existing classical open-restriction cohomology
comparison already identifies the positive derived sections of a single module.
No other original import is removed. The lower-truncation triangle and source comparison
remain needed. No claim is made that KInjectiveRestrictOpen is unused elsewhere in the
project; this pruning is specific to this theorem's proof route.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically correct. Its direct K-injective restriction dependency can be
replaced by the already proved open-restriction module-cohomology comparison. Only W=V
from the affine-basis hypothesis is needed for the successive-step theorem; the complete
hypothesis and statement remain unchanged. Local literature files named in the node were
not present on this machine, so the source tags were read on the Stacks Project website.

## Second reading by A4

1. Compared the delivered Lean module and node with the repository versions. The theorem
   signature, definitions, and existing declarations are unchanged; only proof imports,
   proof text, and the node's proof metadata differ. Verdict: pass.
2. Compiled the module and all sandbox modules with `lcompile.py`; there are no errors,
   warnings, `sorry`s, forbidden declarations, or new axioms. The target's proof uses only
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the private helper and the updated proof route against the open-restriction and
   source-comparison declarations. The helper is a true vanishing transport statement, and
   no split-off statement or new node was added. Verdict: pass.
4. Checked pruning and the shortest available route. The K-injective restriction import and
   dependency are no longer used; the lower-truncation triangle, source comparison, and
   right-derived transport remain required. The unit's realized statement and steps remain
   represented. Verdict: pass.
5. Compared the node's proof, dependencies, and origin with the Lean proof. Every listed
   dependency is used by the proof or its helper, and the removed dependency is recorded in
   `No longer needed`. Verdict: pass.

Changed only the proof implementation, proof-only imports, node proof metadata, and this
second-reading record. No statement, definition, or new node was changed.
