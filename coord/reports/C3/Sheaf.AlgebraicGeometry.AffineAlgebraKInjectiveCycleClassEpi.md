## What changed

Closed `AlgebraicGeometry.affine_algebra_kinjective_cycle_class_epi` without changing its
signature. On an affine inverse-image open, its section projection is the cokernel
projection followed by the canonical quotient comparison. Their epimorphy gives
surjectivity. An affine neighborhood inside each open then proves local surjectivity,
and forgetting modules to abelian sheaves reflects epimorphy.

Added `AffineOpenDerivedTruncationComparison`, proved from affine-open cohomology
vanishing, the existing unbounded bound, and the truncation triangle. Its proof follows
`AffineDerivedSectionsTruncationIso`, adapted to evaluation on any affine open without
requiring a Spec presentation or scalar transport. Added `KInjectiveSectionCycleComparison`
for the remaining general canonical-map identification. Both are proof imports of the
item. The item's original public imports and every existing signature stay identical.
Updated its node to the actual two-part route.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.affine_algebra_kinjective_cycle_class_epi`
(node `new-affine-algebra-kinjective-cycle-class-epi`). This is a decomposition, not a
sorry-free proof: it uses the new general bridge below.

Also proved `AlgebraicGeometry.affine_open_derived_truncation_comparison`
(node `lem-sc-affine-open-derived-truncation-comparison`), with no direct sorry.

Added one hole: `AlgebraicGeometry.kInjective_section_cycle_comparison`
(node `lem-sc-kinjective-section-cycle-comparison`). Its whole proof is `by sorry`.
It has no affine or quasi-coherence hypothesis: it separates identification of the
actual raw class map from the affine vanishing argument, which is proved separately.
There are no remaining sorries in the item, no other new holes, and no new definitions.
The net direct hole count is zero (one closed, one added).

Validation: all three sandbox modules compile in import order, without warnings.
The cokernel factorization is checked by Lean; no unrelated existential isomorphism
is used. The generic bridge covers zero complexes, arbitrary integer degrees and
zero objects; the affine argument also covers empty affine opens. It imposes no
boundedness or termwise injectivity assumption.

## No longer needed

No original import was removed. Removed unused tentative imports of
`Mathlib.Algebra.Homology.Embedding.CochainComplex` from both new modules.
The old direct proof dependencies removed from the item's `proof_deps` are:

- `lem-pc-affine-vanishing`;
- `lem-sc-module-cohomology-source-comparison`;
- `lem-pc-unbounded-derived-functor-cohomological-bound`;
- `lem-sp-derived-functor-single-identification`;
- `def-pur-kinjective-complex`;
- `prop-pur-kinjective-resolutions-exist`;
- `lem-sc-derived-k-injective-restrict-open`.

These are replaced as direct dependencies by the two new nodes. This does not
claim they are globally unreachable: affine vanishing and the unbounded bound
are still used transitively; K-injectivity and resolutions remain assumptions
of the generic bridge, and bottom-degree identification remains in its argument.
The new affine-open proof uses `pqf-lem-affine-vanishing` directly, instead of
repeating its source-cohomology comparison. Restricting K-injectives to an open
is unnecessary because the bridge applies directly to evaluation on the original
sheaf category. No original public import was removed and no globally pruned
module is claimed.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or changed interface. The original DAG's analytic ingredients
were valid, but its statements did not supply the identity with the actual cycle map.
The source library's affine K-injective cohomology comparison provides an existential
isomorphism; that statement alone cannot prove this particular map epi. The new bridge
records precisely the canonical-map calculation still needed.

The local Stacks TeX file is absent on this machine. The source was checked on the
[official Tag 0AVW page](https://stacks.math.columbia.edu/tag/0AVW) and
[official Tag 08D4 page](https://stacks.math.columbia.edu/tag/08D4).
LeanSearch returned an Internal Server Error; records say unavailable, not no match.
Whole-blueprint searches for affine cohomology, cycle class, cycle quotient, derived
affine sections, homology comparison and canonical comparison found no matching
blueprint statement. The unit's realized arrays are empty; no unit statement or step
was bypassed or modified.

## New nodes

`lem-sc-affine-open-derived-truncation-comparison`: proved affine-open evaluation version
of the canonical lower-truncation comparison. It avoids adding a new affine vanishing
or restriction-comparison hole.

`lem-sc-kinjective-section-cycle-comparison`: general left exact additive-functor bridge
from derived lower-truncation invertibility to invertibility of the actual cokernel
descent of the mapped cycle projection. A full mathematical proof is in its docstring
and node; the remaining work is formalizing that identity.

No change records or forced adaptations are needed; existing interfaces are unchanged.

## Second reading by C3

1. Compared every delivered module with the repository. The two auxiliary modules
   are new. The item's only existing theorem has a byte-for-byte identical
   signature; its existing public imports and documentation are unchanged. No
   definitions, target statements, change records or forced adaptations are added.
   Verdict: pass.
2. Compiled all three modules with `lcompile.py --all` in dependency order, with
   no errors or warnings. Inspected all declarations for forbidden constructs.
   The only direct sorry is the entire proof of
   `AlgebraicGeometry.kInjective_section_cycle_comparison`, listed above. A scratch
   copy with explicit `#print axioms` for all three theorems shows only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The affine truncation theorem
   is proved relative to existing open dependencies; no claim of a closed axiom
   closure is made. The scratch copy was removed. Verdict: pass as decomposition.
3. Read the bridge's full statement, docstring and node. It is a genuine
   canonical-map identification, separating that calculation from the affine
   cohomological vanishing proved in the other auxiliary theorem. It is not a
   renamed affine epimorphism assertion. Kernel preservation identifies mapped
   cycles; the quotient universal property identifies the displayed descent.
   Derived comparison on a K-injective complex, left exactness on the upper
   tail and bottom degree, and the assumed lower-truncation isomorphism give
   its invertibility. Checked zero complexes, the zero functor, exact functors,
   complexes concentrated in one degree, and arbitrary integer cutoffs; the
   affine application also includes empty affine opens. Repeated LeanFinder
   search with "left exact functor canonical homology comparison for K injective
   complex and derived truncation", and searched local homology, canonical edge
   and derived-functor sources. No matching general theorem was found. Loogle
   did not recognize `ShortComplex.LeftHomologyData.map`; this is not evidence
   of a mathematical absence. Existing bottom-cohomology and K-injective
   results supply parts, not the actual quotient-map identity. Closing that
   identity requires further formalization; no additional holes were added.
   Verdict: true, needed, and strictly one part of the affine argument.
4. Read the top-level proof, affine vanishing, the unbounded bound route, and
   the existing Spec/scalar-transport truncation proof. The direct affine-open
   evaluation argument avoids an extra restriction or scalar-transport bridge.
   The cokernel factorization and affine-basis local lift are checked by Lean.
   Public imports serve signatures; added proof imports are ordinary imports.
   The complete old direct dependency list is now recorded above. Read
   `dag/units/sk-thm-picard-duality.json` and its statement and step: no realized
   node is bypassed or changed (the realized arrays are empty), and the finite
   affine derived equivalence route above this item stays intact. Verdict: pass.
5. Compared the item's new proof steps and dependency union with the Lean;
   checked both new nodes' provenance, source, searches, chapter, unit and Lean
   records. Read official Stacks Tags 0AVW and 08D4: the affine comparison and
   N=1 truncation bound agree with the route. Corrected the new Lean records to
   contain the actual multiline signatures verbatim. Verdict: pass.

Second-reading changes: corrected the affine-open theorem's docstring summary
(which described upper/single truncation rather than its actual lower-truncation
projection); made both new node signatures verbatim; completed the old dependency
list and clarified direct versus transitive pruning. No Lean proof or signature
changed. One original hole is closed and one strictly intermediate hole is added:
net direct holes closed minus added is zero, a decomposition rather than a
sorry-free proof. No module is claimed globally pruned.
