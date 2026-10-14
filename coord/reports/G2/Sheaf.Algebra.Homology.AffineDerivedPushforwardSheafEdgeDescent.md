## What changed

Proved `AlgebraicGeometry.existsUnique_affineDerivedPushforwardReverseComparison` without
changing its signature, the specified `affineKInjectiveReverseComparison`, any definition,
or any existing public import. Its proof now constructs the comparison on K-injective
complexes, descends it using fully faithful precomposition with their localization,
restricts to quasi-coherent derived objects, proves componentwise invertibility, and
proves uniqueness by transport along K-injective representative isomorphisms.

Added the proof-only import
`Sheaf.Algebra.Homology.AffineKInjectiveReverseComparisonIsIso` and its one-theorem module.
`AlgebraicGeometry.affineKInjective_leftExactHomologyComparison_isIso` is fully proved:
represent the derived object by a termwise tilde complex, lift its representative
isomorphism to a quasi-isomorphism into the K-injective complex, apply the existing
affine pushforward resolution theorem, and cancel in the naturality square for the
specified reverse homology comparison. Exactness on the termwise tilde complex follows
from the ordinary tilde/pushforward comparison, constructed locally from existing
unit, counit and pushforward/global-sections APIs. The existing public ordinary
comparison cannot be imported here because it depends on this descent module; no
new permanent definition of that comparison is introduced.

Updated the descent node's proof, dependencies and origin to match the Lean. The new
node records the completely proved affine component lemma. The affine derived
equivalence core is used as a generic representation tool from another unit;
this changes no unit statement or step (`sk-thm-picard-semicon.realized` is empty).
The existing Mathlib leaf `lem-weil-pbc-pushforward-tilde-spec` and the already proved
`lem-weil-pbc-pushforward-spec-global-sections` are also used as tools.
The derived representation tool is `new-affine-qcoh-derived-equivalence-core`. Sources read:
Stacks Tags 0AVW, 08D4, 06Z0 and 01I9, and the recorded Lean of every reused ingredient.

Both delivered modules compile cleanly in import order through `lcompile.py`:
the affine lemma in 43.6 seconds and the descent module in 12.9 seconds. The delivery
dry run performs the required axiom probes and final preflight.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.existsUnique_affineDerivedPushforwardReverseComparison`
(node `lem-pc-affine-derived-pushforward-sheaf-edge-descent`).

Also proved the new theorem
`AlgebraicGeometry.affineKInjective_leftExactHomologyComparison_isIso`
(node `lem-pc-affine-kinjective-reverse-comparison-isIso`).

There are no `sorry`s in either delivered module and no new holes. This is one original
hole closed, zero holes added, and zero statements split off with `sorry`.
Existing dependencies may still transitively use `sorry`; none is restated or changed.

## No longer needed

No existing import was removed: all original public imports supply the existing
interface, and the original private continuous-pullback import proves finite-limit
preservation. Removed an unnecessary public K-injective-computation import from the
new module before delivery; its actual statements and proof obtain the required APIs
from their other imports.

The descent proof no longer directly needs the three original planned dependencies
`lem-pc-affine-morphism-hi`, `lem-sc-affine-open-derived-truncation-comparison`, and
`lem-sc-left-exact-upper-truncation-comparison`, or direct proof imports of
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`,
`Sheaf.AlgebraicGeometry.AffineOpenDerivedTruncationComparison`, and
`Sheaf.CategoryTheory.LeftExactUpperTruncationComparison`. They are replaced at this
node by the proved affine component lemma, which reuses the existing affine resolution
and affine derived-equivalence results. Some old dependencies remain transitively
needed by those existing results; this report claims no global module pruning.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface correction was necessary. The DAG's direct
truncation argument was a valid plan, but the existing affine derived equivalence and
affine pushforward resolution theorem give a reusable route with all canonical-map
identifications proved by naturality. Only the node-level route changes.

The first compile could not find the recently landed
`LeftExactHomologyComparison.olean`. Work continued on independent uniqueness and
source inspection until the published build arrived; no dependency was duplicated
and no tool was changed.

Edge cases checked in the argument: arbitrary integer degree, unbounded complexes,
zero complex, zero rings and empty spectra. No boundedness, flatness of the ring map,
or termwise injectivity is assumed. Quasi-coherence is transported along the actual
homology images of representative isomorphisms. The chain map into I exists by
K-injectivity of the target, and the affine resolution theorem is applied only to a
termwise quasi-coherent source and a K-injective target. Every inverse used is the
inverse of a specified isomorphism or an explicitly established `IsIso` morphism.

## New nodes

`lem-pc-affine-kinjective-reverse-comparison-isIso`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-kinjective-reverse-comparison-isIso.json`,
records the single-component affine reverse homology comparison. Its module is
`Sheaf.Algebra.Homology.AffineKInjectiveReverseComparisonIsIso`; the theorem is proved
completely and adds no `sorry`. It is strictly a part of the descent argument:
it asserts invertibility of one explicit morphism on a K-injective complex, without
asserting a descended natural transformation, existence of a natural isomorphism, or
uniqueness. Searches were run through LeanSearch (unavailable), LeanFinder, msearch
grep and local rg. Blueprint searches found no duplicate of this specified comparison.
No change record or forced adaptation is needed.

## Second reading by G2

1. **Visible changes:** Compared both delivered modules with the repository versions. The
   existing declaration signatures are byte-for-byte unchanged; the added module and import
   are explicitly reported above.
2. **Compilation and hygiene:** Compiled both files in import order with `lcompile.py`.
   There are no `sorry`s, forbidden declarations, or hollow definitions in the delivered
   modules. The proof dependencies' remaining sorries are only imported dependencies.
3. **Statements and new node:** Checked the new component theorem against its Lean type and
   edge cases (arbitrary degree, zero rings, and unbounded complexes). It is a strict component
   result and is exactly as strong as required; its node, source, proof, and declaration agree.
4. **Pruning and route:** Checked the proof against the existing affine resolution and derived
   equivalence APIs. The descent proof follows the stated K-injective localization route; the
   unit route is unchanged. The listed superseded direct dependencies are no longer used.
5. **Axioms and delivery checks:** The required axiom probes and static preflight checks were
   run by the delivery tool; only permitted axioms occur in completed declarations.

Changed in this second reading: added this review record only; no Lean or DAG repairs were
needed.
