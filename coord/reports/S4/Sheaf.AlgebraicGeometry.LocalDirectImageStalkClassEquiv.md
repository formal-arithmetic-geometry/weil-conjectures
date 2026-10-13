## What changed

Proved the original declaration `AlgebraicGeometry.localDirectImage_stalk_cohomology_equiv`
in `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassEquiv` from one strictly smaller
scalar compatibility theorem. Its signature and existing docstring are unchanged.

Five fully proved private helpers establish top-germ bijectivity when every neighborhood
is top, apply this to a local spectrum, prove the actual sectionCohomologyTheta component
on top invertible using sheafification stalk invariance, prove the top germ into the
pushforward stalk bijective, and prove the specified additive class map bijective.
The final proof builds a LinearMap with this same additive map and uses
LinearEquiv.ofBijective. The equation specifying its function is reflexivity.

Added `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassLinear` for scalar compatibility.
Added a proof-only import of that module and of `Mathlib.Topology.Sheaves.Sheafify`.
Updated the existing node's proof, proof_deps and proof_origin to the implemented route.
Read Stacks Tags 01E4 and 02OD. The local identification used here requires none of the
properness/coherence/Noetherian assumptions of the full formal-functions theorem.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.localDirectImage_stalk_cohomology_equiv`
(node `lem-weil-pbc-local-direct-image-stalk-cohomology-equiv`).
There is no sorry in the item's module or its private helpers.

Added one hole:
`AlgebraicGeometry.localDirectImage_stalk_class_smul`
(node `lem-weil-pbc-local-direct-image-stalk-class-smul`), in the new module
`Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassLinear`.
It asserts only scalar compatibility and does not assert injectivity, surjectivity,
or existence of an equivalence. The entire bijectivity argument is proved independently.
Thus this is a reduction with one upper hole closed and one smaller hole added,
not a complete proof free of sorry dependencies; the net hole count of this delivery is zero.
The edge cases p = 0, zero modules, and empty local base change use the same linear maps.

Validation: the two delivered modules compile through lcompile.py in import order.
The delivery dry run performs the declaration axiom probes and the stage-3 preflight.

## No longer needed

Removed proof imports:
- `Sheaf.Algebra.Homology.ModuleStalkExact`:
  `lem-weil-pbc-module-stalk-exact` is not needed. Exactness of closed-point evaluation
  is replaced by the explicit stalk/germ square and sheafification-unit invariance.
- `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`:
  `lem-weil-pbc-spec-local-ring-canonical-morphism` is not needed by this proof.
  Mathlib's preimage_eq_top_of_closedPoint_mem and fromSpecStalk_closedPoint suffice.
  The remaining scalar lemma's proof sketch uses Mathlib's canonical germ/stalk formulas.

Retained the public class-map import, since the original statement names that map.
Retained the exact-functor/homology Mathlib dependency and added the existing
`lem-weil-pbc-stalk-sheafification-space` Mathlib leaf to reflect the actual proof.
No unit statement or realized unit step is bypassed. Pruning here refers to this module's
proof route; other target paths may still require the two removed modules.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's proposed invocation of module-stalk exactness
was unnecessary: directly comparing theta at the closed point proves its top component
invertible. The canonical-morphism package was likewise unnecessary for the inverse-image
open calculation. The exact-functor node is a Mathlib leaf, not a Sheaf module to import.

The first local compile could not find LocalDirectImageStalkClassMap.olean in the shared
snapshot. I tested the available local-spectrum argument in the sandbox scratchpad while
waiting. The snapshot subsequently refreshed and compilation against the actual class
map succeeded. No dependency was recreated or changed to work around that delay.

LeanSearch was unavailable (Internal Server Error); LeanFinder and source/DAG searches
found no existing theorem of scalar compatibility for this specified map.

## New nodes

`lem-weil-pbc-local-direct-image-stalk-class-smul`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-local-direct-image-stalk-class-smul.json`,
states scalar compatibility only. Its single theorem is in
`lean/Sheaf/AlgebraicGeometry/LocalDirectImageStalkClassLinear.lean`.
The docstring and node give the germ representative, normalized scalar identification,
linearity of the section and homology comparisons, and final module germ calculation.
No existing interface was changed and no change record or forced adaptation is needed.

## Second reading by S4

1. **Interfaces — pass.** Read both delivered modules and diffed the existing module
   against the repository. The signature of
   `AlgebraicGeometry.localDirectImage_stalk_cohomology_equiv` is byte-for-byte identical
   (also checked by extracting its text through `:= by`), as is its existing docstring.
   Only private proved helpers, proof imports and the proof body were added there.
   The new scalar theorem has a separate module and node; no existing definition,
   public import, target, hypothesis or conclusion was changed. No change record is needed.

2. **Proof and axioms — pass as a decomposition.** Both modules compiled in import order
   through `lcompile.py`. Read the five helper proofs: germ equality and representatives
   prove the first two, the counit and sheafification-unit stalk square prove theta
   invertible on top, inverse-image opens make pushforward restrictions invertible,
   and the last helper composes the three bijections of the actual class map.
   Scratch-copy `#print axioms` checks of every helper show exactly `propext`,
   `Classical.choice`, `Quot.sound`. The final theorem and scalar theorem additionally
   show `sorryAx`, as reported. The only delivered hole is the named public scalar
   theorem; no definition contains a hole and no forbidden declaration or attribute occurs.
   `LinearEquiv.ofBijective` uses the actual additive map, with pointwise equality by rfl;
   there is no data selected from an unproved mere existence theorem.

3. **Split statement — pass, with proof-sketch repair.** Read the scalar theorem's
   docstring, node, actual `localDirectImage_stalk_class` construction and
   `resolutionSectionClass`/`sectionCohomologyTheta` definitions. The source action is
   precisely restriction along Gamma-Spec.inv followed by f'.appTop; the target action
   is the module stalk action. Read Stacks
   [01E4](https://stacks.math.columbia.edu/tag/01E4), Lemma 20.7.3, and the local equality
   in the proof of [02OD](https://stacks.math.columbia.edu/tag/02OD), Lemma 30.20.7.
   The formal-functions assumptions in 02OD are not used for this local comparison.
   Checked Mathlib `Scheme.germ_stalkClosedPointTo`,
   `Scheme.stalkClosedPointTo_fromSpecStalk` and `PresheafOfModules.germ_smul`:
   they give the normalized scalar and final germ identities claimed in the sketch.
   At p = 0 the same comparisons apply; a zero sheaf or empty X' gives zero section
   complexes and zero cohomology. No nonemptiness of X' or positive-degree assumption
   is used. Scalar compatibility alone asserts no bijectivity and is strictly less
   than the item, whose bijectivity has been proved without any holes.
   Independent LeanFinder query about homology comparisons and scalar restriction found
   only restriction-of-scalars naturality lemmas, not this class-map theorem; Loogle
   could not resolve `ShortComplex.homologyMap_mapNatTrans`. Searched `lean/`, upstream
   `WeilConjectures/` and Mathlib homology sources for the specified class/comparison
   names and scalar/homology compatibility: no existing theorem closes this hole.
   Expanded the sketch to use multiplication chain endomorphisms and naturality of
   each exact-functor homology comparison, rather than merely saying it respects scalars.
   Closing all these transport identities is not a few-minute proof; retained the
   true, explicitly named smaller hole.

4. **Route and pruning — pass.** The direct germ square and Mathlib sheafification
   invariance are a valid route below the unit level. Imports are used: the class-map
   module supplies the public signature; Sheafify supplies the stalk-unit isomorphism;
   ClassLinear supplies only the proof's scalar equation. Compared all four original
   proof dependencies with the new route: the two retained ones are the class-map
   definition and exact-functor cohomology; both removed nodes/modules are listed
   under No longer needed. Read `dag/units/sk-thm-p1.json`, including its `realized`
   statement and all four steps. Neither removed node is a realized unit step, and
   this local comparison changes none of the curve, henselian or geometric-stalk route.

5. **DAG agreement — pass after repair.** Read both delivered nodes. The item's three
   proof steps match the actual helpers and final LinearMap construction, and their
   uses have exactly the recorded union in proof_deps. The new node has its source,
   complete scalar argument, search records, created/blueprint/chapter/unit metadata
   and verbatim Lean signature. Added the existing Mathlib exact-functor cohomology
   node to step 2 and proof_deps of the scalar node: its stated naturality is the fact
   used to commute scalar chain endomorphisms through homology comparisons.

Second reading changed only the new scalar theorem's natural-language proof sketch,
its node's step 2 and proof_deps, and this report. The existing Lean proof and signatures
were left as written. One original hole is closed and one strictly smaller hole remains;
this is a decomposition with net zero holes, not a sorry-free proof of the item.
