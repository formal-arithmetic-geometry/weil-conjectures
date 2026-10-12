## What changed

Proved `AlgebraicGeometry.Scheme.isPullback_affine_local_functionField_diagonal` with its original signature and visibility. Added the proof-only import `Mathlib.RingTheory.KrullDimension.LocalRing`. All original public imports remain. Updated the node proof and proof dependencies to the direct Mathlib route.

The proof constructs the fraction field as a principal localization using the dimension-one radical criterion, establishes the affine-chart/stalk pullback by equality of open ranges, obtains the tensor-spectrum product cone from the coproduct of rings, and constructs the diagonal-square limiting cone explicitly. It uses no Sheaf theorem or new intermediate statement. The Noetherian hypothesis is preserved, although this argument does not need it.

Source checked: Stacks Project Tag 09NB, opening paragraph, https://stacks.math.columbia.edu/tag/09NB. The local literature file named by the node is absent on this machine, so the source was read on the Stacks website. The unit record `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology`, with no proof steps; this local calculation does not bypass a unit statement or route.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Scheme.isPullback_affine_local_functionField_diagonal` (node `lem-sc-affine-local-function-field-diagonal-pullback`). No holes remain in the module; none were added or split off. This is a full proof from Mathlib, not a decomposition.

The single-file compiler passed. The delivery dry run checks the declaration's axioms and unchanged signature as well.

## No longer needed

No original imports were removed. The following planned dependencies are unnecessary for this proof and were removed from the node's proof dependency list:

- `lem-sc-local-domain-dim-one-principal-localization-fraction-field`, module `Sheaf.RingTheory.LocalDomainDimOnePrincipalLocalization`: the principal localization instance on K follows directly from Mathlib's dimension-one radical criterion and localization comparison.
- `lem-weil-pbc-spec-local-ring-canonical-morphism`, module `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`: only the closed-point equality and stalk-specialization compatibility are needed, and Mathlib proves both directly. The larger package, including module stalks and flatness, is unused.
- `lem-weil-pbc-open-immersion-base-change`: there is no base-changed open immersion to construct; Mathlib's open-range pullback criterion supplies the geometric pullback.
- `lem-weil-pbc-fibre-product-affine-spectra`: `pullbackSpecIso` is unnecessary. The coproduct of rings over integers gives the required binary product cone directly, in every universe.

The two Sheaf modules above need not be imported by this module. This is local pruning; no claim is made that other target branches cease to need them. Integral-stalk fraction-field facts and the principal-localization open-immersion fact remain as Mathlib-backed node dependencies.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The planned tensor-product step suggested a terminal integer spectrum with a universe lift; the ring coproduct universal property makes that construction unnecessary. The canonical-stalk-properties package and localization-isomorphism theorem are much larger than the interfaces this proof needs.

Searches used the supplied msearch tool (LeanFinder and Loogle), plus ripgrep in the source library, statement library, Mathlib, and DAG. LeanFinder returned supporting geometric results but no exact theorem; Loogle did not recognize the unqualified query identifier. Direct source searches found the precise Mathlib interfaces used above. No new nodes or forced adaptations.

## Second reading by W2

1. Interface: PASS. Compared the sole delivered Lean module with the repository by diff and separately checked the theorem signature byte for byte. Its hypotheses, conclusion, universe, name, and public visibility are unchanged. There are no definitions, new declarations, adapted modules, or change records. The added transparency option affects elaboration only.
2. Proof: PASS. Independently compiled the module with lcompile.py, without errors or warnings. Compiled a scratch copy with `#print axioms AlgebraicGeometry.Scheme.isPullback_affine_local_functionField_diagonal`; the result is exactly `propext`, `Classical.choice`, and `Quot.sound`. Checked the complete file for sorry and prohibited declarations/options: none. Reviewed the localization divisibility argument, the two implications of the open-range equality, the tensor projections, and all three obligations of the limiting cone. No data comes from an unproved existence theorem.
3. Split statements: PASS, vacuous. No statements or nodes were split off, and no holes were added. The dimension-one assumption excludes fields; nonemptiness of U supplies the generic point; x outside U excludes the closed prime. These are exactly the edge cases the proof uses.
4. Route and pruning: PASS. Independently read Stacks Tag 09NB, checked the retained Mathlib-backed dependencies, searched the library for function-field/stalk pullback statements, and ran an additional Loogle search for IsPullback and prod.lift (no hits). Mathlib's pullback_map_diagonal_isPullback concerns chosen relative pullbacks and would require additional product identifications here; the explicit cone is correct and is retained. The three original public imports provide objects, arrows, and scheme product instances occurring in the signature; the added KrullDimension.LocalRing import is proof-only. All four old proof dependencies no longer used are listed under No longer needed. The unit sk-thm-curveestimate realizes thm-sc-proper-cohomology and has no realized steps: no unit route is bypassed.
5. Metadata: PASS. Compared the node JSON with its repository version: only proof, proof_deps, and proof_origin changed. The two retained dependencies match the fraction-ring/domain instances and the principal-localization open immersion actually used. The four proof steps accurately describe the Lean construction, and their uses have exactly the stated union. No new nodes require validation.

Second reading changed only this report by recording the independent checks; the Lean proof and node metadata needed no repair. Closed one original hole, added zero, split off zero.
