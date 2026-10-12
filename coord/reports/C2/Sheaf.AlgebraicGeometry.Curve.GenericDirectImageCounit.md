## What changed

Proved `AlgebraicGeometry.Etale.isIso_generic_direct_image_counit` from initiality of generic
base change on pointed étale neighbourhoods, the final-colimit comparison, the existing
`stalkRestrict_eq_counit`, and conservativity of geometric stalks. Its signature is unchanged.

Added `Sheaf.AlgebraicGeometry.Curve.GenericPointedEtaleCofinality`, with a complete
initiality proof. Its private equalization helper lifts the open agreement locus along the
preimmersion `V_K -> V`, preserving the marked point. Added
`Sheaf.AlgebraicGeometry.Curve.GenericPointedEtaleExtension` for the remaining geometric
extension step. This statement has no sheaf or coefficient parameter: it is strictly the
neighbourhood-extension part of the argument, not the counit under a new name.

Updated the existing node's proof, proof dependencies, and proof origin to the actual route.
Updated the theorem's proof docstring to describe that route. No definition, declaration
signature, or target statement changed. The unit record has no realized step at this node;
the affine-curve unit's route and statement are retained.

All three sandbox modules compile without warnings using the required compiler. The
extension lemma was checked on the empty-neighbourhood case (no geometric marking exists),
on a field scheme D (the identity case), and on arbitrary non-quasi-compact étale
neighbourhoods (only an affine neighbourhood of the marking is extended). No global
noetherian, quasi-compact, separated, characteristic, or torsion hypothesis is needed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.isIso_generic_direct_image_counit`
(node `lem-sc-generic-direct-image-counit`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.initial_generic_baseChangeNbhd`
(node `lem-sc-generic-pointed-etale-cofinality`) and its private equalization helper.

One hole added, and the only sorry in the delivery:
`AlgebraicGeometry.Scheme.exists_hom_generic_baseChangeNbhd`
(node `lem-sc-generic-pointed-etale-extension`). Its complete proof in words is in its
module and node: affine étale finite-presentation descent / clearing denominators, then
transporting the marking through the generic-fibre isomorphism.

This is a decomposition: one original hole closed and one smaller geometric hole added,
not a net decrease of holes. No sorry occurs inside a definition or private helper.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`, and node
  `lem-weil-pbc-unrestricted-strict-henselization-stalk`: the final-colimit comparison
  computes degree-zero stalks directly, without derived strict-local cohomology.
- `Sheaf.Paper.InverseImageStalkGerm`, and node
  `lem-weil-pbc-inverse-image-stalk-germ`: the existing `stalkRestrict_eq_counit` already
  contains the necessary inverse-image comparison and compatibility.

The direct imports of `WeilConjectures.SixFunctors.Finite.Stalk` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` were removed from the item as
redundant imports. Both remain transitively available and genuinely needed through the new
cofinality module. They are not claimed as pruned modules. The counit-germ and geometric
conservativity nodes remain needed. No other branch is claimed pruned globally; other
users can still reach the removed nodes.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the actual Lean glue from strict-local degree-zero derived
cohomology to the ordinary generic direct-image counit. Its stated dependencies did not
supply this specialization as an immediately applicable theorem. The direct pointed
neighbourhood argument makes the missing geometry explicit and avoids that glue.

The checked-out blueprint source file named by the node is absent on this machine.
The extension argument was checked against the online Stacks Project sources, Tags 02GH
(standard étale presentations), 01ZM (finite-presentation descent), and 07RP (descent of
étaleness). The source references and full argument are recorded in the new modules/nodes.
No mathematical defect in the original statement was found.

## New nodes

`lem-sc-generic-pointed-etale-extension`:
`lean/Sheaf/AlgebraicGeometry/Curve/GenericPointedEtaleExtension.lean`. This is the remaining
strictly geometric extension theorem. It requires no arbitrary witness in a definition.

`lem-sc-generic-pointed-etale-cofinality`:
`lean/Sheaf/AlgebraicGeometry/Curve/GenericPointedEtaleCofinality.lean`. Its initiality proof
combines the extension step with the complete equalization argument and Mathlib's
cofiltered initiality criterion. No new sorry is left in this module.

No change records are required: existing statement signatures and definitions are unchanged.

## Second reading by C2

1. I compared the delivered counit module with the repository version. The theorem signature is byte-for-byte unchanged; the two added modules and their node records are new, and no target statement or definition was altered.

2. I compiled all three modules with `lcompile.py --all`. The counit and cofinality proofs contain no `sorry`; the sole remaining `sorry` is the explicitly named extension theorem, with its node and proof docstring. The temporary axiom probes report only the permitted standard axioms plus `sorryAx` inherited from that open theorem.

3. I searched Mathlib and the local library for the extension and cofinality statements. The fresh LeanFinder query was “An etale scheme over a fraction field spreads out over a localization of the domain with prescribed geometric point”; its hits were étale-locus and localization lemmas, not pointed extension. Loogle on `AlgebraicGeometry.Scheme.fromSpecStalk` confirmed the preimmersion instance. Local `rg` found `etale_finite_data_descent` and `Etale.exists_stage_of_inverseLimit`, which require constructing an inverse system and do not directly supply the generic pointed extension. This remaining construction cannot be closed by a short application of either theorem. The cofinality helper is a genuine equalization argument using the agreement locus and preimmersion, rather than a restatement of the target.

4. The proof follows the recorded route: initiality gives the colimit restriction isomorphism, `stalkRestrict_eq_counit` identifies the counit stalk map, and conservative universe-lifted geometric stalks finish the argument. Removed strict-henselization and inverse-image-germ imports are no longer used; proof dependencies and imports match the code.

5. I checked the three node records: the original node keeps its statement and statement dependencies; its proof steps and dependency union record cofinality, the final-colimit comparison, the counit germ formula, and stalk conservativity. The new cofinality node records extension plus equalization and the cofiltered initiality criterion; the extension node records fraction-field identification and finite-data descent. Each new Lean signature matches its node verbatim. The unit route is retained: this item is below the affine-curve unit and does not replace any realized unit statement or step. I independently checked the extension statement hypothesis by hypothesis: D is any integral scheme, the marking is over its entire function field, and the output is a dominating pointed neighbourhood rather than an extension of all of W. An empty W has no marking; for a field scheme D the generic inclusion is an isomorphism; for non-quasi-compact or nonseparated W only a standard affine neighbourhood of the marked image is used. Stacks [02GH](https://stacks.math.columbia.edu/tag/02GH) supplies the standard étale neighbourhood, [01ZM](https://stacks.math.columbia.edu/tag/01ZM) supplies finite-presentation descent along affine qcqs stages, and [07RP](https://stacks.math.columbia.edu/tag/07RP) descends étaleness. Nonzero localizations of the affine domain satisfy the required affine/qcqs hypotheses. Clearing denominators must include the polynomial relation witnessing invertibility of the derivative, as the docstring requires. The pair of transported markings satisfies the fibre-product compatibility; no arbitrary witness is used in a definition. These checks pass without added noetherian, separation, finiteness, or torsion assumptions.

I changed only this report by adding the second-reading record. No Lean proof or node statement required repair.
