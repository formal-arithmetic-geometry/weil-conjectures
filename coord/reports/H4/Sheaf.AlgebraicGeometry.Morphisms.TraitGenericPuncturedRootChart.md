## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.GaloisCover.trait_generic_punctured_root_chart`
with a complete Lean reduction to the regular-divisor Kummer theorem. The existing signature,
universe, public imports and docstring are unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.Morphisms.SmoothTraitAffineGenericOpen`,
`Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart`,
`Sheaf.RingTheory.RegularRingSmoothAscent`, and `Mathlib.RingTheory.TensorProduct.Quotient`.

The new affine generic-open theorem is fully proved from Mathlib: fractions over a DVR are
localization at powers of a specified uniformizer, an affine open supplies a smooth algebra,
and pullback open-immersion ranges identify its generic fibre with the principal open.
The proved private helper `smooth_trait_regular_quotient` gives regularity of the affine ring,
injectivity of multiplication by the uniformizer, and regularity of its quotient. The last
uses the tensor-quotient equivalence and smooth regularity ascent over the residue field.
The final proof transfers the unit group order and composes the two etale neighborhoods,
including the lifted point equality and the unchanged root-chart compatibility.

All three delivered modules compile together without warnings through lcompile.py. The unit's
trait route is preserved: regular closed divisor, prime-to-characteristic tameness, Kummer
charts. No data is defined by choosing a witness of an unproved existence theorem; all
existential witnesses are eliminated inside theorem proofs.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.GaloisCover.trait_generic_punctured_root_chart`
(node `lem-sbc-trait-generic-punctured-root-chart`). There are no sorries left in the item.

Also fully proved `AlgebraicGeometry.Scheme.smooth_trait_affine_generic_open`
(node `lem-sbc-smooth-trait-affine-generic-open`) and the private helpers
`fractionRing_away_uniformizer` and `smooth_trait_regular_quotient`.

Added exactly one hole:
`AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_punctured_root_chart`
(node `lem-sbc-regular-divisor-galois-punctured-root-chart`), whose proof is exactly
`:= by sorry` in its own module. It isolates the general 09EB/0EYG classification of a torsor
on a regular principal divisor complement, independently of the trait and smooth family.
Its complete argument and boundary cases are documented in the module and node.

This is a decomposition: one original hole closed and one lower hole added, net zero holes.
The regularity, uniformizer localization, affine neighborhood and assembly steps are proved.
The remaining geometric Kummer theorem is not asserted to be proved.

## No longer needed

None of the baseline imports or nodes was removed. The original node had no proof dependencies
and no proof-only imports to prune. Every final proof-only import is used. A redundant
`Mathlib.RingTheory.Smooth.Flat` import introduced during development was removed; this is
not a baseline pruning claim. No normality, normalization or density module is imported.

## Where the brief, the DAG or earlier work was wrong

The original node's non-elementary steps all had empty uses lists, so there were no existing
stated dependencies to turn directly into a proof. The delivery records the actual reduction:
a proved affine generic-open lemma, existing smooth regularity ascent, and one general
regular-divisor Kummer lemma. No existing statement or definition was changed or disputed.

The local literature checkout does not contain the Stacks sources mentioned in the general
project instructions. The cited source pages 0EYJ, 09EB and 0EYG were read directly online.
The blueprint-reference ancestry command returned None for this recently-created item;
the new nodes retain the item's explicitly recorded blueprint ancestor
`sbc-thm-spreading-finite-etale-galois` and identify its exact trait paragraph. Blueprint
searches for affine generic, regular divisor, generic fibre, Kummer and 0EYG found no duplicate
of either new statement. LeanSearch returned Internal Server Error and is recorded as unavailable.

## New nodes

`lem-sbc-smooth-trait-affine-generic-open` in
`dag/nodes/sec-smooth-base-change/lem-sbc-smooth-trait-affine-generic-open.json`, with module
`Sheaf.AlgebraicGeometry.Morphisms.SmoothTraitAffineGenericOpen`: the proved, group-independent
identification of an affine smooth trait neighborhood's generic fibre with D(pi_R).
It requires neither quasi-compactness nor quasi-separatedness nor a torsor.

`lem-sbc-regular-divisor-galois-punctured-root-chart` in
`dag/nodes/sec-smooth-base-change/lem-sbc-regular-divisor-galois-punctured-root-chart.json`,
with module `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart`:
the remaining general regular-divisor Kummer input. Its hypotheses are a regular ring,
a regular principal divisor, an invertible group order and an identification of the
pulled-back open with the divisor complement. They do not include a DVR or smooth trait
family. Unit equation, empty divisor, empty cover and disconnected torsors are covered.

No change records or forced adaptations are needed.

## Second reading by H4

1. **Interface: PASS.** Compared the delivered item with the repository using `diff -u`
   and independently checked that the entire existing theorem signature before `:= by`
   is byte-identical. Its existing docstring, public imports and universe are unchanged.
   The additions are four proof-only imports, one proved private helper, and the proof body.
   The other two modules are new; no existing definitions or other modules changed.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three modules
   through `lcompile.py --all`, without errors or warnings. Scratch copies with `#print axioms`
   checked every delivered theorem, including both private helpers. The affine generic-open
   theorem and both helpers use only `propext`, `Classical.choice`, `Quot.sound`. The item and
   the remaining regular-divisor theorem additionally use `sorryAx`, accounted for by the one
   named hole listed above. There is exactly one textual `sorry`, the whole proof of the
   regular-divisor theorem; no forbidden declarations, hollow definitions or arbitrary
   data extracted from unproved existence statements occur.
3. **Split statement: PASS.** Read [09EB](https://stacks.math.columbia.edu/tag/09EB),
   [0EYG](https://stacks.math.columbia.edu/tag/0EYG) and the trait paragraph of
   [0EYJ](https://stacks.math.columbia.edu/tag/0EYJ). `IsRegularRing` includes Noetherianity.
   At a generic divisor point its localization is a DVR; connected components of a finite
   group torsor have Galois stabilizers, so the ramification and inseparable residue degrees
   divide a unit group order. Thus the 0EYG tameness hypothesis holds. Etale refinement
   preserves regularity of the base and divisor and injectivity of multiplication by the
   equation. Checked the cases f a unit (split etale locally, g=1, exponents 1), R the zero
   ring (no point y), empty divisor, and disconnected torsors. An empty cover over a nonempty
   open is excluded by torsor surjectivity, but the allowed zero-factor presentation is
   harmless. The docstring and matching node give the complete source-based argument.
   Independent leanfinder, loogle and library grep searches found no existing classification
   or exact affine generic-open theorem; results are appended to the new nodes. The remaining
   hole is precisely the geometric Kummer step, strictly a part of the trait argument:
   localization, neighborhood selection, regularity and final composition are independently
   proved. Closing the geometric theorem is not a short repair.
4. **Route and pruning: PASS.** Read the unit `sk-prop-input-spreading`, including its
   `realized` fields (currently empty). Its trait route via the regular closed divisor,
   tame ramification and Kummer classification is preserved; no unit step is bypassed.
   The baseline item has no proof dependencies to prune, and all four added proof imports
   are used. Public imports supply types in the signatures. The tensor-quotient equivalence,
   flat regular-element ascent, mapped unit order and composed lifted-point equality were
   checked against the actual proof. No shorter existing Kummer input was found.
5. **Nodes: PASS after metadata repair.** The item's three dependency nodes are exactly
   the three recorded reduction steps. The new nodes have the required source, proof,
   search, creation, blueprint ancestry and Lean records; their recorded signatures agree
   with their declarations. Removed `def-sbc-normal-dominant-galois` and
   `def-weil-regular-scheme` from the affine generic-open node's `stmt_deps`: its statement
   uses neither torsors nor regularity. Added the independent searches to both new nodes.

Second reading changed only the new-node dependency/search metadata and this report.
No Lean proof, signature or definition needed repair. The delivery remains one original
hole closed, one new geometric hole added, net zero holes; it is a decomposition.
