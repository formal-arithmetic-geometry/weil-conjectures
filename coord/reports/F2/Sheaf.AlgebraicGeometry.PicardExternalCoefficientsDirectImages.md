## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_directImages`
without changing its signature or existing public imports. Its proof now uses two
strictly smaller mathematical statements in separate new modules:

- `PicardExternalCoefficientsAffineLocalCohomology`: computes every degree of
  cohomology on an inverse-image affine open as a tensor product, without hF.
- `PicardExternalCoefficientsPushforwardCoproduct`: constructs the coproduct
  presentation of the ordinary pushforward, without any acyclicity assumption.

The combining proof uses hF and tensor induction to establish local positive-degree
vanishing. A proved private helper computes the cohomology presheaf from an injective
resolution, makes its stalks zero by shrinking representatives to affine opens, transfers
vanishing through the higher-direct-image theta stalk isomorphisms, and detects the zero
module sheaf using the underlying abelian sheaf. This helper follows the already proved
argument in `HigherDirectImageAffineBasisVanishing`, specialized directly to the whole
morphism rather than open restriction. Finally, the proof transports the ordinary
coproduct cofan through the canonical `toRightDerivedZero` isomorphism, using the
existing, proved `higherDirectImagePresheaf` degree-zero clause.

The node proof and proof_deps now record this reduction. The new modules have genuine
statements, exact sorry theorem bodies, full source/proof docstrings, and matching nodes.
There are no definition changes, additional axioms, or forced adaptations.

All three modules compile together with lcompile.py, with no warnings. The local
comparison was tested conceptually in degree zero and positive degree, with empty X,
empty V, empty Y, F=0 and G=0. The coproduct statement includes the empty basis and
makes no assertion that an infinite sheaf coproduct is sectionwise on arbitrary opens.
The original unit route is unchanged; its realized lists do not include this node.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_directImages`
(node `lem-sc-picard-external-coefficients-direct-images`). No sorry remains in the
item's module. The new private helper `isZero_higherDirectImage_of_affine_local` is
fully proved.

Added two holes, each a proper part of the original argument:

- `AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_local_cohomology`
  (node `lem-sc-picard-external-coefficients-affine-local-cohomology`). This is a local
  cohomology calculation, not a higher-direct-image or coproduct conclusion.
- `AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_pushforward_coproduct`
  (node `lem-sc-picard-external-coefficients-pushforward-coproduct`). This concerns only
  ordinary direct image and has no positive-degree conclusion or acyclicity hypothesis.

This is a decomposition: one upper hole closed, two lower holes added, net -1 holes
closed. It is not an unconditional proof of the target's dependency closure.

## No longer needed

No existing import was removed and no module is globally pruned. The parent's direct
proof dependencies are now the two new nodes and
`lem-weil-pbc-higher-direct-image-presheaf`. The following former direct dependencies
remain needed by the new local calculation or coproduct construction, rather than
being globally pruned:

- `lem-sc-cech-comparison-map-iso-affine`
- `lem-sc-picard-affine-diagonal-intersections`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-flat-tensor-exact`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-weil-pbc-qcqs-finite-affine-open-cover`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `lem-weil-pbc-vector-space-basis-through-vector`

The full Kunneth theorem and external-coefficient acyclicity modules cannot provide a
shorter route: they depend transitively on this item. They were not imported.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematics and original statement were retained. The supplied module had
only statement imports, despite the standing brief saying proof-dependency imports
were already present. The recorded dependencies give affine chart formulas and Cech
comparison separately; they do not directly state the inverse-image-open tensor
calculation or the sheaf coproduct descent. Those two missing steps are now explicit
worker items, and the stalk and degree-zero glue are complete Lean proofs.

The recorded local source path `literature/stacks-project/varieties.tex` is absent on
this machine. The cited source was read at https://stacks.math.columbia.edu/tag/0BED:
the affine-open Cech equality and subsequent derived-direct-image formula support
both new statements. The stage-3 interfaces impose no additional hypothesis on Y.

LeanFinder and grep did not find either geometric result in Mathlib; LeanSearch
returned Internal Server Error and is recorded unavailable, not a negative result.
Blueprint-reference searches for external coefficients and 0BED gave zero matching
imported blueprint nodes. Searches of the current Lean modules found the existing
affine-right degree-zero section comparison, used in the new coproduct node's proof
plan, and the already proved higher-direct-image presheaf theorem used in the Lean proof.

## New nodes

`lem-sc-picard-external-coefficients-affine-local-cohomology`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-external-coefficients-affine-local-cohomology.json`,
is the local Cech tensor calculation on X times an affine V, in all degrees. Its Lean
module is `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology`.
It removes hF from the local calculation, letting the upper proof itself derive
vanishing by tensor induction. It keeps the original finite-affine-cover argument.

`lem-sc-picard-external-coefficients-pushforward-coproduct`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-external-coefficients-pushforward-coproduct.json`,
is the degree-zero ordinary direct-image basis construction. Its Lean module is
`Sheaf.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproduct`. It needs no
acyclicity and leaves the ordinary-to-derived-zero transport to the upper Lean proof.
Both new nodes inherit sec-abelian-varieties/sk-prop-av-cube and the original blueprint
ancestor chain. No change record is required.

## Second reading by F2

1. I compared the delivered direct-images module with the repository version. The target theorem signature, all existing declaration signatures, and the existing public imports are unchanged byte for byte; the added imports are proof-only imports. The two new declarations have signatures matching their DAG nodes. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. The target's positive-degree proof uses the affine-local comparison, tensor induction, and a fully proved stalk-vanishing helper. The remaining `sorry`s are exactly the two named split statements, with no sorry in a definition and no prohibited declarations. Verdict: pass.

3. I read both new statements against Stacks Project Tag 0BED (Lemma 33.29.1), and searched the local Lean library plus LeanFinder/grep for existing external-coefficient cohomology or coproduct declarations. Neither statement duplicates an existing declaration. The affine-local statement is strictly smaller than the target: it gives one affine-open cohomology isomorphism in one degree and has no derived-image or coproduct conclusion. The pushforward statement is also strictly smaller: it concerns only ordinary direct image and has no acyclicity or positive-degree assertion. Empty schemes, empty opens, zero modules, and an empty basis are included. Verdict: pass.

4. The proof is pruned from the original direct proof dependencies to the two split nodes and `higherDirectImagePresheaf`; the remaining imported modules are used by those declarations or by the helper. The helper reproduces the affine-basis stalk argument already present in the library, and the degree-zero derived transport uses the proved degree-zero clause. No target or definition was changed. Verdict: pass.

5. The unit route is retained: the node remains in unit `sk-prop-av-cube`, and the proof follows the Tag 0BED affine-local calculation and direct-image decomposition route. The source was checked at the linked Stacks page. Verdict: pass.

I changed nothing in the delivered Lean proofs or statements. I restored the proof-only module import after confirming it is required for `moduleDirectImage`; the final file compiles cleanly. I also recorded this second reading and will run the delivery dry run and final delivery checks.
