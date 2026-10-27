## What changed

The statement of `AlgebraicGeometry.Scheme.completedKoszulQuotientRoosAugmentation`
is unchanged. Its proof now constructs the natural map of the actual product/cofiber/shift
models from a normalized strict tensor tower augmentation. Naturality follows from the
product functor, the strict augmentation square, and composition of cofiber maps.
The source comparison uses identity maps on both products. The unit proof takes product
projections of the finite quotient equations and uses the actual cofiber inclusion,
so the second coordinate stays zero as a strict equation of complexes.

For quasi-isomorphy, the proof transfers eventual vanishing of strict cone transitions
through derived evaluation, applies the existing ringed strict derived-limit theorem,
and uses the existing exact-products Roos comparison. Exactness of countable products
comes from the public pro-etale theorem; no shared interface is changed.

Two new modules isolate finite augmentation and strict tensor cone vanishing. A third
new module contains the fully proved pro-zero-cone-to-Roos comparison. Their
supporting tower, quotient unit and total summand definitions are explicit functors
and maps. No data definition chooses an arbitrary witness from an unproved theorem.
The finite augmentation statement specifies uniqueness; the main theorem eliminates
that existence statement inside its proof.

Remote compilation checked all four modules: the proved Roos bridge in 11.1 seconds,
the finite augmentation statement in 43.8 seconds, the tensor cone statement in
8.7 seconds, and the main assembly in 55.7 seconds. The latter was measured with
profiling enabled; both development options are removed from the delivery. No
transparency setting or time limit was relaxed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.completedKoszulQuotientRoosAugmentation`
(node `lem-weil-pbc-completed-koszul-quotient-roos-augmentation`).
This is a decomposition, not an axiom-free completion: one upper hole is replaced
by the following two strictly smaller holes, each in its own module.

- `AlgebraicGeometry.Scheme.completedKoszulTensorQuotientAugmentation`
  (`lem-weil-pbc-completed-koszul-tensor-quotient-augmentation`): finite strict natural
  augmentation with its total summand formulas. It has no K-flatness or Roos conclusion.
- `AlgebraicGeometry.Scheme.completedKoszulTensorQuotientConeProZero`
  (`lem-weil-pbc-completed-koszul-tensor-quotient-cone-pro-zero`): eventual derived-zero
  cone transitions after tensoring with K-flat P. It has no Roos or limit conclusion.

The item module contains zero remaining holes; the delivery adds exactly two.
All private assembly lemmas are proved, including the strict unit equation. The new
`AlgebraicGeometry.Scheme.completedAdicRoosMapQuasiIsoOfProZero` is also fully proved;
it transfers derived pro-zero cones to quasi-isomorphy of the concrete Roos map.

## No longer needed

No original public imports are removed and no module is withdrawn. The original
Noetherian Koszul augmentation, completed constant reduction and K-flat preservation
dependencies are now used by the smaller finite/tensor-cone statements. They are not
claimed as globally pruned. The root's proof dependencies are updated to the actual
assembly, including both new nodes. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically appropriate, but its stated dependencies
do not directly provide the strict augmentation in these particular exterior completed
coefficient models. The existing AdicResidue augmentation and tensor-cone theorems
use a different coefficient-slice presentation and dual Koszul model. Their signatures
were inspected; they cannot simply be applied to the recorded functors. The two new
statements expose exactly the finite model compatibility and tensor cone steps.

The blueprint ancestor command returned `None` for the root's old string-form
`blueprint.from`. The new nodes explicitly name the existing blueprint ancestor
`prop-weil-pbc-koszul-reconstruction`, order 1248. The current blueprint was searched
for Koszul statements, and the newest unit text was read. No unit record is edited.

## New nodes

`lem-weil-pbc-completed-adic-roos-pro-zero-cone` is proved without a new hole. It packages
the exact countable products, derived evaluation naturality and existing Roos comparison.
After replacing the higher tensor-functor presentation by the actual tensor tower,
profiling showed no single remaining definition bottleneck, but the assembled file
still took 61--63 seconds. This self-contained proved comparison was moved to its own
module so each file can compile within 60 seconds. No time limit or transparency
setting was weakened.

`lem-weil-pbc-completed-koszul-tensor-quotient-augmentation` records the actual strict
tensor tower and its unique normalized augmentation before products. Its sources are
the degree-zero Koszul quotient construction in Stacks 091N and 099M. The unit and
vanishing formulas uniquely determine every total tensor component, including r=0,
I=A, the zero ring and the empty scheme.

`lem-weil-pbc-completed-koszul-tensor-quotient-cone-pro-zero` records the transport of
the algebraic pro-zero augmentation cone through constant realization, completed scalar
extension, and K-flat total tensor. Its sources are the Artin--Rees argument in Stacks
091N and its use in 099M. The natural-language proof specifies the strict tensor-cone
sign and transitions. Neither node repeats the Roos augmentation theorem.

LeanFinder, Loogle, grep and LeanSearch queries were run and their actual results
recorded in both nodes. There are no change records: no existing declaration signature,
definition, instance, attribute or public import is changed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
