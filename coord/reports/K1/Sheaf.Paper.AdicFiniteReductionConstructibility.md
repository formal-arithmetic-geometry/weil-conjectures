## What changed

The signature and public imports of
`AlgebraicGeometry.Scheme.adicFiniteReduction_constructible_cohomology` are unchanged.
Its proof now performs induction on the positive coefficient exponent. The base case
uses `hres.1`. At the successor, the proof uses the graded coefficient-filtration
triangle, obtains constructibility of its first term from the bounded residue, and
obtains constructibility of its third term by restricting the induction hypothesis
along the surjective quotient factor. The completed weak Serre argument then proves
constructibility of the middle term in every degree.

The weak Serre proof is written in the item's private namespace
`AdicReductionConstructibility`. It works for arbitrary Noetherian coefficients in
the independent coefficient universe. It transports finite-type locally constant
Serre closure through the constant-ring module equivalence, refines the actual global
stratifications by fibre products, and uses exact stratum inverse image to handle
kernels, cokernels and extensions. The derived homology-property instance supplies
the five-term exact-sequence argument. This generalizes the local-model proof used
in `FieldBoundedConstructibleTensor`; no field hypothesis is used or introduced.

Three new modules isolate distinct missing interfaces. `AdicCoefficientFiltration`
constructs the actual kernel module of the successive quotient, its constant
single complex, its derived tensor with the higher reduction, and the exact scalar
restriction of the lower reduction. All these definitions are concrete and contain
no holes or choices from unproved existence theorems. Its triangle assertion has no
constructibility or boundedness hypotheses. `AdicGradedLayerConstructibility`
concerns only that tensor layer, without asserting constructibility of a reduction.
`CoefficientSurjectiveRestrictionConstructible` is a general, degreewise scalar
restriction theorem for arbitrary surjections of Noetherian rings, without a
residue hypothesis, ideal-power tower or boundedness assumption.

The current integral-models unit and its first proof step are preserved. Sources
read: current blueprint `sk-lem-integral-models` and
`sk-lem-integral-models-stacks.proof.md`; Stacks proetale.tex Tag 09BR,
lemma-compare-truncations-constructible, Tag 09B5, lemma-constructible-serre;
sites-cohomology.tex Tag 094H, lemma-locally-constant-tensor-product.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.adicFiniteReduction_constructible_cohomology`
(node `lem-sfb-adic-finite-reduction-constructibility`). There are zero holes in
the assigned module. Its induction and private Serre lemmas are complete Lean proofs.

Added three named holes, each the sole theorem hole in its own new module:

- `AlgebraicGeometry.Scheme.adicFiniteGradedLayer_triangle`
  (`lem-sfb-adic-coefficient-filtration-triangle`). Remaining work is the exact
  coefficient sequence, its tensor triangle, and the unit/balancing endpoint comparisons.
- `AlgebraicGeometry.Scheme.adicFiniteGradedLayer_constructible`
  (`lem-sfb-adic-graded-layer-constructibility`). Remaining work is residue balancing,
  finite stratification and the bounded-above locally constant tensor computation.
- `AlgebraicGeometry.Scheme.coefficientSurjectiveRestriction_constructible`
  (`lem-sfb-coefficient-surjective-restriction-constructible`). Remaining work is
  the preservation of finite local models and exact cohomology transport.

This is a decomposition: one upper hole closed and three smaller holes added, not
a complete proof from standard axioms. Each new docstring and node gives its source
and full natural-language proof, including empty and degenerate cases.
The single-file compiler has verified the assigned proof against these declarations;
the delivery tool checks the final four-file packet as well.

## No longer needed

No original public import was removed, and no module is withdrawn.
`lem-sfb-discrete-noetherian-constructible-serre`
(`Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`) is no longer needed
for this proof route: its published pro-etale theorem is on the original small site
and does not directly give the predicate on the coefficient-sized site. The item
instead proves the needed arbitrary-coefficient Serre assertion from the already
proved finite local-model theorem and constant-ring equivalence. This is the only
original declared dependency pruned from the full route.

The other original dependencies are still needed transitively: the filtration
triangle retains reduction data and derived change of rings; the graded-layer
argument retains finite stratification pullback, pro-etale operations, tensor
pullback and locally constant tensor. They are named by the new nodes rather than
imported speculatively into the induction module. No claim is made that their
modules have become globally unused. Every added proof import serves the completed
Serre argument or one of the three interface statements.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no counterexample was found. Edge
cases checked in the constructions and proof plans: J=0, J=top, the zero ring,
the empty scheme, zero layer modules, and unbounded-below tensor cohomology.
The latter is why the layer conclusion asserts no lower bound or Tor interval.

The original dependency declarations do not by themselves expose the specific
coefficient-filtration triangle, the balanced graded-layer constructibility result,
or surjective scalar restriction on the independent coefficient-site predicate.
The original Serre theorem also uses a different site/universe presentation. The
completed local-model proof resolves the Serre presentation issue; the other three
interfaces are now explicit, independently provable obligations. None is the item
under another name: the first is purely a derived triangle without hres; the second
is only its graded tensor term; the third is generic scalar-restriction preservation.
The proof combining these steps is fully written and compiled.

The source's printed fixed tensor truncation cutoff in Tags 09BQ and 094H is not
used in the layer proof plan. Bounded residue supplies one finite common
stratification, after which the already stated bounded-above local tensor theorem
is applicable directly.

## New nodes

`lem-sfb-adic-coefficient-filtration-triangle`, module
`Sheaf.Paper.AdicCoefficientFiltration`: the actual graded-kernel tensor triangle,
with concrete definitions for its three named objects. It makes the first display
of Tag 09BR precise over the larger quotient ring.

`lem-sfb-adic-graded-layer-constructibility`, module
`Sheaf.Paper.AdicGradedLayerConstructibility`: the second display and tensor step of
Tag 09BR, using the common finite stratification and Tag 094H. This has no induction
hypothesis or higher-reduction constructibility conclusion.

`lem-sfb-coefficient-surjective-restriction-constructible`, module
`Sheaf.Paper.CoefficientSurjectiveRestrictionConstructible`: preservation of individual constructible cohomology sheaves under an arbitrary
surjective Noetherian coefficient map. Only preservation, the direction needed by the induction, is stated.

All new nodes inherit the chapter, unit and blueprint ancestor of the assigned
node. Search queries were run through msearch (LeanFinder, Loogle, Mathlib grep and
LeanSearch); project and blueprint searches found no exact duplicate. The existing
item node changes only its proof route fields. There are no change records because
no existing statement, definition or public interface changes.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
