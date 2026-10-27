## What changed

Replaced the hole in `Sheaf.Paper.CompactSupportCoefficientExchangeInvertible`
with a proof from a single finite evaluation lemma. The existing theorem statement,
public imports, and all shared definitions are unchanged.

The proof transports the given base-field unit along global sections and residue
field evaluation to supply the residue-field invertibility instances required by
the existing realization API. It then uses the normalization equation from
`FrobeniusExchange.compactRealization_existsUnique`: cancel the isomorphisms
surrounding each evaluated operation-reduction counit, then apply joint
conservativity to the actual system morphism. Next, construct Noetherian instances
for the middle scheme and Y. The input reductions are bounded constructible by
K.property. The restricted integral scalar-extension functor supplies bounded
constructible scalar reductions; the actual `scalarReductionIso` identifies these
with evaluations of scalar extension of the whole input system. Transport the two
constructibility predicates across the specified isomorphisms and apply the finite
lemma. Joint conservativity makes the system mate invertible. Finally, explicitly
unfold the source comparison and coefficient exchange into the realization
isomorphism, the image of the reconstruction counit, the image of the system mate,
and the inverse scalar-reduction isomorphism. Functorial preservation and composition
of isomorphisms close the original theorem.

Added the private proof imports
`Sheaf.Paper.CompactSupportSystemScalarFiniteInvertible` and
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`, and updated the assigned
node's proof route to match these Lean steps.

Remote single-file compilation accepted both modules; the completed assigned proof
compiled in 7.8 seconds. Temporary profiling options were removed before delivery.
The delivery command runs the final compilation, warning checks and axiom probe.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.sfCompactSupportCoefficientExchange_isIso`
(node `lem-sf-compact-support-coefficient-exchange-invertible`). There is no sorry
left in the assigned module.

Added one hole:
`WeilConjectures.FrobeniusExchange.systemCompactScalar_evaluation_isIso`
(node `lem-sf-compact-support-system-scalar-finite-invertible`), in its own module.
This is a decomposition: one original hole closed, one finite lemma added, net zero.
The theorem proved here still depends on the existing admitted library declarations.

The remaining lemma is strictly the single-index finite step. It applies to an
arbitrary derived system N with two explicit bounded constructibility hypotheses
at n. It has no integral constructible category, completeness, common interval,
field of definition, reconstruction counit, or total inverse limit in its assertion.
The proof above supplies those finite hypotheses and independently proves both the
reconstruction step and the passage from finite evaluations to whole systems and
then to the original realized coefficient exchange. Thus the new lemma is not the
original exchange under a new name or a repackaged hypothesis.

## No longer needed

No original public import was removed, and no module is withdrawn. The additional
proof imports are precisely those used by the proof. The unit
`sk-def-sf-operations` has no realized statement or step to bypass.

The following former direct proof dependencies of the assigned node are no longer
directly needed; they are retained in the finite lemma's argument where indicated:

- `lem-weil-pbc-finite-ring-constructible-derived-origin`,
  `det-pe-classical-sheaves-modules`,
  `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
  `lem-finite-compact-support-scalar-transport`, and
  `lem-coef-semilinear-derived-sections`: retained below the new finite lemma.
- `lem-sf-compact-support-restriction-of-scalars`: the finite transport theorem
  already includes the specified restriction comparison; no separate direct use.
- `lem-pur-coefficient-extension-reduction-model`: the assigned proof uses the
  already packaged whole-system `scalarReductionIso` and its normalization.
- `lem-weil-compact-support-reduction-tower-functor`: the proof uses the existing
  literal system compactification operation and its normalized realization, so no
  separately chosen tower functor is required.
- `lem-coef-normalized-dvr-effectivity`,
  `lem-sf-integral-compact-support-constructible`,
  `lem-weil-strict-roos-comparison`, and
  `lem-weil-proetale-countable-products-exact`: cancellation in the published
  compactRealization projection equation proves reconstruction-counit invertibility
  directly. Its normalization and finite reduction isomorphisms already package
  the needed realization facts.

These are removals from this node's immediate proof route, not claims that their
modules leave the targets' import closure. Existing upstream declarations and
imports are preserved, including dependencies used transitively by the cited APIs.

## Where the brief, the DAG or earlier work was wrong

The recorded plan did not isolate the exact missing finite evaluation
specialization. The generic `SemilinearSections.evaluation_mate` and the intrinsic
finite scalar-transport theorem are available, but neither directly states the
bounded-constructible evaluation theorem for the literal
`FrobeniusExchange.systemCompactScalar`. This is the single remaining finite lemma.

The reconstruction part of the plan is shorter through the already stated
compactRealization normalization equation: no new effectivity theorem or chosen
inverse-limit comparison is needed here.

Checked the split's mathematical edge cases: zero systems, identity coefficient
embeddings, and empty schemes introduce no exception; the argument makes no
flatness or injectivity assumption on finite quotient coefficient maps. It requires
boundedness of both finite input evaluations explicitly, so ramified scalar
extension is not silently assumed t-exact. Both Noetherian hypotheses needed by
finite compact-support scalar transport are stated in the new theorem and derived
from the field structure maps in the assigned theorem.

## New nodes

`lem-sf-compact-support-system-scalar-finite-invertible` is the single finite
proper/open mate-evaluation step, in
`lean/Sheaf/Paper/CompactSupportSystemScalarFiniteInvertible.lean`. Its docstring
contains the complete argument: bounded etale antecedents, tensor/pullback
compatibility and reflection of cohomological vanishing, intrinsic finite scalar
transport, and evaluation of the specified proper/open adjunction word. The node
records the same argument and the existing dependencies used by it. The statement
was searched with Lean Finder, LeanSearch, Loogle, Mathlib grep, and blueprint
searches; none supplied this specialization.

No change record is needed: no existing signature, definition, visibility,
attribute, or public import changes.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
