## What changed

Replaced the hole of `AlgebraicGeometry.Scheme.integralResidueStratum_input`
without changing its signature, definitions, public imports, or original docstring.
The completeness argument now restricts the actual intrinsic unit using
`stratumIntrinsicComplete_preserved` and the existing equivalence between the
published intrinsic presentations. The existing raw inverse-image scalar comparison
and derived scalar compositor identify the resulting object with the exact
`integralResidueStratumPull` in the conclusion.

Added `IntegralResidueCoefficientCompleteness`. Its theorem
`integralResidueCoefficient_complete` is proved using the existing
`openDvrIntrinsicCriterion` and `purCoefficientModel_predicates`. It extends the
five fields of the supplied residue coefficient model by the actual exact scalar
restriction equivalence. The private helper proves invariance of the specified
completed-adic intrinsic unit under object isomorphisms, by naturality of the
functorial Koszul unit and its existing intrinsic-unit comparison. No new
completeness assumption is used.

The residue part is reduced to two comparisons at arbitrary positive quotient
level. `IntegralResidueFiniteReduction` compares the actual reduced inverse image
with a concrete, normalized finite scalar restriction. Its definition
`integralResidueFiniteModel` restricts the localization's representative and then
localizes; it chooses no arbitrary witness from an unproved existence theorem.
`IntegralResidueFiniteChart` transports one supplied finite perfect constant chart
to the small quotient coefficient universe on that chart's slice.

The proof generates the etale covering sieve from the given cover, checks its
covering property by joint surjectivity, factors each member through a cover
member, and applies the existing proved
`finitePerfectModelsRestrictIso_further` to propagate that member's slice model.
It then composes with exact restriction of the global finite comparison. The
remaining statements contain no covering or integral lifting assertion.

Validation: `lcompile.py --all` compiled all four modules successfully. The
coefficient-completeness, finite-reduction and finite-chart modules took 36.7,
35.7 and 36.8 seconds; the item took 44.8 seconds. The original theorem signature
and both original definition bodies were checked byte for byte against the source
and are unchanged. The dependency overlay has no cycle through the item.

## Proved and sorry left

One original hole is replaced by a complete Lean composition proof:
`AlgebraicGeometry.Scheme.integralResidueStratum_input`. There are no remaining
holes in the item module. The new coefficient completeness theorem and all private
helpers have complete proofs.

Two holes are added, each the entire proof of a public named theorem in its own
new module:

- `AlgebraicGeometry.Scheme.integralResidueFiniteReduction`, node
  `lem-weil-pbc-integral-residue-finite-reduction`: the finite quotient tensor and
  inverse-image comparison, for all positive exponents. It has neither completeness
  nor local perfectness hypotheses or conclusions.
- `AlgebraicGeometry.Scheme.integralResidueFiniteChart`, node
  `lem-weil-pbc-integral-residue-finite-chart`: scalar and module-universe transport
  of a single finite perfect chart to its slice. It has no completed object,
  completeness, covering, propagation, or integral lifting hypothesis or conclusion.

This is a decomposition, not an axiom-free proof of the original obligation.
The completeness implication and propagation to every sieve arrow are proved
from existing library declarations; the two finite presentation comparisons
remain. The packet closes one textual hole and adds two, so its net hole count
is +1 before accounting for the newly exposed import closure. No definition contains a hole.

## No longer needed

No existing module is withdrawn and no global pruning is claimed. Original public
imports are preserved. No imported upstream declaration is removed or altered.

The original direct proof edges to
`lem-weil-pbc-completed-constant-sheaf-reduction` and
`lem-weil-pbc-completed-realization-derived-cohomology` are unnecessary for this
assembly: the completeness implication uses the existing DVR unit criterion,
and the residue comparisons concern finite coefficients. These modules remain
available and may still be required transitively by their existing consumers.
The original direct edge to `def-weil-pbc-intrinsic-completion` is replaced by the
existing presentation-equivalence and Koszul-unit APIs; that definition is still
used transitively. The required stratum-restriction step and the unit route stay.
The new source imports are proof imports only, and all newly added imports are
used by the composition or its helpers.

## Where the brief, the DAG or earlier work was wrong

The existing `def-sf-open-quotient-koszul-models` bundled three independent
interfaces. Its open-extension dependency caused an artificial cycle from the
coefficient-only intrinsic criterion back through integral constructibility to
this item. The node record is narrowed to coefficient/completion structures; the
unchanged open structures receive their own node and their three actual consumers
are recited. An overlay DAG traversal confirms the input remains outside any cycle.


The completeness clause did not require another unproved coefficient transport
statement: the existing DVR intrinsic criterion can be applied to precisely the
supplied coefficient model after adjoining its explicit scalar equivalence.
Likewise, propagation to smaller slices is already proved in
`FinitePerfectQuotientModels`, so it is removed from the new finite-chart obligation.

The remaining finite comparisons are not supplied by the statements of the
originally listed completed-constant flatness and realization exactness results.
Those results do not by themselves identify the particular finite coefficient
presentations or the different module universes. The two new statements isolate
these comparisons, for all n, rather than restating the completed stratum input.

Read the source PDF at Lemma 6.5.8 and Proposition 6.6.11. Checked empty schemes,
empty covers, zero complexes, arbitrary differentials, and unbounded complete K.
The coefficient ideal equation is explicitly retained in the finite-chart lemma:
it identifies the two quotient rings even when the scheme is empty. A bounded
finite-projective representative over the finite small ring has small terms,
which permits the module-universe reduction; no arbitrary large module is
claimed small. The sieve argument uses factorization through a cover member,
not membership only on the generators.

## New nodes

`lem-weil-pbc-integral-residue-coefficient-completeness`, in
`IntegralResidueCoefficientCompleteness`, records the proved fixed-scheme
coefficient-completeness implication and the unit-isomorphism argument.

`lem-weil-pbc-integral-residue-finite-reduction`, in
`IntegralResidueFiniteReduction`, records the normalized finite scalar model and
the remaining derived finite reduction comparison. Its docstring gives the
projection-square and pure-tensor proof, including localization representatives.

`lem-weil-pbc-integral-residue-finite-chart`, in
`IntegralResidueFiniteChart`, records transport of one perfect finite constant
chart to the small coefficient universe and the corresponding slice. Its
docstring explains finite-projective smallness, scalar equivalence,
sheafification, and localization. Further restriction is deliberately handled
by the already proved library lemma in the item proof.

The three proof nodes are in `dag/nodes/sec-proper-base-change/`. Their proof
dependencies and the item's route are updated.

`def-sf-open-dvr-open-model`, in `dag/nodes/sec-six-functors/`, separates the
already existing `OpenDvrOpenModel` and `jShriek` attachment from the bundled
coefficient/completion node. Four existing node records are adjusted; no existing
Lean definition, theorem, signature or import is changed. The change record is
`coord/changes/K7-integral-residue-model-node-separation.md`.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
