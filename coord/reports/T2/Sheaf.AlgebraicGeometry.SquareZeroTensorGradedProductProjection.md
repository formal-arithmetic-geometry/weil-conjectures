## What changed

Existing declarations stay in the original module verbatim, including definitions,
proof of coefficient evaluation, docstrings, public names, and the irreducibility
attribute. Added the proved `tensorGradedSection_product_raw` and
`tensorGradedSection_projection_of_raw` helpers to this module. The original target
now applies the projection helper to the raw identity.

The raw identity applies quotient multiplication, then the canonical tensor-section
comparison and arithmetic equality transport. The two open lower theorems have new
modules, imported only for proofs. The original public presentation import remains.
Removed the first worker's unnecessary declaration moves, raw helper module, and
movement change records; there is no existing interface change to record.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.Modules.tensorGradedSection_product`.
Proved the new helpers `tensorGradedSection_projection_of_raw` and
`tensorGradedSection_product_raw`. `tensorGradedCoefficientProjection_apply` was already
proved and is moved unchanged, so it is not counted as a newly closed hole.

Added two holes, both strict parts of the old proof:
- `AlgebraicGeometry.Scheme.Modules.tensorGradedQuotient_multiply`, node
  `lem-sc-square-zero-tensor-graded-quotient-multiply`: arbitrary quotient sections,
  without the canonical block-degree comparison.
- `AlgebraicGeometry.Scheme.Modules.tensorSectionProduct_comparison`, node
  `lem-sc-square-zero-tensor-section-product-comparison`: canonical comparison coherence,
  without a graded algebra or its quotient multiplication.

No other delivered theorem contains sorry. This is a decomposition: one original hole
closed, two lower holes added (delivery-local net -1), not a completed proof of the
original mathematical argument. Closure and whole-library figures are for the ledger.

## No longer needed

No original module is pruned; the original public presentation import is retained.
The proposed SquareZeroTensorGradedProductProjectionRaw module is no longer delivered:
its proved helper belongs in the original module and its separate file is unnecessary.
The original direct proof dependencies are replaced in the target node by the raw and
projection helpers: `lem-sc-square-zero-ideal-tensor-unit`,
`lem-sc-square-zero-tensor-graded-presentation`, and
`lem-weil-pbc-closed-immersion-unit-quotient`. They remain needed below the helpers.
The projection helper uses only `TensorGradedPresentation.c_projection`, not the raw
product theorem: its raw identity is an explicit hypothesis.

## Where the brief, the DAG or earlier work was wrong

The first reading report counted an already-proved coefficient evaluation as progress
and accepted a single raw-product hole retaining nearly the whole target argument.
The second reader replaced that hole with independent quotient-multiplication and
comparison-coherence obligations and a real combining proof. The projection node
incorrectly recorded the raw theorem as a proof dependency despite accepting it as a
hypothesis; that dependency is removed. Original docstrings were dropped; restored.
Once the raw identity was proved, its separate module and declaration moves became
unnecessary: all existing declarations are now kept exactly in their original module.
No change records or moving interfaces are delivered. This also avoids a moving user
inventory as other groups land new downstream modules during this reading.

The Stacks sources were read online because the literature tex is absent on this host:
https://stacks.math.columbia.edu/tag/09MS (the exact tensor sequence and graded sequence)
and https://stacks.math.columbia.edu/tag/01CD (functorial tensor pullback).
The lower lemmas spell out the local lifting and coherence details these sources leave
implicit; neither lemma requires the Noetherian or ample hypotheses of the ambient
09MS theorem, since those are used later in its proof, not in these tensor identities.

## New nodes

`lem-sc-square-zero-tensor-graded-product-projection-raw` is now proved from two parts.
`lem-sc-square-zero-tensor-graded-product-projection-projection` is the proved application
of the degree projection and `c_projection`.
`lem-sc-square-zero-tensor-graded-quotient-multiply` is the local descent of `b_multiply`
through `b_quotient` and the closed immersion unit, for arbitrary degreewise sections.
`lem-sc-square-zero-tensor-section-product-comparison` is the algebra-free coherence
identity for the explicit pullback and tensor-power comparisons.

## Second reading by T2

1. Compared the delivered modules to the repository and mechanically compared all
   existing declaration signatures byte for byte. Definitions, original coefficient
   evaluation proof, docstrings, declaration locations, public presentation import,
   and irreducibility attribute are retained. No target statement changed.
   Previously checked seven unchanged users against the moved-definition overlay;
   those moves are now removed entirely, preserving the original public interface.
2. Compiled the modules individually in import order through lcompile.py. The only
   text holes are the two named lower theorems; no data definition has a hole and no
   axiom, unsafe, opaque, extern, or implemented_by is introduced. Axiom probes are
   checked before delivery. The explicit scratch #print axioms check succeeded:
   the two definitions, coefficient evaluation, and projection helper use only
   propext, Classical.choice, and Quot.sound; raw and target multiplication also
   use sorryAx through the two lower obligations.
3. Read the explicit presentation and canonical comparison definitions, and searched
   via leanfinder, loogle, grep, and local rg with alternative queries. Existing
   structural tensor-section lemmas supply pieces, but neither full lower statement
   already exists. Tested the arguments at n=0, e=0, a=d=0, zero input sections, and
   the identity closed immersion: unitors handle degree zero without orthogonality.
   Quotient descent uses local lifts, never an unjustified global section lift.
   Each open lemma has a full proof docstring and matching node. The two obligations
   are independent strict parts; the raw identity is now actually proved from them.
4. The proof first cancels c with q, then reduces raw multiplication to b_multiply
   descending to the quotient and algebra-free comparison coherence. The new
   lower imports are proof-only. No unit-level route is bypassed:
   dag/units/sk-thm-curveestimate.json still realizes thm-sc-proper-cohomology and
   has no recorded proof steps. The replaced target dependencies are all listed
   above; their lower-level use is retained.
5. Checked the node proof steps, dependency unions, source, Lean declaration records,
   chapter, unit, and blueprint provenance against the actual proof. Corrected the
   projection helper dependency and replaced the raw node's vague placeholder plan
   with the two lemmas that the Lean proof applies.

Second reading changed: decomposed the raw hole into quotient multiplication and
comparison coherence and proved the raw identity from them; restored docstrings;
removed unnecessary declaration moves and their records; corrected node dependencies
and progress accounting.
