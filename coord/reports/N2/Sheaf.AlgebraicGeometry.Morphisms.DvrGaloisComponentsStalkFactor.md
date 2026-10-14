## What changed

Proved the unchanged declaration `AlgebraicGeometry.Scheme.dvr_galois_components_stalk_factor`
from a general normalization chart-cover theorem and a proved reducedness theorem.
The item now proves Artinianness directly from monicity, transports the coproduct equation
to B, selects a chart, computes contraction, and constructs the stalk equivalence.
The private proved helper `affine_chart_stalk_germs` establishes compatibility for every
structural germ using the actual affine stalk equivalence and open-immersion stalk map.
Two new modules and their nodes are included; neither changes existing interfaces.
The node's route is updated to match the Lean proof. No target or definition changed.

## Proved and sorry left

Closed the item's only hole: `AlgebraicGeometry.Scheme.dvr_galois_components_stalk_factor`
(node `lem-sbc-dvr-galois-components-stalk-factor`). This is a decomposition, not a
sorry-free proof of the original result: its proof uses the chart-cover theorem below.
Also proved `RingTheory.dvr_galois_root_tensor_reduced`
(node `lem-sbc-dvr-galois-root-tensor-reduced`) from Mathlib with no sorry.
Added exactly one hole, `AlgebraicGeometry.Scheme.reduced_artinian_tensor_normalization_charts`
(node `lem-sbc-reduced-artinian-tensor-normalization-charts`). No sorry remains in the item.
The chart theorem asserts only the geometric chart cover, with explicit reduced Artinian
hypotheses; it contains no stalk, prime contraction or germ assertion. Those conclusions
are proved in the item. Holes closed: 1; holes added: 1; net: 0.

## No longer needed

Removed the exploratory proof import `Mathlib.RingTheory.Etale.Field`, using the narrower
`Mathlib.RingTheory.Unramified.Field` API instead. Removed redundant direct imports of
`Mathlib.RingTheory.Polynomial.Content`, `Mathlib.RingTheory.TensorProduct.Finite`,
`Mathlib.RingTheory.Flat.Basic` and `Mathlib.RingTheory.Localization.BaseChange` from
the new reducedness module; Eisenstein and Flat.Stability supply their used APIs.
The new chart module needs Artinian.Module rather than Artinian.Ring.
No original imports or dependency nodes were removed: the original node had no proof
dependencies. The proof needs no tame ramification, degree divisibility, invertibility of n,
localization-of-integral-closure theorem beyond the remaining chart construction, or
DVR structure of the root quotient. No new dependency on a root-uniformizer theorem is added.

## Where the brief, the DAG or earlier work was wrong

The original node had two non-elementary proof steps with empty `uses` and no Lean proof
dependencies. It did not actually supply declarations for its stated plan. This delivery
makes the chart step a precise independent theorem and proves the remaining algebraic and
stalk steps. The root algebra need only be a domain for reducedness: a full DVR theorem
is unnecessary. Edge cases checked mathematically: n=1 is covered by the same Eisenstein
proof; inseparable root extension does not matter since E/K is separable; empty component
families give empty normalization; zero tensor factors have no maximal factor to select.
The generic chart statement allows zero rings and arbitrary commutative E_i, assuming
exactly reducedness and Artinianness. No selected root prime is baked into it.

## New nodes

`lem-sbc-dvr-galois-root-tensor-reduced` records the proved algebraic reducedness result.
Its proof uses Eisenstein, flat tensor injection, localization base change and formal
unramifiedness over a field. It is a new proved module, not a new hole.

`lem-sbc-reduced-artinian-tensor-normalization-charts` records the remaining chart-cover
construction from finite affine coproducts and reduced Artinian tensor algebras. Its source
and complete proof in words are in its docstring and node. It is strictly the geometric
part of the original plan. The unit route is preserved; all work is below the trait step.

No change records or forced adaptations are needed.


## Second reading by N2

1. Compared the existing module with the repository by diff. The existing theorem
   signature is byte for byte unchanged; no existing definition or visibility changed.
   The added imports are proof-only. Verdict: pass.
2. Compiled all three delivered modules locally in import order. Scratch copies with
   `#print axioms` show only propext, Classical.choice and Quot.sound for
   `RingTheory.dvr_galois_root_tensor_reduced`; the original theorem and the chart
   theorem additionally show sorryAx, exactly for the reported remaining chart hole.
   Scanned all delivered Lean for forbidden declarations and hollow definitions:
   none; exactly one named theorem has sorry. Verdict: pass.
3. Read both new nodes and their Lean statements and natural-language proofs.
   The chart statement is true by reduced Artinian decomposition and finite-product
   integral closure, including empty families, zero factors and the identity base
   change. It is strictly the geometric portion: contraction and all stalk germs
   are genuinely proved in the item. Reviewed n=1 and inseparable root extensions
   for reducedness. Searched again with leanfinder, loogle and grep using integral
   closure of products, residue fields, and normalization open covers; inspected
   Mathlib normalizationObjIso, normalizationCoprodIso and IsArtinianRing.equivPi.
   Also inspected IntegralClosureFiniteNormalProduct and TraitGenericNormalizationCharts
   upstream. They supply components or a different tame-cover result, not this chart
   theorem. The remaining geometric construction cannot be closed in a few minutes.
   Verdict: pass as a decomposition, net zero holes.
4. Checked the algebraic reduction, coproduct equation over B, chart selection,
   contraction, and affine_chart_stalk_germs from top to bottom. No shorter direct
   theorem found. Imports added to the item are private proof imports; the new modules'
   public imports are used in their signatures. The original proof_deps was empty,
   so no old dependency is missing from No longer needed. Inspected
   dag/units/sk-prop-input-spreading.json: no realized route is altered or bypassed.
   Verdict: pass.
5. Compared node lean.statement fields with the declarations and checked proof_deps
   against the actual two lemma applications. New nodes have sources, complete proof
   plans, searches, creation metadata, blueprint provenance and matching module records.
   Existing node changes stay in its proof route fields. Verdict: pass.

Second reading changed only this report by adding the independent review record;
no mathematical or Lean repair was needed. Temporary axiom probes were removed.
