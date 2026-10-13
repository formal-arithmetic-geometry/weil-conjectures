## What changed

Proved `AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_ring_bridge`
by applying the existing `Module.flat_of_flat_closedFiber` to the local stalk tower.
All three existing theorem signatures and their public imports are unchanged.
Added proof imports of `FinitePresentationStalkLocalizationModel`,
`PolynomialChartClosedFiberModuleFlat`, and `Sheaf.RingTheory.FlatOfFlatClosedFiber`.

Added and proved `AlgebraicGeometry.exists_finitePresentation_stalk_localization_model`.
It explicitly localizes the affine section algebra at the images of the base-prime
complement, then uses localization transitivity to recover the source stalk. This
supplies both finite-presentation models required by the existing criterion.

Added and proved `AlgebraicGeometry.polynomial_chart_closedFiber_module_flat`.
Its private helpers identify the kernel of the fibre-inclusion stalk map with the
image of the base maximal ideal. The reverse kernel inclusion constructs a map
from the spectrum of the quotient into the fibre and checks its stalk composite
on germs. Surjectivity, the first isomorphism theorem, naturality of stalk maps,
and the quotient-tensor equivalence give the required closed-fibre flatness.

Updated all three existing nodes' proof routes to match the Lean. No definitions,
existing interfaces, or other groups' modules are changed.

## Proved and sorry left

Original hole closed (1 of 1):
`AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_ring_bridge`
(node `lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-ring-bridge`).
The two existing downstream wrappers remain proved.

Additional theorems proved without sorry:
`AlgebraicGeometry.exists_finitePresentation_stalk_localization_model`
(node `lem-sbc-finite-presentation-stalk-localization-model`) and
`AlgebraicGeometry.polynomial_chart_closedFiber_module_flat`
(node `lem-sbc-polynomial-chart-closed-fiber-module-flat`).
Axiom checks on both new public theorems show only `propext`, `Classical.choice`,
and `Quot.sound`. The original bridge inherits `sorryAx` through the existing
`Module.flat_of_flat_closedFiber` obligations; these are unchanged by this delivery.
All private helper theorems are proved. No holes remain in the delivered modules;
no holes are added or split off. The existing ring criterion is used as requested,
with its existing downstream obligations unchanged.

All three files compile without warnings through lcompile.py. The comparison was
checked mathematically for n=0, arbitrary non-Noetherian bases, and empty schemes:
n=0 gives a vector space over the residue field; empty schemes provide no point x;
the stalk/quotient identification uses no Noetherian hypothesis. The model theorem
also handles trivial section rings vacuously when there is no point.

## No longer needed

No existing imports, nodes, or modules are pruned. The proof retains the planned
ring criterion and canonical fibre construction. Removed the unused proof imports
`Mathlib.RingTheory.LocalRing.Quotient` and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` from the new comparison
module during import cleanup; its other imports already provide the needed API.
No geometric regularity, quasi-finiteness, depth, or dimension lemma is needed
for the reverse bridge.

## Where the brief, the DAG or earlier work was wrong

The earlier bridge hid the entire local-criterion application in a sorry, although
`Module.flat_of_flat_closedFiber` is already stated and proved from its own named
obligations. The finite-presentation and localization verifications can be proved
directly using Mathlib. Locality is an automatic instance, not a conclusion needing
the flatness criterion. The explicit `hbase` hypothesis is redundant with `[Flat f]`
but is preserved verbatim and used in the proof.

LeanSearch was attempted for both new statements and returned HTTP 500, recorded
as unavailable. LeanFinder and grep searches ran successfully and found the
localization ingredients but no complete fibre-stalk quotient comparison. Blueprint
searches for stalk finite presentation, fibre stalk quotient, and 00RH found no
existing blueprint statement to reuse. The unit route still applies the fibrewise
flatness criterion; it is not bypassed.

## New nodes

`lem-sbc-finite-presentation-stalk-localization-model` records the proved affine
stalk localization model in `Sheaf.AlgebraicGeometry.FinitePresentationStalkLocalizationModel`.
It is a reusable algebra-model statement and contains no flatness conclusion.

`lem-sbc-polynomial-chart-closed-fiber-module-flat` records the proved canonical
fibre-stalk/quotient-tensor comparison in `Sheaf.AlgebraicGeometry.PolynomialChartClosedFiberModuleFlat`.
Its docstring explains the quotient construction, kernel computation, and flatness
transport. It verifies one hypothesis of the local criterion. No change records
are needed.

## Second reading by U4

1. **Visible changes:** Compared the delivered item module with the repository version. Existing theorem signatures and public imports are unchanged; the only existing declaration body change is the proof of `AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_ring_bridge`. The two added modules and their node records are explicitly listed above.

2. **Compilation and axioms:** Compiled all three delivered modules with `lcompile.py --all`; there are no errors or warnings and no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` in the delivered sources. The two new public theorems use only `propext`, `Classical.choice`, and `Quot.sound`; the bridge's `sorryAx` comes only through the pre-existing criterion dependency.

3. **Statements:** Checked the added finite-presentation stalk model and closed-fibre module-flatness statements against their proofs and edge cases. Both are true with the stated hypotheses and are strictly intermediate results, not restatements of the target. No target or existing interface was weakened or changed.

4. **Pruning and route:** The proof uses the existing local flatness criterion, the affine localization model, and the canonical fibre comparison. No prior proof dependency is unused; only the two explicitly named proof-only imports were removed during cleanup. The unit route through the fibrewise flatness criterion remains intact.

5. **DAG agreement:** Verified that the Lean declarations, proof dependencies, proof routes, blueprint/unit metadata, and new node records agree. The report records the added nodes, closed hole, and no remaining holes in delivered modules.

Changed during second reading: added this section only; no Lean source, statement, node, or import changes were needed.
