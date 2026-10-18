## What changed

Proved `AlgebraicGeometry.Scheme.exists_geometricPoint_strictHenselization_lift` in
`Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift`, with its signature and all
public imports unchanged. The proof uses the existing affine-chart ind-etale theorem,
flat generalization lifting, and a section of the weakly etale geometric fibre. It constructs
the final morphism as a section followed by the other pullback projection; the final equality
is the actual pullback identity and section equation.

Updated the declaration's proof docstring and its DAG proof, proof dependencies and proof origin
to describe this shorter route. Added proof-only imports for
`Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale`,
`WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`,
`Mathlib.AlgebraicGeometry.PullbackCarrier`, and
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_geometricPoint_strictHenselization_lift`
(node `lem-weil-pbc-geometric-specialization-strict-local-lift`).
One of one original sorries proved; zero split off; zero holes added; zero sorries remain
in the delivered Lean file. No definitions or signatures were changed.

The proof's geometric edge cases require no extra hypotheses: the chart exists because it
contains s; the strict local scheme has its closed point; the fibre is nonempty by flat
lifting of t; and the section theorem needs neither finite presentation nor quasi-compactness.
It applies to the prescribed field Ωt, so the construction does not replace barT with an
unrelated geometric point. The case t=s is included without any additional choice of embeddings.

## No longer needed

Removed these direct proof imports (some remain transitively available to other results):

- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation`
- `Sheaf.RingTheory.StrictHenselizationTriplesPresentation`
- `Sheaf.RingTheory.StrictHenselizationTriples`
- `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`
- `Sheaf.RingTheory.StrictHenselizationFaithfullyFlat`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.WeaklyEtaleField`
- `Mathlib.AlgebraicGeometry.Stalk`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`

The direct proof no longer needs the following planned nodes. The affine chart theorem
packages the neighbourhood-colimit comparison. Flat generalization lifting replaces the
local presentation, localization-prime identification and faithful-flat spectrum argument.
The already-proved weakly-etale section theorem packages the geometric fibre's residue-field
embedding, avoiding its separate construction in this module.

- `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`
- `lem-weil-pbc-colimit-initial-full-subcategory`
- `def-weil-etale-morphism`
- `def-weil-pbc-ind-etale-algebra`
- `lem-sbc-geometric-strict-henselization-local-presentation`
- `lem-sc-strict-henselization-triples-presentation`
- `lem-weil-pbc-strict-henselization-triples`
- `lem-sc-strict-henselization-faithfully-flat`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-faithfully-flat-surjective-spectrum`
- `lem-weil-pbc-weak-etale-field`
- `def-weil-residue-field`
- `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`
- `lem-weil-pbc-morphism-from-spec-local-ring`

The proof still uses the ind-etale-to-weakly-etale clause of
`lem-weil-pbc-ind-etale-stability`, via the proved upstream instance rather than the Sheaf
bundle theorem. The strict-local ring and structural map remain statement dependencies.
Removed the obsolete `tool_uses` approvals for local presentation, triples presentation,
triples, and faithful flatness; retained strict-henselization functoriality.
No unit statement or realized unit step is bypassed: this helper is not itself a unit's
statement or step, and the new chart helper and geometric-section helper are already proved.
No module is withdrawn and no global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but longer than necessary given the declarations
already present. `strictHenselization_indEtale_of_affine_chart` avoids reconstructing the
chart comparison, and `exists_comp_eq_id_of_weaklyEtale` supplies the entire residue-field
argument over the prescribed algebraically closed field. Thus no new intermediate statements,
new nodes, definition repairs, change records, or consumer adaptations are needed.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
