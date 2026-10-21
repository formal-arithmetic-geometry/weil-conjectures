## What changed

Restore lean/Sheaf/AlgebraicGeometry/PicardConnectiveModelComparison.lean from the
quarantine archive named by coord/rework.tsv. Preserve the public statement and
all three public imports and the existing DAG route. Add one private proof import
for WeilConjectures.FromJoel.Algebra.Homology.Single.
The proof combines picard_termwise_model_comparison with
DerivedCategory.connective_single_hom_bijective and the explicit additive equivalence
between chain maps from a single complex and ordinary cycles.

The change record is coord/changes/F2-picard-connective-comparison-restoration.md.
No other library module or DAG attachment is changed.

## Proved and sorry left

The restored theorem AlgebraicGeometry.Scheme.picard_connective_model_comparison
has a complete proof. Its quarantined source contains zero holes, so this repair
closes 0 of 0 textual sorries and adds zero holes. No theorem is split off.
The private singleCyclesEquiv, isoHomAddEquiv and localizationEquiv are complete
constructions, with no data taken from an unproved arbitrary existence theorem.

## No longer needed

None. No imports, declarations, nodes or modules are pruned. The two declared proof
lemmas are both used. The ordinary-cycle definition is used to identify the kernel
and the raw restriction equation. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole quarantine restoration, rather than a new proof of a textual
sorry. The missing live path does not mean the mathematical obligation was withdrawn.
The archived proof already realizes the current node plan, including the naturality
clause and the simultaneous choice of comparison families.

Searches run in this session: LeanFinder on single-complex morphisms and cycles
found fromSingle₀Equiv (natural-number complexes only); Loogle found mkHomFromSingle;
local rg found the existing integer-indexed fromSingleEquiv in the adopted source.
None replaces the scheme-level coherent model comparison. The private
singleCyclesEquiv now uses the existing integer-indexed
HomologicalComplex.fromSingleEquiv, with an explicit proof of additivity. This removes
the duplicate chain-map constructor and inverse checks while preserving its value
and the degree-zero formula used by the naturality proof.

The generic helpers were checked independently with the current connective-map lemma.
The initial published snapshot still imported the retired Sheaf ordinary-cycle twin,
so the first delivery attempt stopped before elaboration and pushed nothing. After
the updated dependency became available, the restored module compiled cleanly on
the server (13.5 seconds). The scratch parameterized check was not used as validation;
the actual unchanged theorem signature and complete proof were compiled instead.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
