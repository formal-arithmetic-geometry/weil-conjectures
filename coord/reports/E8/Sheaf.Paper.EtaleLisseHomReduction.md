## What changed

Completed the proof of `WeilConjectures.etaleLisseHomReduction`. The target proof assembles the lisse cover, the perfect and Tor bounds, the exceptional-stratum bounds, the finite-coefficient endpoint bounds and the canonical comparison data. The coefficient-Hom comparison is proved in `Sheaf.Paper.EtaleLisseCanonicalIso` from the finite-free local identity and the perfect-input restriction square, which remain separate split statements.

(Reviewer correction, cc review of aed7c29e5ead) As delivered, six intermediate theorems of the item module and `etaleLisseCanonicalIso` were left with `sorry`, although the module already contained unused private proofs of them. The reviewer closed them with those helpers: `etaleLisseHomFiniteFreeCover`, `etaleLisseHomLisseBounds`, `etaleLisseHomCoefficientInvertibleExponent` (the copy of the coefficient annihilator argument), `etaleLisseHomExceptionalBounds`, `etaleLisseHomComparisonData`, and `etaleLisseCanonicalIso` (cover conservativity plus a definitional transport of the heterogeneous equality). `etaleLisseHomEndpointBounds` was false as delivered: `dS` was an arbitrary integer, and `S` had no finiteness hypothesis. Take `dS = -1`, `S = Spec k`, `K = N = A[0]`, `a = 0`, `b = -1`, `dX = 0`. Then the claimed interval `[2,-2]` would force `RHom(A,A) = A` to vanish. The statement now assumes `S` separated of finite type over `k`, `dS : ℕ` and `IsDualizable K`, and it is proved. The dead helpers `predicate_of_witness` and `zero_sub_transport` were removed.

## Proved and sorry left

Closed `WeilConjectures.etaleLisseHomReduction` (node `lem-coef-etale-lisse-hom-reduction`) and the intermediate theorems `etaleLisseHomEndpointBounds`, `etaleLisseHomFiniteFreeCover`, `etaleLisseHomLisseBounds`, `etaleLisseHomExceptionalBounds`, `etaleLisseHomCoefficientInvertibleExponent`, `etaleLisseHomComparisonData` and `etaleLisseCanonicalIso`. The delivery leaves `sorry` in exactly two split theorems:

- `etaleFiniteFreeHomLocalIdentity` (node `lem-coef-etale-finite-free-hom-local-identity`)
- `etalePerfectHomRestriction` (node `lem-coef-etale-perfect-hom-restriction`)

No definition or private declaration contains `sorry`.

## No longer needed

The proof does not use the old direct local-comparison route or the private Hom/change-of-rings and open-complement helper imports removed from the item. It uses the source-library bounded-constructible Hom, dualizable Hom Tor and exceptional-support theorems, the finite-domain endpoint calculus, and the two split comparison steps. No source-library declaration or target statement was removed or weakened.

## Forced adaptations

`Sheaf.Paper.FiniteFreeHomEvaluationCoordinates` (unclaimed): `lisseHomModuleDerivedCategory` and `lisseHomConstantFunctor` become `abbrev`s with unchanged bodies; see `coord/changes/e8-lisse-hom-category-alias.md`. Its only other importer, `Sheaf.Paper.FiniteFreeHomLocalCalculation`, compiles against it unchanged.

## Where the brief, the DAG or earlier work was wrong

The target does not assume `a ≤ b`. The derived Hom bounds accept the supplied interval directly, and the interval is widened only for the endpoint calculus and the flat model.

## New nodes

`lem-coef-etale-lisse-hom-endpoint-bounds`, `lem-coef-etale-lisse-hom-finite-free-cover`, `lem-coef-etale-lisse-hom-lisse-bounds`, `lem-coef-etale-lisse-hom-exceptional-bounds`, `lem-coef-etale-lisse-hom-coefficient-invertible-exponent`, `lem-coef-etale-lisse-hom-comparison-data`, `lem-coef-etale-lisse-canonical-iso` (all proved), and the split statements `lem-coef-etale-finite-free-hom-local-identity` and `lem-coef-etale-perfect-hom-restriction`.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly, and the maintainer's independent review is the only review.
