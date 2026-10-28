## What changed

Corrected and proved `AlgebraicGeometry.Scheme.finiteModel_derivedRepresentative_transport`
in `Sheaf.Paper.FiniteModelCoefficientTransport`: ordinary scalar extension computes the
specified derived value for a K-flat input. The proof uses invertibility of the derived
counit, uniqueness of scalar-extension adjoints, the scalar-composition isomorphism,
exact inverse-equivalence restriction, and exact constant realization.

Exposed the already proved `finiteModel_constantComplex_mapIso` and proved
`finiteModel_exists_kFlat_representative` from the source flat-resolution theorem.
Both preserve the original coefficient universe; the constant functor includes the
prescribed universe lift. The local functorial flat-resolution helper is proved from
the free-forgetful counit, with no postponed data or additional assumptions.

Added the same necessary K-flat hypothesis to the existing core and lifted comparison.
Adapted the unclaimed `Sheaf.Paper.FiniteModelDerivedScalarComparison` without changing
its signature: choose a K-flat representative R of P, use the two corrected comparisons
on R, and transport back through the exact functors and L. Updated all four DAG nodes.
The proper-base-change unit and target statements are unchanged.

Change record: `coord/changes/K1-finite-model-kflat-transport.md`.
All four delivered modules have compiled separately in import order, each under 11 seconds.

## Proved and sorry left

The corrected `AlgebraicGeometry.Scheme.finiteModel_derivedRepresentative_transport` is
fully proved; the item has **zero remaining holes**. Its original arbitrary-input
statement was false, so removing that hole by correcting its signature is a statement
repair, not a proof of the old statement and not a net proof-closure claim.

Also proved `AlgebraicGeometry.Scheme.finiteModel_exists_kFlat_representative`;
`AlgebraicGeometry.Scheme.finiteModel_constantComplex_mapIso` remains fully proved.
The existing core proof and arbitrary-complex parent proof compile with the repair.
No new sorry declarations or split-off obligations are added.

One pre-existing hole remains in the delivered related module, with a corrected
statement: `AlgebraicGeometry.Scheme.finiteModel_constantScalarExtension_liftComparison`
(node `lem-weil-pbc-finite-model-lift-comparison`). Its proof is exactly `by sorry`;
the docstring gives its complete proof from a flat-term K-flat resolution, constant
realization comparison, tensor/lift compatibility, and quasi-isomorphism invariance.
The existing derived-change bridge is imported unchanged; its proof obligation is
outside this delivery. Original item holes: 1; unchanged-statement holes proved: 0;
item holes after repair: 0; new holes: 0.

## No longer needed

Removed the proof import
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`: the argument uses
ordinary-module extension, its K-flat derivability criterion and uniqueness of left
adjoints, and does not use the module-object derived-scalar theory.

The transport proof no longer needs `lem-weil-pbc-derived-module-scalar-adjunction`;
that existence-only declaration does not identify ordinary scalar extension on an
arbitrary complex. The localization dependency remains, and the actual K-flat
preservation, flat-resolution and constant-realization dependencies are recorded.
No whole module is withdrawn; these nodes can still be needed on other routes.
The core and parent remain needed; no unit statement or unit proof step is pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statements, now corrected): ordinary scalar extension on an
arbitrary P cannot represent derived scalar extension for non-flat q. For
q : ℤ → ℤ/2 and P=(ℤ/2)[0], Tor_1^ℤ(ℤ/2,ℤ/2)=ℤ/2 is nonzero and is absent
from ordinary tensoring of P. The same error occurred in both core and lift comparison.
Stacks sites-cohomology, lemma-derived-base-change (06YY), computes using K-flat
resolutions; lemma-derived-pullback-composition (0D6D) explicitly chooses such a
resolution. Exact constant realization is sites-modules, lemma-constant-exact (093J).

Each corrected node has a statement_change record and complete citer audit:
the parent still holds for arbitrary P because its proof now resolves P; the corrected
core passes its K-flat hypothesis to the corrected lift comparison. Neither a target
signature nor the mathematical conclusion of the general parent is weakened.
The server queue marked the item disputed; no rework or build-error entry was present.
The declared adjunction/localization dependencies alone did not justify the false
ordinary-versus-derived identification. No further copy of the same obligation was
introduced, despite its prior sequence of splits.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteModelCoefficientTransport": "16ef003c35da56f41e0451523ae88b81ed35ce24", "Sheaf.Paper.FiniteModelConstantScalarExtensionCore": "140d3ec122c1d9071224cdf526d33ca6b966bc0f", "Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison": "ee72bce5cc31bdb4ab668a052668a131b38e6aad", "Sheaf.Paper.FiniteModelDerivedScalarComparison": "c9b56287ab16acb3f320c3a81cb1a7a9511da19e"}, "results": {}, "time": "2026-10-28T05:11:44+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
