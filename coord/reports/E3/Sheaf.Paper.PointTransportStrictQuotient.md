## What changed

Prove `WeilConjectures.pointTransport_strictQuotient` with its exact original
statement. The original eight model definitions and instances move verbatim to
`Sheaf.Paper.PointTransportStrictQuotientModels`, which the item publicly imports.
Their names, signatures, bodies and public availability are preserved.

Three new proved modules provide the section formula, strict transition,
augmentation and chain-map identities, and canonical finite derived evaluation:
`PointTransportStrictQuotientSections`, `PointTransportStrictQuotientIdentities`,
and `PointTransportStrictQuotientFiniteEvaluation` under `Sheaf.Paper`.
The strict calculations use the actual prescribed maps on sections. Finite
evaluation uses natural finite sigma and inverse-image comparison, together with
the naturality of exact-functor localization factors.

The item constructs the two functors to complexes of integral-module towers using
the existing complex/functor equivalence. K-flat reduction, exact pullback,
restriction and point sections preserve quasi-isomorphisms levelwise. The existing
localization of good complexes then gives the two derived functors and the unique
natural transformation with the required equation on every representative.

The complete single-file proof exceeded 60 seconds. Before splitting, the slow
rewrites were replaced by direct equality chains, finite calculations were made
for an arbitrary finite complex before quotient substitution, and large choices
were kept irreducible locally. The modules separate the remaining kernel checks;
no shared definition was changed to obtain the timing improvement.

Only the item, these new modules, their nodes, and the change record are changed.
The change record is `coord/changes/E3-point-transport-strict-quotient-modules.md`.
There are no adaptations of other existing modules. The proof imports the existing
private proved K-flat invariance/localization and finite-sigma helpers using
`import all`; it does not change them.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.pointTransport_strictQuotient`
(`lem-trf-point-transport-strict-quotient`).

The new public theorems `WeilConjectures.strictQuotientPointMap_sections`,
`WeilConjectures.strictQuotientPointMap_identities`, and
`WeilConjectures.strictQuotientPointMap_derived` are proved, as are all their
private helpers. No `sorry` remains in any delivered Lean file; zero holes are
added and zero unproved statements are split off. The moved definitions contain
no holes. Existing named dependencies are used as declarations of the library.

Validation: all five modules compiled remotely in import order under the enforced
per-file limit. The corrected finite evaluation and main module then compiled
together again with exit code 0. A source check found zero holes and no debugging
commands in every delivered Lean file. The theorem statement and all eight moved
definition/instance bodies match the original source exactly; their bodies have
no mathematical interface change.

## No longer needed

The separate planned dependencies `lem-trf-quotient-tensor-insertion`
(`Sheaf.Paper.QuotientTensorInsertion`) and
`lem-trf-point-quotient-tower-homotopy`
(`Sheaf.Paper.PointQuotientTowerHomotopy`) are not required by this proof.
The existing kappa, theta and pullback-transition formulas directly prove the
strict identities. Levelwise homology detection and the existing good-complex
localization construct the required derived tower functors without the separate
whole-diagram source comparison or a separate homotopy-category factorization.

The original direct proof imports of
`Sheaf.Paper.PointAutomorphismRestrictionNatural`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, and
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients` are removed.
Restriction and unit naturality are proved directly in the strict calculations;
K-flat invariance and resolving-class localization use the already proved helpers
in `IntegralOperationsWellDefined`. Thus the old standalone restriction-natural
and site-derived-tensor-descent nodes are not direct proof dependencies here.
Their use by other declarations and by imported helper proofs is unaffected.

The former public imports are preserved through the publicly imported model
module. The small-module-diagram import is retained there for the tower category;
`Mathlib.CategoryTheory.Localization.Predicate` remains a proof import of the item.
No module or DAG node is withdrawn, including the quarantined tower-homotopy file.
No declaration is removed from `lean/WeilConjectures`.

## Where the brief, the DAG or earlier work was wrong

The tower-homotopy dependency is quarantined in the current snapshot. Its absence
is not treated as withdrawal: the delivery gives a direct proof using the existing
reduction functors and quasi-isomorphism invariance. The unit has no realized
statement or proof step requiring the omitted dependency.

The latest blueprint snapshot (`main-20261026`) no longer contains the old
`prop-trf-rational-frobenius-integral-model` file cited by this retained node.
The current integral transport proof is under `sk-prop-tf-transport-integral`.
This assignment proves the retained Lean statement verbatim; no target statement
or definition is weakened and no replacement parent route is claimed.

## New nodes

`def-trf-point-transport-strict-quotient-models` records the unchanged published
strict quotient models in their new module. The original node retains the main
theorem attachment; the model declarations are attached to this new node.

`lem-trf-point-transport-strict-quotient-sections` proves the actual section formula
by cancelling the identity-on-sections restriction comparisons and applying the
published sigma and kappa formulas. The zero complex and n=0 (exponent one) need
no additional condition, and the proof works in every integer degree.

`lem-trf-point-transport-strict-quotient-identities` proves transitions,
augmentation and chain-map naturality for arbitrary integral complexes. It uses
restriction and adjunction-unit naturality. No flatness of a coefficient quotient
is assumed, and the proof applies to identity and zero chain maps as well.

`lem-trf-point-transport-strict-quotient-finite-evaluation` proves comparison with
the specified finite transport for arbitrary complexes. It uses natural sigma,
natural inverse-image comparison and exact-functor factors. The purely categorical
factor calculation uses only naturality and isomorphism cancellation.

All four nodes are proved constructions or proved statements, not new work left
with holes. The change record is
`coord/changes/E3-point-transport-strict-quotient-modules.md`.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
