## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceCoefficientRestriction`
by the construction of both completed projection cones from finite comparison
isomorphisms. The theorem's signature and public import are preserved.

The proved private lifting argument uses the residue scalar equation to show
that sections at level n are killed by l^(n+1). For any additive map into that
level, approximate a p-adic scalar by an integer modulo l^(n+1). The annihilation
equation then proves linearity. This applies to arbitrary source modules; the
source need not be torsion. Lift the actual ring-limit and root-limit cones,
after composing with the respective finite comparison inverses. Naturality
holds because the additive maps are unchanged. Inverse cancellation proves both
projection normalizations on every section.

`DiagonalTraceCoefficientIdentification` constructs the isomorphism of the
lifted valuation ring with Z_l using its absolute-value characterization. It
identifies the positive quotient via `PadicInt.toZModPow` and its kernel, proves
the actual coefficient maps invertible, assembles their tower isomorphism, and
uses the recorded underlying-section equations of the restriction. The resulting
comparison sends one to one.

Two independent finite constructions remain in new modules: the exact residue
restriction, with no Chern data or coefficient cones; and the normalized finite
Tate-line comparison for a supplied restriction, with neither a restriction
construction nor either completed cone. The main proof combines these with the
proved coefficient identification and the directly constructed cones.

Only the item, its node, and three new modules with their nodes are included.
No other existing interface, declaration, instance, or public import changes.

## Proved and sorry left

Original item holes: 1. The original hole of
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceCoefficientRestriction`
(node `lem-sfb-diagonal-trace-coefficient-restriction`) is closed; zero holes
remain in the item. This is a decomposition: one original hole closed and two
strictly smaller holes added, packet net -1, not a sorry-free proof of the entire
construction.

Also proved without a new hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceCoefficientIdentification`
(node `lem-sfb-diagonal-trace-coefficient-identification`), including its unital
normalization. Every private helper in the delivery is proved.

Every hole added:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceResidueRestriction`,
  node `lem-sfb-diagonal-trace-residue-restriction`.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceLineIdentification`,
  node `lem-sfb-diagonal-trace-line-identification`.

Each remaining proof is exactly `:= by sorry`, with a source and a complete
proof in words. No data definition chooses an arbitrary witness from these
existence assertions: the main theorem eliminates them only within its proof.

The finite arguments do not use the supplied derived Chern normalization `hc`.
Its binder is preserved verbatim, with a declaration-local unused-variable
linter suppression. Compilation and delivery use the required remote tools;
the final delivery command records all compiler and preflight results.

## No longer needed

No existing import is removed and no module is withdrawn. No global pruning
is claimed. The former direct proof dependencies
`det-sp-coefficient-towers-abelian` and `lem-coef-semilinear-derived-sections`
are needed only for the two finite constructions, whose nodes retain them.
They are not needed by the completed cone-lifting argument and are not newly
imported into the item. The existing Chern, restriction and coefficient-cone
definitions remain statement dependencies.

The two remaining finite-construction modules publicly import only
`DiagonalTowerTraceModels`; they do not need `Coefficients` or the definitions
of derived cone comparison maps. The coefficient identification needs no
completed projection or Chern datum.

## Where the brief, the DAG or earlier work was wrong

No statement is weakened or disputed. The declared generic semilinear and
abelian tower results provide the underlying module calculus, but their
signatures do not directly state these project-specific finite identifications.
The completed cones themselves do not require a new existence statement:
additive maps into finite torsion targets are already p-adic linear. This
argument is proved in the item rather than split off again.

Checked the first positive level n=0, zero sections and empty sites. The
coefficient identification uses the valuation-ring isomorphism only for
E=ULift Q_l. The finite line comparison is scalar extension along an isomorphism,
so it needs no local freeness or invertibility of l on T; the arbitrary ordinary
scalar model is tied to the tensor model by its existing `obj_eq` and
`unit_section` equations. The cone-lifting lemma works without any torsion
hypothesis on its source and uses annihilation of its target at every section.
No scheme morphism, direct-image comparison or derived conservativity is used.
The blueprint unit route is unchanged.

Ran LeanSearch, LeanFinder, Loogle and source grep through `msearch.py`, searched
the project sources and DAG, and read the current blueprint proof paragraph (1).
The new finite statements are strictly separate parts of the original plan.

## New nodes

`lem-sfb-diagonal-trace-residue-restriction`: the exact section-preserving
restriction functor, independently of Chern data and all normalized cones.

`lem-sfb-diagonal-trace-coefficient-identification`: the proved unital additive
coefficient-tower identification, from the explicit lifted valuation and residue
ring isomorphisms.

`lem-sfb-diagonal-trace-line-identification`: the ordinary pure-tensor
root-tower comparison for a supplied restriction, before the completed
root-limit cone. No completed cone or restriction functor is asserted here.

No change record is required: no existing statement, definition or public
interface changes.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
