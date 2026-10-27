## What changed

Replaced the assigned theorem's single sorry by a complete assembly from the normalized
section family already stated in `etaleExtension_free_presentations_hom`, two isolated
comparison steps, and the library's resolution-defined flat base-change theorems.
The original theorem signature and every public import are unchanged. No existing
module besides the item is changed; no shared definition or instance is changed.

Proved private helpers for the actual module-base-change map's invertibility under an
etale test, naturality of the counit mate on all modules, and its extension-unit equation
on all modules. The final assembly cancels the section-coordinate isomorphisms and uses
reflection of isomorphisms to obtain invertibility of the module-sheaf comparison.

Added proof imports:
- `Sheaf.TraceFormula.ZariskiEtaleRightAdjointSquare`
- `Sheaf.TraceFormula.ZariskiEtalePushforwardSectionFormula`
- `WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsLift`
- `WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionDegreeZero`
- `WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionIso`

The two new public statements isolate parent step 1 and the map-identification part of
steps 4–7. Neither asserts the whole comparison square: the first contains no e or
quasi-coherent pushforward result; the second asserts only an equality of section maps,
with no existence of contexts, right square, or invertibility conclusion. No data is
chosen in a new definition.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Scheme.Modules.zariski_etale_functor_comparison_square`
(node `lem-trf-zariski-etale-functor-comparison-square`). Its proof has no sorry.

The private helpers `etale_moduleBaseChangeMap_isIso`,
`pushforwardComparison_naturality`, and `pushforwardComparison_unit` are proved.

Added two holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.zariskiEtale_rightAdjoint_square`
  (`lem-trf-zariski-etale-right-adjoint-square`).
- `AlgebraicGeometry.Scheme.Modules.zariskiEtale_pushforward_section_formula`
  (`lem-trf-zariski-etale-pushforward-section-formula`).

This delivery is a decomposition: one original hole closed, two holes added, two
textual holes in the packet, net closure minus addition = -1. It does not claim a
sorry-free proof of the original mathematics. The other theorems used by the proof
retain their library status and are not changed by this delivery.

## No longer needed

Removed proof-only imports from the item:
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.Topology.Defs.Filter`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`
- `WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSections`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`

Removed from the item's direct proof-dependency list:
- `def-trf-space-etale-module-functors`
- `lem-weil-pbc-etale-scheme-base-change`
- `lem-trf-zariski-etale-tensor-sections`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `def-weil-pbc-composite-adjunction`
- `def-weil-closed-immersion`
- `lem-weil-pbc-affine-scheme-qcqs`
- `def-weil-finite-type-morphism`
- `def-weil-pbc-quasi-compact-scheme`
- `lem-trf-space-qc-separated-etale-local`
- `lem-pc-flat-base-change-cohom`
- `lem-weil-pbc-flat-base-change-map-sections`
- `def-pur-sheaf-tensor-product`
- `lem-weil-pbc-open-immersion-module-pullback-restriction`

The quasi-compactness and separatedness hypotheses in the actual Lean statement are
already the scheme notions, so the space-to-scheme atlas and diagonal argument is
unnecessary here. The current small-etale pushforward definition already evaluates on
the scheme fibre product; the general chart-limit model need not be unfolded in the
assembly. Normalized extension comes directly from the free-presentation theorem.
Base-change invertibility uses the actual resolution comparison and its degree-zero
identification, avoiding finrank-only field-extension statements and a second section
calculation for invertibility.

Some removed direct dependencies remain required indirectly by the two split steps or
by the existing free-presentation theorem. No global withdrawal of those modules is
claimed. No module is deleted. Removed the two obsolete direct `tool_uses` approvals
`lem-weil-pbc-ringed-topoi-module-adjunction` and
`lem-weil-pbc-flat-base-change-map-sections` from the item's node; the new right-square
and section-formula nodes explicitly retain those mathematical inputs respectively.
The unit statement and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original DAG attachment for `lem-pc-flat-base-change-cohom` is
`Modules.finrankH_pullback`, a dimension statement for field extension, rather than
invertibility of the canonical sheaf map in this generality. The earlier review already
noted this mismatch. The resolution comparison isomorphism and its degree-zero
identification give the needed actual map without correcting any library statement.

The pullback-isomorphism clause needs no additional argument: the specified comparison
is an Iso by definition. Naturality and the final unit equation hold for all modules
and all morphisms; their proofs do not use the quasi-coherence or compactness hypotheses
that scope those clauses in the assigned statement.

Edge checks for the split statements: empty schemes and opens, the zero module, and
identity morphisms use the same functor and adjunction identities. Arbitrary maps
between etale test schemes are covered by sheaf naturality and require no new flatness
hypothesis. The section-formula statement assumes quasi-coherence of H and of a_*H
explicitly; it asserts map equality without claiming that the map is invertible.

## New nodes

`lem-trf-zariski-etale-right-adjoint-square` records existence and the explicit
open-coordinate normalization of the direct-image/restriction square, from Stacks
03FH (2), with its right-adjoint proof. Its module is
`Sheaf.TraceFormula.ZariskiEtaleRightAdjointSquare`.

`lem-trf-zariski-etale-pushforward-section-formula` records only identification of the
canonical counit mate with module base change in normalized tensor-section coordinates,
from Stacks 03LC (3) and 02N7 in degree zero. Its module is
`Sheaf.TraceFormula.ZariskiEtalePushforwardSectionFormula`.

No interface change records are needed: existing signatures, definitions, attributes,
instances and public imports are unchanged.

Validation: the new statement modules compiled individually in 23.2 s and 15.9 s.
The original target signature and all public imports were compared textually after
normalizing whitespace; all three node Lean statement records agree with their files.
The updated DAG dependency closure is acyclic (779 nodes).
The completed assigned module compiled cleanly in 17.1 s, below the 60 s limit.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
