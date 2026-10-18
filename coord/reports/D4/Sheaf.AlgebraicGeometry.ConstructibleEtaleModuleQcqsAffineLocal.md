## What changed

Proved `AlgebraicGeometry.Scheme.constructible_etale_module_qcqs_affine_local`
without changing its signature. Added three proved private helpers in the same module:
transport a stratification across an isomorphism without changing its domains;
replace each domain by its explicitly constructed nilradical subscheme; and pull
finite local constancy along a composite using the existing pullback comparison.

The cyclic proof uses the singleton whole-scheme cover, a finite affine refinement
of a given cover followed by `exists_global_stratification_factoring_local`, and
base change of a global stratification followed by reduction of its domains.
All finite-value comparisons use `finite_locally_constant_module_values_iff`.
Updated the existing node's proof, proof dependencies and proof origin to match.
Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` for the explicit
reduction construction and its already proved reducedness instance. No new nodes,
statements, definition changes, consumer adaptations, or change records are needed.

Validation: launcher single-file compilation passes cleanly. The temporary
`#print axioms` probe reported exactly `propext`, `Classical.choice`, `Quot.sound`.
The import-direction check permits the added import. Empty schemes, empty finite
subcovers, and empty strata are allowed throughout; no intersection of affine opens
is assumed affine. All witnesses used inside definitions are explicit constructions.

Searches run through msearch: LeanFinder query "constructible etale sheaf affine
local quasi compact quasi separated scheme" returned affine limit and constructible
image results, with no theorem giving this equivalence; Loogle "IsAffineOpen, Opens"
reported unknown identifier; grep "constructible.*affine|affine.*constructible"
returned no hits. Local rg searches found the proved pullback, finite-values,
gluing, and nilradical subscheme APIs used here. The existing declared dependencies
sufficed, with explicit reduction simplifying the representative step.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.constructible_etale_module_qcqs_affine_local`
(node `lem-weil-pbc-constructible-qcqs-affine-local`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
Split-offs: 0. This is a proof, not a decomposition. The axiom probe also confirms
that no imported `sorryAx` occurs in the theorem's proof closure.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.ConstructibleSheaf.Refinement`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Mathlib.CategoryTheory.Adjunction.Basic`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`.
- `WeilConjectures.ConstructibleSheaf.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.

The removed API imports are either unused here or already public through imports
that the proof needs; no public import was removed. Removal of a
direct import does not claim that its module becomes globally unreachable.

Removed explicit proof-dependency edges:

- `lemma-constructible-immersion-independence`: an actual reduction map and ordinary
  pullback preserve the finite local systems, so same-image descent is unnecessary.
- `lem-weil-pbc-etale-inverse-image-restriction`: the proof works entirely with the
  existing module-valued pullback functors and their composition isomorphism.
- `def-constructible-constant`: only the proved finite-values equivalence is used.
- `def-weil-pbc-inverse-image`: the functor is already part of the statement/API;
  no construction from its defining adjunction is needed in this proof.
- `lem-weil-pbc-constructible-preimage`: `Stratification.pullback` already supplies
  constructibility for the base-changed strata. Transport across isomorphisms uses
  the existing scheme-morphism preimage lemma directly.
- `def-weil-constructible-subset`: constructibility is carried by the stratification
  records, so no separate reconstruction from its definition is needed.

No unit realization is bypassed: this node is below the fixed realized statements
and proof steps of `sk-thm-p1`, and the finite-cover/gluing/base-change route stays.

## Where the brief, the DAG or earlier work was wrong

There was no mathematical defect in the statement or gluing interface. The old
proof plan requested a more general immersion-independence result than is needed:
reduce the actual base-changed domains, retaining explicit maps to them. This
also avoids any separate scalar-linearity or inverse-image/restriction argument.
The old `LocallyClosedStratification` docstring says its underlying structure has
no constructibility condition; the current `Stratification` does have that field.
The proof uses the current record and does not change this shared definition.

The server has no compiled `Mathlib.Tactic.Tfae` module, so the proof uses the
already imported theorem `List.tfae_of_cycle` directly. This required no tool
change or additional build.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
