## What changed

The statement of
AlgebraicGeometry.Scheme.lisse_tower_compatible_stalk_markings is unchanged.
Its proof constructs the covering sieve from finite_lisse_tower_section_cover,
evaluates compatible sections, and uses NatTrans.ofOpSequence and naturality
to obtain all comparable-index squares.

Sheaf.Paper.LisseTowerIsomorphismSections isolates the finite-level Isom-sheaf
construction, its reduction maps, and consecutive evaluation squares. It chooses
neither a common covering nor compatible sections. This is the finite-level
part of original proof steps 1 and 2, not the original conclusion renamed.

Sheaf.Paper.ConstantAdicRestrictedTower builds a genuine sequential diagram
from the existing actual consecutive transitions. Its map theorem identifies
every sequential map with the actual all-pairs arrow. The proof uses
sectionwise scalar-compositor identities, mate pasting, exact localization,
M.cocycle, and invertibility of the equal-index arrow. No local-system or
stalk-model assumptions occur in this module.

All added imports of the item are private proof imports. No existing shared
definition, statement, public import, or adopted source-library module changes.

## Proved and sorry left

Closed the item's one original hole:
AlgebraicGeometry.Scheme.lisse_tower_compatible_stalk_markings.
Its complete assembly proof depends on the new finite-level theorem below.

Added one hole:
AlgebraicGeometry.Scheme.lisse_tower_isomorphism_sections,
node lem-weil-pbc-lisse-tower-isomorphism-sections.
It has its source and full natural-language argument in its docstring.

The scalar-coherence theorem
AlgebraicGeometry.Scheme.constantAdicRestrictedTower_map and its private
helpers are proved without new holes. The definitions contain no holes.

This is a decomposition of the original obligation, not an unconditional
proof of the mathematical theorem: one upper hole closed, one lower hole
added; one hole remains in the delivered modules.

## No longer needed

No Lean module is withdrawn, and no global pruning is claimed.

The item's proof no longer uses
lem-weil-pbc-compatible-finite-derived-trivializations
(Sheaf.Paper.CompatibleFiniteDerivedTrivializations). Instead it applies the
existing proved finite_lisse_tower_section_cover directly to the finite-level
Isom data. The quarantined module and its node are preserved.

The original direct dependencies
lem-weil-pbc-finite-ring-derived-local-constancy,
prop-weil-pbc-site-comparison-finite-level,
def-weil-pbc-proetale-modules,
lem-weil-pbc-comparison-pullback,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
def-weil-pbc-bounded-constructible-tower,
lem-weil-pbc-constant-adic-quotient-scalar-comparison, and
def-weil-pbc-constant-adic-finite-diagram-data are represented through the
new finite-level Isom statement or scalar-coherence module. Their mathematics
is still needed there; they are not claimed globally unused.
No preexisting import was removed from the item.

## Where the brief, the DAG or earlier work was wrong

The old plan refers to CompatibleFiniteDerivedTrivializations, whose Lean
module is quarantined rather than live. Its archive was read and preserved.
The present proof uses the live finite-lisse section-cover theorem instead;
the Isom-sheaf identification and consecutive evaluation are stated
separately. No absence from lean/ was treated as withdrawal authorization.

No counterexample to the item or statement change is asserted. The empty
base is handled by the covering theorem; the proof does not need an
inhabited index type. Zero levels present no separate issue. Equal indices
in the all-pairs square are handled using invertibility and the cocycle,
not an unjustified faithfulness claim for derived quotient restriction.

## New nodes

lem-weil-pbc-lisse-tower-isomorphism-sections records the strictly finite-level
construction and evaluation of Isom sheaves, before choosing any compatible
sections. Its sole theorem is the remaining hole.

lem-weil-pbc-constant-adic-restricted-tower-maps records the explicit sequential
diagram and its all-pairs map formula, independent of markings or covers.
It also attaches constantAdicRestrictedStep and constantAdicRestrictedTower.

The item node's proof, proof_deps and proof_origin now follow the assembly
proof. No other existing node changes and no change record is required.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
