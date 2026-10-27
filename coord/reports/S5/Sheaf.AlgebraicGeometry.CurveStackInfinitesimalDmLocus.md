## What changed

Repair of the return at head `739bb9f02`: removed the duplicate private
`CategoryTheory.fullModuli_isHomLift` from `OpenModuliDiagonalRestriction`.
The original helper in `OpenModuliSubstackAlgebraicity` is now public, with explicit
independent object and morphism universes. The diagonal restriction module imports
that module privately and uses the shared theorem in both directions. Its DAG proof
dependency records this reuse. No new hole or duplicated theorem was introduced by this repair. Current main has also
acquired `CategoryTheory.openStackAlgebraicLfp` in `OpenStackAlgebraicLfp`, with
the exact generic algebraicity conclusion needed here. Removed the retained packet's
duplicate `openModuliMap_isAlgebraic_lfp` theorem and its hole; the full-open
specialization now imports and applies `openStackAlgebraicLfp`. The existing node's
current attachment, proof and maintainer metadata are preserved verbatim.

Replaced the proof hole in `Sheaf.AlgebraicGeometry.CurveStackInfinitesimalDmLocus`
with a complete Lean assembly of the existing largest-open, stabilizer and group-scheme
identity criteria. The target statement and `SchemePointIn` definition are unchanged.
All new proof imports in the item are private.

Proved `CategoryTheory.OpenModuliSubstack.hasUnramifiedDiagonal_of_contained` in
`OpenModuliDiagonalRestriction`: construct the inverse comparison between the two
iso-comma categories through the full inclusion, prove it fully faithful and essentially
surjective, and retain both diagonal projection comparisons.

Proved invariance of `HasTrivialInfinitesimalAutomorphisms` under presheaf isomorphisms
over the geometric field, using the induced pullback isomorphism and conjugation.
Proved that a full pullback-stable subcategory is fibred in groupoids, including the
strongly cartesian universal property. These proved private helpers supply the actual
glue in the main theorem and the full-open algebraicity specialization.

Added the full-open specialization in `OpenModuliSubstackAlgebraicity`, proved
from current main's generic theorem `openStackAlgebraicLfp` attached to the existing
node `lem-sfb-open-stack-algebraic-lfp`. The specialization uses its algebraicity
clause; the existing theorem also retains the node's locally-finitely-presented
atlas clause.
No existing declaration signature was changed, and no existing module was adapted.

Separated the geometric containment, proper-scheme realization and stabilizer
comparison arguments into individual public theorems/modules. Each has its source,
full proof in words, edge-case discussion and matching node. These results are
independent parts of the argument: none constructs a largest open or restates the
item theorem. The stabilizer comparison supplies the classifying point, naturally
represented group, field-to-chart comparison and identity-point comparison; the main
proof itself applies the existing field-point stabilizer and dual-number criteria.

Validation: all six modules compiled together through `lcompile.py --all`; the main
module has no `sorry`. The source-library tree and all public imports of existing
modules were preserved. Empty curves and empty opens, arbitrary characteristics,
nonreduced automorphism groups and algebraic-space geometric objects were retained.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.exists_curveStack_infinitesimal_dm_locus`.
This is a **decomposition**, not a proof free of lower holes: one original hole closed,
three lower theorem holes added, net -2 before the project's pinned-closure ledger.

The item has zero remaining holes. The delivery has exactly three remaining holes,
each the entire proof of the following public theorem:

- `AlgebraicGeometry.ProperCurveModuli.open_containment_of_geometric_points`,
  node `lem-sfb-proper-curve-geometric-containment`.
- `AlgebraicGeometry.ProperCurveModuli.exists_scheme_family`,
  node `lem-sfb-proper-curve-scheme-realization`.
- `AlgebraicGeometry.ProperCurveModuli.exists_stabilizer_comparison`,
  node `lem-sfb-proper-curve-stabilizer-comparison`.

The repair removes the former packet's added hole
`CategoryTheory.openModuliMap_isAlgebraic_lfp`; it reuses the existing
`CategoryTheory.openStackAlgebraicLfp` without changing that theorem or its hole.
`OpenModuliSubstack.isAlgebraic` and the full-subcategory fibredness proof have no
local holes.

New public theorem proved without a hole:
`CategoryTheory.OpenModuliSubstack.hasUnramifiedDiagonal_of_contained`,
node `lem-sfb-open-moduli-diagonal-restriction`.
The shared public hom-lift helper and the private helpers for infinitesimal
automorphism transport, isomorphism invariance, strongly cartesian arrows and
fibredness are all proved.
No `sorry` occurs in data, a definition, an instance or an anonymous proof branch.

## No longer needed

The duplicate local `fullModuli_isHomLift` proof in `OpenModuliDiagonalRestriction`
is removed; all of its uses now refer to the single shared public theorem in
`OpenModuliSubstackAlgebraicity`. The packet's generic
`openModuliMap_isAlgebraic_lfp` and its separate proof obligation are also removed;
the existing `OpenStackAlgebraicLfp` module supplies that statement.

No existing module or node is withdrawn, and no original import is removed.
The original six dependencies remain mathematically needed. In particular,
`lem-sfb-proper-curve-automorphism-scheme` is needed by the new stabilizer-comparison
node: its import is not placed directly in the main module because the main proof
uses the comparison interface. It is not pruned.

Removed exploratory proof imports of `Mathlib.CategoryTheory.FiberedCategory.Fibered`
and `.Cartesian` from the item, since it no longer contains those helpers; the required
API is already exposed by the statement imports of the algebraicity module. Removed
the exploratory direct import of `ProperCurveAutomorphismScheme` from the item.
No progress is claimed for pruning modules.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically sound, but its statements do not directly supply
several comparisons its assembly needs. In particular, an `OpenModuliSubstack` stores
fibredness of its ambient category, not its own full-subcategory projection. Algebraicity
of the open therefore cannot simply be extracted from that structure. The requisite
full-subcategory fibredness is proved here; the general representable-open algebraicity
result was already a DAG node. Its current Lean attachment
`OpenStackAlgebraicLfp` is now reused instead of the packet's duplicate statement.

`exists_proper_curve_automorphism_scheme` uses an algebraic space over the geometric
field and automorphisms on slice sites, whereas the curve stack stores an algebraic
space over k with a map to the represented field and uses literal presheaf pullbacks.
`IsModuliAutomorphismSpace` additionally asks for naturality on every test scheme.
The comparison theorem records that missing slice-site/fibred-Yoneda work explicitly;
using the representation theorem's existence conclusion alone would not prove it.

Likewise a proper scheme was not already supplied as a `ProperCurveFamily`, and the
geometric-point containment step needs the pullback open and the fibred Yoneda
comparison, rather than just a pointwise implication. These are the remaining separate
source arguments. The generic permanence theorem `dm_open_finite_etale_permanence`
is not applicable: it assumes a finite diagonal and finite-type smooth atlas, which
are not hypotheses for the stack of all proper curves here.

Edge cases checked for the retained statements: the empty represented scheme and
empty open admit empty atlases; all property transport is over the specified field;
no smoothness of the automorphism group is used; the identity-reduction equation fixes
the dual-number base, not the projection to the original curve. The unit's realization
route is unchanged. No statement was disputed or weakened.

## New nodes

`lem-sfb-full-open-substack-algebraicity` records the proved specialization
`OpenModuliSubstack.isAlgebraic` and its shared hom-lift helper. Its proof first
constructs full-subcategory fibredness and then applies current main's generic
`openStackAlgebraicLfp`. It adds zero holes. The first repair preflight required
this attachment because `OpenModuliSubstackAlgebraicity` is a new module; the
existing generic algebraicity node stays unchanged.

`lem-sfb-open-moduli-diagonal-restriction` is the proved full-inclusion comparison of
diagonal scheme tests. `lem-sfb-proper-curve-geometric-containment` states detection
of open containment by geometric proper-curve objects. `lem-sfb-proper-curve-scheme-realization`
records the represented proper-scheme family. `lem-sfb-proper-curve-stabilizer-comparison`
records the source's natural automorphism/stabilizer and dual-number comparisons.
Each new node has its Mathlib searches, statement dependencies, source and proof steps.
The already existing `lem-sfb-open-stack-algebraic-lfp` retains its current main
Lean attachment to `OpenStackAlgebraicLfp`; its stale sandbox copy is omitted from
this repair. No change record is needed: existing statements and definitions
have not changed.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
