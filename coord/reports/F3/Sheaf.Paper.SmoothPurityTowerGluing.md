## What changed

Reduced AlgebraicGeometry.ProEtale.SpTowerGluing.tower_gluing to the geometric global
chart-adjunction step and the finite-compatibility step. The original theorem has
exactly its original signature. Its combination proof supplies compact-support
preservation from sp_tower_bound, applies the two separate assembly theorems at the
same adjunction, and proves uniqueness of every counit-preserving isomorphism.
The private counit_unique_iso proof explicitly constructs the two transposes,
proves them inverse with the two Hom injectivities, and proves Iso uniqueness.

Extracted every existing definition through Charts verbatim into
Sheaf.Paper.SmoothPurityTowerGluingData, publicly re-exported from the original item,
so the two new statement modules can mention the interface without a cycle.
The byte comparison of the complete moved declaration block passes. Definition
bodies, fields, names, visibility and attributes are unchanged. The new data module
has zero holes and makes no choice from an unproved existence statement.
All thirteen downstream modules retain the same definitions and need no edits.

Validation: server compilation of the data and both new statement modules succeeds.
All four delivered modules, including the final item, compile successfully through
lcompile.py --all. The first delivery preflight found a definition-node signature
attachment containing the structure body; this metadata was corrected to the exact
Charts signature before the successful delivery preflight.
The two statements were checked against empty source, d=0, equal coefficient indices,
ramified coefficients and arbitrary finite test objects. The first omits all finite
exceptional adjunction/reduction assertions. The second assumes the actual adjunction
and normalized Charts and supplies only its finite compatibility. Neither statement
alone is the original theorem under another name; their combination and uniqueness
argument are Lean proofs, rather than a new alias for the old existence claim.

## Proved and sorry left

Original item: one hole, tower_gluing. Its proof is now complete from the two named
assembly statements and the existing sp_tower_bound declaration. Its preservation
and unique-isomorphism arguments are proved in the item. This is a decomposition,
not a claim to have proved the geometric descent and finite-compatibility steps.

Holes closed: AlgebraicGeometry.ProEtale.SpTowerGluing.tower_gluing
(node det-sp-tower-gluing).

Holes added and remaining:

- AlgebraicGeometry.ProEtale.SpTowerGluing.tower_global_chart_adjunction,
  node lem-sp-tower-global-chart-adjunction, in its own new module.
- AlgebraicGeometry.ProEtale.SpTowerGluing.tower_chart_adjunction_levels,
  node lem-sp-tower-chart-adjunction-levels, in its own new module.

There are zero sorry in the item and shared data module, and two in the new statement
modules. Both are public named theorems whose entire proofs are sorry. Each has its
source, a complete natural-language proof, its blueprint tag and matching DAG node.
The existing dependency sp_tower_bound is not changed or counted as a new hole.
Net packet holes: one closed, two added, net minus one. No axiom or hollow definition
is added. No existing dependency proof or adopted source declaration is changed.

## No longer needed

No mathematical node or module is pruned. All seven original proof dependencies
remain used by the new assembly nodes. The item now needs directly only the shared
interface and proof imports SmoothPurityTowerBound,
SmoothPurityTowerGlobalChartAdjunction and SmoothPurityTowerChartAdjunctionLevels.
Its two former proof imports SmoothAdmissibleCoordinateCover and
SmoothPurityTowerBinaryCtfFibre are absent from the shared definition module; they
remain required by the geometric assembly's proof plan. Every original public
import is retained in the shared data module, hence re-exported by the original.
No Lean module is withdrawn and no deleted.txt is supplied.

## Where the brief, the DAG or earlier work was wrong

The dependency lemmas provide substantial local, binary, finite and transpose data,
but none directly states either of the two final assembly conclusions. The global
chart record additionally asks for an etale graph normalization and the full dependent
ConstructionAt predicate at its actual chart family. Those data are retained in
the geometric assembly, with explicit construction instructions. The finite assembly
must also supply the ReductionExceptionalRealization for each chosen finite
adjunction; an arbitrary isomorphism of right functors is insufficient.

The source-library search found no replacement theorem. The semantic Mathlib searches
found ordinary sheaf adjunctions and generic constructors; the generic Hom-equivalence
API is used for uniqueness. The unit route remains the same: coordinate construction,
finite-cover descent, representability/functoriality, then finite evaluation and
coefficient mates. No failure of the brief or tool is alleged.

## New nodes

lem-sp-tower-global-chart-adjunction states the geometric global chart adjunction,
conditional on the separately obtained compact-support preservation. Its proof plan
retains admissible charts, uniform intervals, the graph-normalized coordinate pairs,
binary fibre/counit gluing and functorialization by transposes. It does not contain
the Levels conclusion.

lem-sp-tower-chart-adjunction-levels assumes a given tower adjunction and its actual
normalized Charts. It states only the finite adjunction/realization, evaluation,
unit/counit and coefficient-mate reduction compatibility. Its plan applies the
existing finite evaluated representability and reduction-transpose declarations.

def-sp-tower-gluing-interfaces owns the unchanged shared declarations, previously
attached to the parent theorem module. It is a zero-hole definition extraction and
adds no mathematical datum. The parent attachment now records only tower_gluing.

Change record: coord/changes/F3-smooth-tower-gluing-interfaces.md.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
