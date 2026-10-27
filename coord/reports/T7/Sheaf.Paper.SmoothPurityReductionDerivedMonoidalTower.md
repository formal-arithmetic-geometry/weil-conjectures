## What changed

Reduced sp_reduction_derived_monoidal_tower to three genuine steps of its original
proof: strict ordinary/signed-total balancing, localization of those prescribed
maps with normalized monoidal coherence, and compatibility with geometric pullback
for already specified endpoint towers. The assembly proof constructs both endpoint
closed tensor models using ringedDerived_closed_symmetric_monoidal, constructs the
comparison record, and makes the simultaneous choice only inside a theorem proof.
No public definition selects arbitrary data from an unproved existence theorem.

Proved the total_kflat and level_kflat obligations directly from existing theorems.
The latter uses the existing stronger independent-coefficient K-flat scalar theorem,
so it does not need flatness of the coefficient map or even the supplied flat-term
hypothesis. Strict forward/inverse/summand fields and all derived fields are explicitly
assembled into SpReductionMonoidalTower. The geometric lemma is parameterized by
those same already constructed endpoint towers.

Moved all 47 original interface declarations, preserving their source text verbatim
except blueprint doc tags, into SmoothPurityReductionMonoidalData. The original item
publicly re-exports it. This is required to avoid an import cycle with the three
independent proof-step modules. It is not a timeout workaround. No source-library
module is modified, no existing mathematical statement or definition changes.

Change record: coord/changes/T7-reduction-monoidal-interface-location.md.
The unit's realized statement/step arrays are empty; its integral adjunction and
reduction route is retained. No unit step or DAG parent is bypassed or withdrawn.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.sp_reduction_derived_monoidal_tower
(lem-sp-reduction-derived-monoidal-tower), by a complete assembly proof.
The private total_kflat and level_kflat helpers are proved, with no sorry.

Added three holes, each exactly a public named theorem in its own module:

- AlgebraicGeometry.ProEtale.sp_reduction_strict_tensor_balancing
  (lem-sp-reduction-strict-tensor-balancing).
- AlgebraicGeometry.ProEtale.sp_reduction_tensor_comparison_descent
  (lem-sp-reduction-tensor-comparison-descent).
- AlgebraicGeometry.ProEtale.sp_reduction_geometric_tensor_square
  (lem-sp-reduction-geometric-tensor-square).

This is a decomposition: one upper hole closed, three strictly smaller comparison
steps left. The upper module has zero holes; the packet has three holes. No axiom,
hollow definition or sorry inside a partial proof is added.

## No longer needed

Removed the original private imports from the upper module:
Sheaf.Paper.SequenceSiteCompletionProjection,
Sheaf.Paper.KFlatRingedToposPullback,
Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients,
Sheaf.Algebra.Homology.ChangeOfRingsKFlat,
Sheaf.SixFunctors.RingedDerivedMonoidalComparisons.
The existing KFlatTotalTensorModel import remains used by total_kflat. The other generic comparison
modules remain mathematical dependencies of the split steps; none is globally
pruned. ChangeOfRingsKFlat is replaced for the level_kflat proof by
ChangeOfRingsKFlatAllIndependentCoefficients, because the latter applies directly to
the recorded scalar functor with independent coefficient universe.

All seven original public imports remain publicly accessible through the extracted
interface module. No existing module, node or declaration is withdrawn. The old
proof dependencies not used directly by the assembly are delegated to the named
strict/descent/geometric step nodes; none is claimed unnecessary in the target DAG.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is usable, but generic ringedDerivedMonoidalComparisons has
its Site interface with equal site object/arrow/coefficient universes, whereas the
actual pro-etale site has object/coefficient universe u+1 and arrow universe u.
Applying it requires transport plus normalized comparison identifications; it is
not a direct one-line application to this item. The descent and geometric split
statements expose those remaining genuine comparison arguments rather than moving
the entire original existential into a new theorem.

Checked edge cases in the new statements: zero modules and complexes, empty schemes,
identity geometric map and identity quotient transitions, and the nonflat quotient
map Z_l -> Z/l. The strict comparison uses balanced tensor identities, not flatness.
The descent fixes input models and strict maps and supplies no geometric comparison;
the geometric lemma assumes already supplied endpoint towers and constructs none.
This prevents any new statement from being the original theorem under another name.

Searches used leanfinder, loogle, leansearch, launcher grep and local rg. They found
ordinary/condensed monoidal structures but no existing coherent derived reduction
comparison. Local search found the two directly reused representative-class lemmas.

## New nodes

- def-sp-reduction-monoidal-comparison-data owns the relocated existing interface
  declarations only; no new mathematical operation and no existence hole.
- lem-sp-reduction-strict-tensor-balancing is the underived tensor and chain part of
  original steps 1 and 4; no derived comparison or geometric square.
- lem-sp-reduction-tensor-comparison-descent takes the strict comparison and fixed
  closed tensor models as input, and proves the derived comparison and normalization
  from original steps 1--5 and 8; no existence of endpoint tensors or geometric data.
- lem-sp-reduction-geometric-tensor-square takes both endpoint monoidal comparisons
  as input, and proves their geometric square from original steps 6--8.

Every new theorem has a full natural-language proof, source, edge-case check and
DAG record. The parent node proof and declaration attachment reflect the Lean proof.
The original statement and stmt_deps are preserved. The relocated declarations keep
all original semantics and public visibility.

Validation: lcompile.py --all compiled all five packet modules successfully, with
no errors or warnings. The original 47 interface declaration texts were compared
byte-for-byte after normalizing only their blueprint doc tags. The upper assembly
was compiled using all four new modules; both private representative-class proofs
were also separately compiled during development.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
