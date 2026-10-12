## What changed

Reduced AlgebraicGeometry.Etale.abelianHigherDirectImageClass_pullback without changing
its signature, definitions, or public imports. Added proof-only imports of
AbelianPullbackSingleComposition and AbelianDerivedDirectImageTransitionShift.

The proof performs the adjunction calculation with a proved private categorical lemma:
naturality of the second unit and the pullback comparison, counit naturality, and the
first adjunction triangle identity. It then uses shift compatibility of the actual derived
transition, applies homology via a proved categorical naturality lemma, and evaluates
composition of sheaf morphisms at the identity generator.

AbelianPullbackSingleComposition proves the abelian-coefficient single-complex coherence.
It reuses the generic private proofs in the already proved EtalePullbackSingleComp module;
that module's public theorem is specialized to ModuleCat coefficients and cannot be applied
to AddCommGrpCat. The proof now imports that module with `import all` and applies its existing private
plus_single_comp and plus_single_natIso directly. All seven copied generic helpers
were deleted; no existing module or declaration is changed.

AbelianDerivedDirectImageTransitionShift constructs the transition as an actual composite,
using the generic actual-composite definition Adjunction.transitionThrough. This representation
avoids expensive reduction of derived adjunction projections when instantiating the abstract
adjunction calculation. The repair first eliminates equality transport with subst, identifies
the concrete transition using a proved generic associativity helper, and closes evaluation
by exact rather than simplifying the concrete adjunction structures. This fixes the earlier
60-second timeout; the main module compiled in 18.8 seconds. Its shift theorem is the single remaining intermediate hole.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.Etale.abelianHigherDirectImageClass_pullback
(node lem-sbc-abelian-higher-direct-image-class-compatibility) by decomposition.
Proved AlgebraicGeometry.Etale.abelianPullbackSingleComposition
(node lem-sbc-abelian-pullback-single-composition), by applying the existing generic
private lemmas in EtalePullbackSingleComp, without duplicating their statements.

Added one hole: AlgebraicGeometry.Etale.abelianDerivedDirectImageTransition_shift
(node lem-sbc-abelian-derived-transition-shift). This statement has arbitrary complexes and
integer shifts and concerns only the derived transition. It has no raw class, homology,
representable, generator, or section evaluation. The main proof genuinely combines it with
the proved single-complex coherence, adjunction triangle, homology, and evaluation calculations.
No sorry remains in the item's module or in a definition. One original hole closed and one
new hole added is a decomposition, with net hole count zero, not an axiom-free final proof.

## No longer needed

Removed redundant direct proof imports:
- Sheaf.AlgebraicGeometry.DerivedCategories.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction.
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.

The main proof uses the derived-category functors, exact inverse images and derived adjunctions
through the retained transition interface. The old direct proof dependency def-weil-pbc-derived-inverse-image is replaced
by lem-sbc-abelian-pullback-single-composition and lem-sbc-abelian-derived-transition-shift;
it remains a transitive dependency of those helper nodes.
No original dependency node is globally pruned;
the exact-functor and adjunction modules remain reachable transitively. DerivedCategories is
not needed by this proof: its coefficient/torsion definitions do not occur here.
The new modules import MorphismDefs directly, avoiding an unused AbelianHigherDirectImageMap
import in both modules.
Deleted seven duplicated private declarations from AbelianPullbackSingleComposition:
CategoryTheory.Functor.single_hom, complex_single_comp, derived_single_comp,
complex_single_natIso, derived_single_natIso, plus_single_comp and plus_single_natIso.
Their original declarations and proofs remain in EtalePullbackSingleComp, now imported
only for this proof. Removed the unchanged sandbox copy of EtalePullbackSingleComp
from the delivery. No modules are globally pruned by this repair.

No additional geometric finiteness, cohomology continuity, or sheafification comparison
isomorphism lemma is imported.

## Where the brief, the DAG or earlier work was wrong

The node's first step compresses two coherence calculations. The single-complex composition
calculation already has a proved generic implementation in EtalePullbackSingleComp, but its
exported result fixes module coefficients. The current item uses abelian coefficients, so the
first delivery copied the generic helpers. The return correctly rejected that duplication.
The repair uses `import all` to access the existing generic helpers directly; their
private visibility does not require copying or changing them.

The unit record sk-lem-failure-field has no realized nodes for this calculation, and its
geometric route is preserved. Both new nodes serve the same canonical-comparison step as the
original node's blueprint ancestor sbc-lem-higher-direct-image-limit. The blueprint search
for single-composition and transition-shift comparisons found no matching imported node.

Read Stacks Tags 09Z1 and 03Q8: these establish the canonical sectionwise comparison and its
use in the limit theorem; the explicit categorical coherence equations here are elaborations
of that comparison, not quotations of separately numbered statements in those tags.
The shift statement was checked for arbitrary integer shifts, identity maps and zero complexes:
it is formal functor/adjunction coherence and requires no geometric assumptions.

The resumed attempt also ran LeanSearch for exact-derived single-complex composition and
for derived-adjunction transition shift compatibility. Both calls returned Internal Server
Error and are recorded as unavailable without a mathematical verdict.

Searches actually run through msearch: leanfinder for derived-adjunction/inverse-image/shift
compatibility and for single-complex composition; loogle for homEquiv_naturality_left_symm and
shift_app_comm; grep for derivedPlus_unit_comp, upperStarPlusComp, homEquiv_naturality, and
bounded-below derived adjunction shift compatibility. Additional local rg found the proved
module-coefficient composition calculation. No exact abelian shift-transition theorem was found. The resumed search also found
DerivedAdjunctionCommShift.derivedPlus_upperStarLowerStar_commShift, which states the
unit/counit part but does not supply shift coherence for upperStarPlusComp. The remaining
hole groups those coherence steps; it does not duplicate the original class-compatibility goal.

## New nodes

lem-sbc-abelian-pullback-single-composition: the proved equality of the two source factors
on an arbitrary abelian sheaf in degree zero. Module AbelianPullbackSingleComposition.
Its proof dependency is now lem-sbc-pullback-single-comp, whose existing generic
private coherence lemmas are used directly; its statement and Lean record are unchanged.

lem-sbc-abelian-derived-transition-shift: compatibility of the derived transition with integer
shifts for arbitrary complexes and a coefficient morphism; the only new sorry.
Module AbelianDerivedDirectImageTransitionShift. Its proof plan uses the existing
lem-weil-pbc-derived-adjunction-commshift for the unit/counit coherence; the remaining work
also includes the composition comparison. No change records or forced adaptations.

## Second reading by C1

1. Compared every delivered module with the repository version. Existing declaration
signatures and definitions are unchanged; the main target proof only changes its proof and
proof-only imports. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py`. There are no axioms, unsafe
features, or hollow definitions; the sole remaining `sorry` is the named split theorem
`AlgebraicGeometry.Etale.abelianDerivedDirectImageTransition_shift`. Verdict: pass.

3. Checked the split statement against identity maps, zero complexes, and arbitrary integer
shifts. It is a genuine derived-transition coherence statement, strictly simpler than the
target and not a restatement. Local searches found no existing declaration with this
statement. Verdict: pass.

4. Read the proof top-down. It uses the existing generic coherence lemmas, the new abelian
single-composition theorem, the named transition-shift split, homology naturality, and section
evaluation. The removed imports are proof-only and the report lists them; no globally unused
node is claimed. Verdict: pass.

5. The DAG records, Lean declarations, proof dependencies, and unit route agree. The new
split node has its source, proof plan, searches, and module record; the unit's realized route
is preserved. Verdict: pass.

Changed only this report by recording the second reading; no Lean code or DAG statements were
changed during review.
