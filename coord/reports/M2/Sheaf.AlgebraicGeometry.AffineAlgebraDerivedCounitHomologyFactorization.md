## What changed

Proved `AlgebraicGeometry.affine_algebra_derived_counit_homology_factorization` with
its signature unchanged. Exact scalar restriction compares the algebra derived image
with scheme derived image. The affine cohomology comparison proves algebra
quasi-coherence and reflection of isomorphisms on quasi-coherent complexes. The existing
unit factorization and right triangle identity then show the derived counit is
invertible. Composing its homology isomorphism with the inverse of the underived counit
produces the required existential source comparison; inverse cancellation proves the
factorization equation.

Added proof-only imports for the existing affine module adjunction isomorphisms,
derived unit factorization, derived pullback quasi-coherence, natural acyclic-pushforward
cohomology comparison, affine higher-image vanishing, exact right-derived comparison,
bounded-below/unbounded single-object comparison, and sheafification instances. The
original public imports and declaration visibility are unchanged. A scoped heartbeat
limit covers the sheaf-category elaboration of the scalar-restriction comparison.
Updated the existing node's proof, proof dependencies and proof origin to match.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affine_algebra_derived_counit_homology_factorization`
(node `lem-sc-affine-algebra-derived-counit-homology-factorization`).
No `sorry` remains in the delivered module. No holes, public declarations, modules,
or nodes are added. This is a proof from existing declarations, including existing
holed dependencies; it does not claim that the entire transitive closure is sorry-free.

The proof uses the existing holed statements
`AlgebraicGeometry.affine_algebra_module_adjunction_isos` and
`AlgebraicGeometry.affine_algebra_derived_unit_homology_factorization`; these are not
new holes of this delivery. Their statement modules are the next work, as stage 3 intends.

## No longer needed

Removed the old proof dependency node `lem-pc-ringed-spaces-derived-adjoint-general`
from the direct proof route, and the direct proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`:
this proof uses derived pullback quasi-coherence as an existing interface, rather than
constructing a derived adjunction itself. This module remains reachable through that
interface; no global pruning of it is claimed.
Removed the redundant direct proof import `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`:
the statement dependency `DirectImageAlgebraDerivedCategory` already publicly imports
it, and its theorem is still used. It is not pruned from the mathematical dependency graph.
Removed the redundant added proof import `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
the used affine higher-direct-image module publicly imports Proper, which publicly
imports Separated. No existing node is made globally unnecessary. No separately stated compatibility of
canonical derived counits with cohomology is needed for this existential conclusion.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan asks for a canonical counit-compatible cohomology comparison.
The Lean conclusion asks only for existence of an isomorphism e satisfying one equation.
After proving both counits invertible, this e is their composite with an inverse, so
no canonical derived-counit compatibility lemma is required. This is a shorter route
below the unit level. The unit `sk-thm-picard-duality` has no realized statement or step
attached to this node, and its route is unchanged.

Checked [Stacks Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW), especially its
K-injective scalar-restriction comparison, flat pullback, unbounded affine cohomology
formula and underived module correspondence. The triangle-identity argument is the
categorical simplification of the final counit step. The local literature source is
not present in this clone, so the cited Stacks page was read directly. Searches with
LeanFinder (affine direct-image-algebra cohomology comparison), Loogle
(`Adjunction.right_triangle_components`, `NatIso.isIso_map_iff`) and Mathlib grep
(`counit.*homology.*factorization|algebra.*derived.*homology`) found no direct theorem
that bypasses the existing interfaces. Local library search found the analogous proof
in `AffineDerivedCounitHomologyFactorization` and the scalar-restriction comparison
in `FiniteAffineDerivedEquivalence`. The latter module cannot be imported here because
it reaches this item, so only its generic comparison constructions are used.

The proof imposes no boundedness, nonzero ring, nonempty scheme or surjectivity
hypothesis. The auxiliary O_Y derived category is the standard one, and is not added
to the theorem's hypotheses. All comparisons also apply to identity morphisms, zero
complexes and empty schemes.


## Second reading by M2

1. Compared the sole delivered Lean module with the repository by diff. The existing
   theorem signature is byte for byte unchanged, as are all three public imports and
   the exposed public visibility. There are no changed definitions or change records.
   Verdict: pass.
2. Read the scalar-restriction, cohomology-reflection, unit, triangle-identity and
   inverse-cancellation arguments. Local compilation passed with no warnings (57.2 s
   after an initial wall-clock timeout). No sorry or forbidden declaration occurs in
   the delivered module. The explicit axiom probe is recorded below. Verdict: pass
   subject to the delivery tool's final compile and axiom checks.
3. No statements or nodes were split off or added. Existing comparisons are used only
   through their stated interfaces. The standard auxiliary derived category is a real
   construction; the existential isomorphisms are uniquely determined up to the equality
   used, and no arbitrary data definition is introduced. Identity maps, zero complexes
   and empty schemes require no extra assumptions. Verdict: pass.
4. Searched the library for affine derived counit and reflection results and Mathlib
   with `reflectsIsomorphisms.*(derived|qcoh)|counit.*IsIso`. Found no theorem replacing
   the affine reflection argument; the analogous affine-scheme proof also uses a unit
   and triangle identity. All public imports serve the signature, and added imports are
   proof-only. The old proof dependency removed from the route is now explicitly named
   under No longer needed. The unit's realized statement and step lists attach no node
   to this item, so its route is unchanged. Verdict: pass.
5. Diffed the existing node: only proof, proof_deps and proof_origin changed. The uses
   union equals proof_deps and follows each part of the actual Lean proof. The statement,
   source, Lean signature and blueprint membership stay unchanged. Verdict: pass.

Second reading changed the theorem's natural-language proof to describe the actual
triangle-identity route, and completed the report's removed-node accounting. It removed the redundant direct Separated import. It did
not change the Lean proof or any signature, add holes or add nodes.

Axiom probe: `#print axioms
AlgebraicGeometry.affine_algebra_derived_counit_homology_factorization` compiled
successfully in 57.9 s and printed exactly `propext`, `sorryAx`, `Classical.choice`,
`Quot.sound`. The existing holed dependencies account for `sorryAx`.
