## What changed

Proved AlgebraicGeometry.Scheme.Modules.scalar_moduleCohomologyPullback_comparison in
Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison, preserving its exact
statement and both original public imports.

The proof works with the actual choices of moduleCohomologyFMap. Scalar restriction
preserves injectives, and scalar direct image preserves injectives because inverse image
is exact. Thus the scalar image of the chosen comparison quasi-isomorphism has a homotopy
inverse. Its composite with the chosen horizontal lift has the required augmentation.
Adjunction, the Ext cocycle roof formula, and evaluation at 1 identify scalar pullback
with the same map on resolution homology. The final calculation includes the forgetful
homology isomorphisms appearing in ModuleCohomologyFMapData.map.

All auxiliary constructions and lemmas are private and proved in this module.
The added Sheaf proof imports are
Sheaf.AlgebraicGeometry.FieldScalarRestrictionInjectives and
Sheaf.CategoryTheory.ExactFunctorResolutionCocycle. The latter supplies the existing,
proved exact-functor cocycle calculation with independent Ext universes. The added
Mathlib.Algebra.Homology.ConcreteCategory import supplies concrete cycle constructors.
The nonnegative injective-complex homotopy-inverse theorem is already publicly
available through the original imports. Updated the existing node's proof,
proof dependencies, and origin.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.Scheme.Modules.scalar_moduleCohomologyPullback_comparison.

Holes closed: 1. Holes added: 0. Split-offs: 0.
No declaration in the delivered module contains sorry. A #print axioms command run
inside the completed module reports only propext, Classical.choice, and Quot.sound;
the proved theorem has no inherited sorryAx either.

First-worker validation: the original completed proof compiled without warnings
(42.7 seconds), and its dry run printed OK. Independent validation of the shortened
proof and delivery is recorded below.

## No longer needed

No original import or original proof-dependency node was removed: the field-linear
operations and the module cohomology map are both required.

Second reading also removed the added proof imports
WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap (its duplicate roof
calculation was replaced) and Mathlib.Algebra.Homology.DerivedCategory.KInjective
(already publicly reachable through both original imports). These were not original
proof dependencies; no original import or dependency node was pruned.

The signed tensor-pairing alternative in the old node's proof is unnecessary.
In particular, this proof does not use def-sc-module-cohomology-cup-product
(Sheaf.Paper.ModuleCohomologyCupProduct), despite its appearance in the original
statement-dependency metadata. It also requires no comparison through cohomology of
underlying abelian sheaves. No claim is made that these modules are unreachable from
other targets.

Removed unused private experimental helpers moduleSection_comp, scalar_sections_obj,
and scalar_pushforward_sections. Removed redundant experimental imports
Sheaf.Topology.RingedSpaceModuleCohomology and Mathlib.AlgebraicGeometry.Modules.Sheaf;
the two original public imports already expose what the proof uses from those modules.

## Where the brief, the DAG or earlier work was wrong

The statement is valid without extra hypotheses, including degree zero, empty schemes,
and zero coefficients. No definition, statement, public visibility, or other module was
adapted. The proof-context change record is
coord/changes/scalar-module-cohomology-pullback-proof-context.md.

The original plan omits the comparison of its different chosen resolutions. Scalar
restriction preserving injectives and the homotopy inverse of the restricted vertical
comparison provide that missing argument. The Ext roof calculation must allow the
module Ext universe w and the scalar Ext universe w+1 to differ; the private calculation
now uses the existing proved generic theorem with independent universes. The DAG
proof records these steps explicitly.

## Second reading by B2

1. Compared the sole delivered module and node with the repository versions.
   PASS: restored the conclusion's original line layout, making the existing theorem
   signature byte-for-byte identical. Both original public imports are unchanged;
   every added import is private to the proof. No existing definition, public
   visibility, target, or other module changes. The context change record documents
   only local instances, names, and extra private-helper universes.

2. Read the entire proof, including resolution transport, the homotopy inverse,
   augmentation at degree zero, evaluation at 1, and forgetful homology maps.
   PASS: the original proof compiled cleanly. All new definitions construct data
   explicitly; the chosen resolution data and adjunctions come from proved results.
   No forbidden declarations or holes occur in the module. The shortened proof's
   independent compile and axiom check are recorded below.

3. PASS: no split-off statements, new public declarations, new nodes, or holes.
   Checked the private reductions at degree zero (no negative homotopy term), zero
   coefficient modules, empty schemes, and identity scheme maps; the construction
   requires no nonzero cycle, point, flatness, or positive-degree hypothesis.
   Searched Mathlib using Lean Finder, Loogle, and grep with resolution-cocycle
   queries, and searched Sheaf/upstream sources with Ext and pullback terminology.
   Found the proved exactFunctor_resolution_cocycle, which accepts independent Ext
   universes and removes the duplicate derived-category roof calculation.

4. PASS: replaced the duplicate calculation by the existing generic tool and
   Mathlib's Ext associativity and mk₀_comp_extMk. Removed the now-unneeded added
   ExtendMap import and the redundant added KInjective import. Kept the two original
   proof dependencies, so no original dependency node or module is pruned.
   Inspected dag/units/sk-prop-av-cube.json: this node is a lower-level comparison
   helper, not a realized unit step. The unchanged unit route is respected; the
   added cross-unit dependency is a proved generic tool, not an alternative unit
   argument. No claim is made that other targets cease to reach any module.

5. PASS: only proof, proof_deps, and proof_origin change in the existing node.
   The steps describe the final Lean argument, including the generic cocycle tool;
   proof_deps is exactly the union of their uses. The statement, lean.statement,
   unit, chapter, blueprint, and source remain unchanged. No new-node fields apply.

Second-reading changes: restored exact signature formatting; replaced the private
integer-complex Ext roof calculation and its extension wrapper by the existing
proved generic cocycle theorem plus Mathlib source precomposition; removed two
unneeded added imports; updated the proof metadata, context record, and this report.

Independent validation: the final proof in a scratch copy compiled without warnings
in 47.7 seconds. #print axioms scalar_moduleCohomologyPullback_comparison reports
only propext, Classical.choice, and Quot.sound, with no sorryAx. The final module
contains zero sorry tokens and zero forbidden declaration forms; all lines fit the
100-character limit. The original signature matches byte-for-byte, and the node's
proof_deps equals the union of its proof-step uses.
