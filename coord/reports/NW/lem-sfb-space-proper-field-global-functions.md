## Worker report

Module: `Sheaf.AlgebraicGeometry.SpaceProperFieldGlobalFunctions`.
Declaration: `AlgebraicGeometry.AlgebraicSpace.structureMap_globalSections_bijective_of_geometricallyReduced_connected`.
One theorem, with `sorry` as its entire proof. No definitions or axioms are added.
The node changes only in `lean`; its reviewed mathematical statement and split are preserved.

The inherited BLOCKED ending concerned stage 1, not this stage-2 delivery. The current
node is split and reviewed PASS but has no Lean record; coord/queue.tsv lists it in
stage 2. There is no repair note. The stage-handoff paragraph of coord/brief-stage2.md
explicitly authorizes stating this accepted split with deliver2.py.

Hypotheses and conclusion, clause by clause:

- The ground field is `(k : Type u) [Field k]`. `Z : AlgebraicSpace (Spec (CommRingCat.of k))`
  is an algebraic space over that field, not a scheme or a chosen atlas.
- The named structure morphism is `p : Z ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k))))`.
  Here the target is the actual representable fppf sheaf of Spec k over itself.
- Properness is `hp : MapIsProper p`, the recorded conjunction of separatedness,
  finite type, and universal closedness. No smoothness, irreducibility, Noetherian,
  finite-presentation or rational-point assumption is added.
- Every algebraically closed extension is quantified by
  `∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]`. All field maps are covered
  by the algebra structure and its algebraMap. The universe is the project's scheme
  universe, not an independent smaller universe; it includes AlgebraicClosure k.
- The base change is the actual sheaf pullback `Limits.pullback p.hom (...yoneda.map g)`.
  The map g is explicitly `Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))`,
  with domain `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))` and codomain
  `Over.mk (𝟙 (Spec (CommRingCat.of k)))`. Thus no arbitrary comparison or map is used.
- Reducedness is `∀ T : CostructuredArrow yoneda (...).obj, IsEtale T.hom →
  AlgebraicGeometry.IsReduced T.left.left`. These are exactly all objects of the
  small etale site of the fibre product, before bundling its algebraic-space proof.
  Mathlib's scheme reducedness tests the affine etale chart rings for nilpotents.
  This is the defining expression of `AlgebraicSpace.IsReduced` on those charts,
  not a second named notion or a condition only on the ground-field charts.
- Nonemptiness and connectedness are together
  `ConnectedSpace (Point (...).obj)`. Mathlib ConnectedSpace extends PreconnectedSpace
  and has a Nonempty field (Topology/Connected/Basic.lean:705). The point topology is
  the recorded atlas-final topology of def-a1-space-point-topology.
- The conclusion is `Function.Bijective (SheafOfModules.sectionsMap (moduleStructureMap p))`.
  `SheafOfModules.sections` consists of compatible chart sections; `sectionsMap` is
  literally the map induced on those sections. Its domain is Gamma(Spec k, O), and
  its codomain is Gamma(Spec k, p_*O_Z) = Gamma(Z, O_Z). The latter equality follows
  from the specified compatible-chart-limit model of moduleDirectImage. The former
  identifies canonically with k by Gamma-Spec. The chart projections in
  existsUnique_moduleStructureMap send a section to its regular-function pullback,
  so this is exactly the canonical constants map, including its unit normalization.
  It is already a unital ring map: each chart projection is regular-function pullback
  and the projections jointly detect the identities. Bijectivity of this map is
  equivalent to being an isomorphism of k-algebras with the structure-map action;
  the inverse preserves each operation by injectivity. No arbitrary algebra
  equivalence replaces the prescribed map, and no conclusion clause is omitted.

Statement dependencies read and used:

- def-weil-field: Mathlib `Field`, Algebra/Field/Defs.lean:180.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`, lines 470 and 479.
- def-trf-algebraic-space: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `IsEtale`, `EtaleSite`, `structureSheaf`, `Modules`.
- def-pc-field-extension: `Mathlib.Algebra.Algebra.Defs`, `Algebra` and `algebraMap`;
  the field instances make this a field extension. `IsAlgClosed` is Mathlib's
  polynomial-splitting definition, equivalent to the node's root condition.
- def-a1-space-point-topology: `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`,
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace` and the existing `Point`.
  This module is publicly imported through AlgebraicSpaceMorphismProperties.
- def-sfb-space-morphism-properties:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`, `MapIsProper`.
- def-sfb-space-module-structure-map:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`, `moduleStructureMap`,
  read together with existsUnique_moduleStructureMap and ModuleDirectImageModel.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, `schemeSpace`, supplies the
  representable target using its published construction. The pullback in sheaves
  exists by the public imports of AlgebraicSpaceMorphismProperties.

Every already-stated proof dependency is imported non-publicly: quasi-coherent
module, quasi-coherent pushforward, canonical flat direct-image base change,
Zariski/etale equivalence, affine pullback sections, algebraic closure, finite
extensions of algebraically closed fields, flatness of field extensions, basis
extension and tensor-product basis/scalar-extension results. The two proof nodes
lem-sfb-space-flat-proper-fp-locality and
lem-sfb-space-proper-connected-function-field have no recorded Lean statement;
no import is invented for them. All four proof steps are reproduced in the docstring.

Source read: literature/stacks-project/spaces-over-fields.tex,
lemma-proper-geometrically-reduced-global-sections (Tag 0DMY), all eight clauses
and proof, particularly (4), (5), (7). The source's wording 'geometrically reduced
and connected' in (7) means both properties geometrically, as its proof uses
geometric irreducibility. Our accepted node spells this out by all algebraically
closed extensions; the Lean follows that unambiguous version.

Edge cases checked before writing: Spec k satisfies the intended statement;
the empty space is excluded by ConnectedSpace.nonempty; two disjoint proper
components fail geometric connectedness. A nontrivial finite separable extension
has disconnected geometric fibre; a nontrivial finite purely inseparable extension
has nonreduced geometric fibre. Dual numbers fail reducedness. Reducible connected
reduced proper geometric fibres remain allowed: no irreducibility is imposed.
Positive characteristic and algebraically closed ground fields are allowed.
No counterexample or statement correction was found.

Searches for an existing statement (msearch.py NW, this item):

- leanfinder: "Global sections of a proper geometrically reduced nonempty connected
  algebraic space over a field equal the base field". Eight hits, led by
  AlgebraicGeometry.isField_of_universallyClosed, scheme function-field results,
  IsIntegral and scheme reducedness. No algebraic-space theorem.
- loogle: "AlgebraicGeometry.finite_appTop_of_universallyClosed, IsAlgClosed".
  Zero hits; no exact match.
- grep: "GlobalSectionsBijective|proper.*globalSections|globalSections.*proper".
  Zero hits in Mathlib.
- leansearch: "Global sections of the structure sheaf of a proper geometrically
  reduced connected algebraic space are the ground field". Eight hits including
  Scheme.ΓSpecIso, isField_of_universallyClosed and scheme structure-sheaf formulas;
  no algebraic-space theorem.
- rg of lean/WeilConjectures and lean/Sheaf for the item id, GlobalSectionsBijective,
  geometric/proper global sections, and the new declaration name. Upstream
  Scheme.GlobalSectionsBijective.of_geometricallyConnected has the scheme analogue
  only; its full signature and docstring were read. Proper.lean:150 and 161 likewise
  concern schemes and integral hypotheses. SpaceAffineGlobalSections defines a
  scalar-sections construction on a chosen small model, not the theorem here.
  No exact declaration and no collision with the proposed name was found.

Validation: scompile.py successfully compiled both the sandbox module and its final
library module path, with no errors or warnings. All universes and variables are
explicitly bound, and every line is at most 100 characters. The only initial error
was inference of the domain of Over.homMk; the final code spells out its full type.

## Second reading by NW

This is a separate rereading by the same worker, not a claimed independent review:
the dispatcher prohibits starting other agents and the maintainer reviews independently.
I reopened the accepted node and final Lean signature. Field, algebraic space and named
morphism agree; hp expands to exactly the three properness clauses. The repeated
pullback expressions have the identical Spec(algebraMap) map and typed Over objects.
The etale chart condition is reducedness, and ConnectedSpace supplies both of the
remaining geometric-fibre clauses. The conclusion uses sectionsMap of the recorded
structure map, so the map itself, rather than just the source/target cardinalities,
is fixed. Both identifications of sections in the preceding clause audit are canonical.
No hypothesis or conclusion clause is missing. During implementation I replaced the
equivalent Hom-from-O encoding with Mathlib sectionsMap to state Gamma(p-sharp) directly.
No new node, dependency repair, mathematical correction, or disputed statement remains.
