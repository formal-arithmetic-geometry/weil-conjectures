## Worker report

The module `Sheaf.AlgebraicGeometry.StackCoheratorFlatTestRestriction` states
`CategoryTheory.moduliLqcCoherator_counit_flatTest_isIso`, with its whole proof `sorry`.
It introduces no definitions and makes no correction to the mathematical statement.

Hypothesis and conclusion matching:

- The size convention is rendered by explicit independent `universe u v w`,
  `Scheme.{u}` and `BasedCategory.{v, w}`. Module and structure-ring universes are the
  recorded common ambient universe `max (u + 1) v w`; neither site universe is
  identified with another.
- The base scheme S is `{S : Scheme.{u}}`. The stack Z/S is
  `F : BasedCategory.{v, w} (Over S)` with `hF : IsAlgebraicModuliStack F`.
- The big fppf ringed site is the recorded `moduliModuleRings F hF.1.1`.
  Its module category is Mathlib's `SheafOfModules`, as exposed by
  `ringedSiteModules`, not a copied category.
- H is an object of `(locallyQuasicoherentFlatCompatible F hF.1.1).FullSubcategory`.
  Its property is exactly the conjunction of local quasi-coherence on every small
  etale test and invertibility of the canonical tensor comparison on flat arrows.
- The inclusion and coherator are `ObjectProperty.ιOfLE h` and Q, with
  `adj : ObjectProperty.ιOfLE h ⊣ Q`. These are exactly the witnesses whose existence
  `exists_moduliLqcCoherator` states. They are parameters because the dependency
  existentially supplies them rather than choosing a functor. No arbitrary map is
  supplied: the map in both conclusions is `(adj.counit.app H).hom`. The property is
  invariant under the unique compatible isomorphism between right adjoints, so it
  applies to every witness of the recorded existence theorem. The redundant Hom
  formula and invertibility of the unit are not extra hypotheses.
- A scheme test is `T : Over S` and
  `z : BasedFunctor (discreteModuli (yoneda.obj T)) F`. Its object is
  `z.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T)))`, evaluation of the representable
  scheme category at its identity. The based-functor projection equation identifies
  its underlying scheme with T.left. This is the usual equivalence of scheme tests
  with objects of the fibred groupoid, with no selected cartesian section.
- Flatness is `hz : ModuliSpaceTest @Flat z`: every etale scheme chart of every
  actual algebraic-space base change has flat projection. This existing predicate
  contains no properness or DM hypothesis despite its owning module's title. The
  item's stmt_deps gains its already landed owning node
  `def-sfb-dm-stack-morphism-properties`; no other base field changes.
- The first conjunct is `IsIso` of the image of the actual counit under
  `moduliEtaleRestriction F hF.1.1` at this object. This is an isomorphism of the
  recorded small-etale module sheaves, with canonical regular-function coordinates.
- The second conjunct is `IsIso` of its image under
  `SheafOfModules.evaluation (moduliModuleRings F hF.1.1) (op ...)`: exactly the
  linear map q_H(z) on the original test's sections, not only the value at a
  selected cartesian lift. Evaluation at the final etale test identifies it via
  the slice-equivalence counit and naturality.
- There are no quasi-compactness, quasi-separatedness, finite-presentation,
  Noetherian, nonemptiness, or surjectivity hypotheses on F, z, or H.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack` (including its fibred-groupoid proof).
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `CategoryTheory.moduliModuleRings`, `moduliSchemeForget`, and the inherited fppf site.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.StackLqcCoherator`:
  `locallyQuasicoherentFlatCompatible`, its two defining predicates,
  `moduliEtaleRestriction`, `moduliEtaleLift`, `moduliTestSlice`,
  `moduliEtaleLiftSchemeIso`, `exists_moduliLqcCoherator`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, equivalent
  to flat stalk homomorphisms by `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliSpaceTest`, the existing source-local chartwise predicate.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules.evaluation`.
  `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: the inclusion and
  underlying morphism of a full subcategory.

Public imports expose statement dependencies; proof-only imports cover the recorded
stack chartwise calculus, space module operations, algebraic spaces, scheme-test
quasi-coherent restriction and space fppf covering calculus. The proof dependencies
`lem-sfb-space-fppf-qcoh-descent`, `lem-sfb-smooth-atlas-module-descent`, and
`lem-sfb-smooth-atlas-quasicoherent-source-maps` have no recorded modules on the
read base, so no import can yet be supplied for them. They are named in the complete
seven-step proof docstring, in exactly the roles of the node's proof. No statement
construction depends on a missing declaration.

Edge cases checked before writing: the empty scheme test is allowed (flatness is
vacuous and the restricted module category has only zero sections); the zero module
is allowed; identity scheme tests when the stack is a scheme are flat; arbitrary
nonflat scheme tests are correctly excluded by hz; flat tests need not be surjective,
quasi-compact or locally finitely presented. Independent stack-object and
stack-morphism universes are retained, including stacks with large automorphism
categories relative to the base scheme universe. An arbitrary right-adjoint witness
has the same counit assertion by uniqueness of universal arrows.

Searches made using the prescribed msearch.py wrapper:

- LeanFinder: "The quasi coherator counit of a locally quasi coherent flat compatible
  module on an algebraic stack restricts to an isomorphism on flat scheme tests".
  Eight results, concerning scheme restriction adjunctions, flatness criteria, or
  condensed modules. None states this stack result.
- LeanSearch: "quasi coherator counit algebraic stack flat test restriction
  isomorphism". Eight results, concerning scheme restriction, general category
  adjunctions or sheaf comparisons. No matching declaration.
- Loogle: "CategoryTheory.Adjunction.counit, SheafOfModules.toPresheaf,
  CategoryTheory.IsIso". No hits; the middle identifier was unknown to the service.
  The actual evaluation API was read directly from Mathlib's Sheaf.lean.
- Mathlib grep: `coherator|Coherator|flat.test`, subdirectory AlgebraicGeometry.
  No hits.
- Project rg: `coherator|Coherator|Moduli.*Flat|Moduli.*Test|Flat.*Moduli` in
  lean/WeilConjectures and the chartwise calculus module. Scheme derived coherator
  results are different statements; the chartwise ModuliSpaceTest is reused.
- Project rg: `coherator|Coherator` in lean/Sheaf. It finds the defining
  StackLqcCoherator interface and derived scheme/space results, no flat-test counit
  theorem. Direct grep of the item id in lean/WeilConjectures found no declaration.
- The proposed full declaration name was checked in both project roots and
  dag/lean_names_upstream.json: no existing declaration.

Source read: local literature/stacks-project/stacks-cohomology.tex, lemma-adjoint
(Tag 0778), lemma-flat-object-and-Q (Tag 0GQK), and the item's full expanded proof.
The deprecated example Sheaf/CategoryTheory/CompactObject.lean is withdrawn; its
node points to WeilConjectures/CategoryTheory/CompactObject.lean, which was also read
for the current module header and declaration conventions.

No STATEMENT-DISPUTED issue, new node, dependency repair, or statement correction.

## Second reading by Q16

This is a second pass by the single dispatched worker; the independent review is
performed by the maintainer as specified in the dispatch brief. No second agent was
started. With the node and module open, I checked the base S, independent universes,
algebraic-stack predicate, the exact L_Z full subcategory, and the chosen coherator
adjunction against the dependency signature. The flatness condition is the actual
scheme-chart condition, not flatness of T over S and not flat compatibility of H.
The two IsIso conjuncts respectively state the small-etale restriction and the
original section map, both of the same adjunction counit. The object used for the
scheme test is evaluation at its identity, canonically over T by z.w_obj. The full
subcategory `.hom` forgets only the object predicate and retains the module map.
There is no claim that the algebraic-space fibre product is a scheme. All seven
proof steps are present, including the universal-arrow identification needed to
ensure that the counit under discussion is the actual counit of adj.

The compile caught the explicit ring argument required by
SheafOfModules.evaluation; this was supplied without changing the statement's
mathematical content. No mismatch with any hypothesis or clause remains.
