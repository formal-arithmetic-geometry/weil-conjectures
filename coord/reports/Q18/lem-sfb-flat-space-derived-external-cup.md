## Worker report

The module `Sheaf.AlgebraicGeometry.FlatSpaceDerivedExternalCup` states
`AlgebraicGeometry.AlgebraicSpace.FlatExternalCup.flat_space_derived_external_cup`.
There is one postponed theorem, with all ten DAG proof steps in its docstring.
The law records remain in the theorem module. Canonical constructions and normalized
presentation witnesses live in `Sheaf.AlgebraicGeometry.FlatSpaceDerivedExternalCupMaps`,
owned by the new definition node `def-sfb-flat-space-derived-external-cup-maps`.
The item statement is unchanged. Four already landed statement dependencies and
this definition node record the interfaces actually used.

The result asserts the existence of normalized simultaneous section comparisons,
the algebra/external laws for every affine base, the scalar laws for every base
morphism, and the canonical comparison with the genuine Zariski ringed-site cup.
The witness data are fixed by section formulas, derived units, or K-flat
representative formulas. In particular, an arbitrary isomorphism between two
cohomology objects cannot satisfy the specification merely by being invertible.
No definition chooses data from this theorem or from an unnormalized existence
assertion. Only the theorem has `sorry`.

Hypotheses and objects, clause by clause:

* A commutative ring is `A : Type u` with `[CommRing A]`. The affine base is
  `Y : Over S` with `e : Y.left ≅ Spec (.of A)`; the ambient scheme `S` is arbitrary.
  Taking `S = Spec A` and `Y` its identity object recovers the original statement,
  including every ring map out of A. Arbitrary A, B, C and their maps share the
  universe containing the schemes. No separate smaller universe bounds test rings.
* Spaces are the dependency's actual `AlgebraicSpace S`. Flat qcqs structure maps
  are `admissible f`: exactly `MapIsFlat f`, `MapIsQuasiCompact f.hom.hom`, and
  `MapIsQuasiCompact (Limits.pullback.diagonal f.hom.hom)`. Flatness uses the
  existing chartwise property. Quasi-compact affine testing is identified with
  the source's arbitrary quasi-compact scheme testing by the existing
  `quasiCompact_iff_quasiCompact_scheme_tests`. There is no properness, finite
  presentation, Noetherianity, cohomology finiteness/projectivity, or coefficient
  flatness hypothesis.
* The fixed small etale module categories are `X.SmallModules`. Their actual
  structure objects are `X.derivedStructure`, and `sections` abbreviates
  `(affineDerivedSections A Y e X f).obj X.derivedStructure`, an object of
  `DerivedCategory (ModuleCat A)`. The displayed `HasDerivedCategory` instances
  are localization presentations at universe u, not geometric hypotheses.
* The product is any cartesian presentation with `IsPullback p.hom q.hom f.hom
  g.hom`; using the existing fibre product gives the named product in the node.
  `external` is literally `(rho_p ⊗ rho_q) ≫ mul`. `rho` is constructed from the
  existing ordinary regular-function structure map, its universal right-derived
  comparison, geometric direct-image composition, and identity coefficient
  restriction. No projection pullback is supplied as a free parameter.
* `AlgebraLaws.kunneth` says this exact `external` is an isomorphism.
* `mul` is exactly `affineDerivedCup` followed by the structure multiplication.
  `structureMul` is the unitor transported from the fixed coefficient unit.
  `unit` inserts `a ↦ a • id_O` using the actual ordinary scalar sections and
  universal derived unit. `AlgebraLaws.associative`, `.left_unit`, `.right_unit`,
  and `.commutative` render all commutative algebra axioms. `symmetry` uses the
  existing Koszul derived symmetry, rather than an unsigned exchange map.
* `AlgebraLaws.external_mul` renders preservation of the signed tensor-product
  algebra multiplication using `MonoidalCategory.tensorμ` for that same derived
  symmetry. `.external_unit` renders preservation of its tensor-product unit.
  Together with `.kunneth` this is an algebra isomorphism, not just an object
  isomorphism. No separately chosen algebra structure is introduced.
* For every T-morphism `h`, `.pull_mul` and `.pull_unit` preserve products and
  units; only its source and target structural maps must be admissible.
  `.pull_id` and `.pull_comp` give functorial pullbacks. In particular, h itself
  need not be flat, proper, or quasi-compact.
* `ExternalCoherence.naturality` is the complete two-factor pullback square,
  `.associativity` compares both parenthesizations of three cartesian factors,
  and `.permutation` gives the transposition with Koszul symmetry. Iterating
  transpositions and reassociation gives all permutations and parenthesizations.
  `.left_unit` and `.right_unit` give the unit factor T. The ring-unit comparison
  `AlgebraLaws.affine_unit` identifies K_T with the native tensor unit, identified
  with A[0] by `DerivedCategory.singleFunctorObjUnitIso` in the definition `unit`.
* `AlgebraLaws.first_projection` and `.second_projection` are the equations for
  `x ↦ x ⊗ 1` and `y ↦ 1 ⊗ y`, including the ordinary unit constraints.
* For any affine base morphism `g`, `spaceAffineRingMap e e' g` is the actual
  coefficient ring map. `baseChange` is the scalar-adjoint of the same geometric
  pullback, with the standard derived extension/restriction adjunction. Thus
  its domain is B tensor_A^L K, not a tensor chosen by the statement.
  `BaseChangeLaws.invertible` asserts invertibility for every cartesian scalar
  change of an admissible space. `.multiplication` and `.unit` preserve products
  and units. `ScalarTensor.tensor_representatives` and `.unit_representative`
  specify the scalar tensor comparisons by ordinary scalar extension on flat-term
  K-flat representatives and localization; they do not assume flatness of B.
* `BaseChangeNaturality.pullback` gives scalar-change compatibility for every
  morphism between the two cartesian squares. `.external` is its full external
  cup compatibility diagram. `BaseChangeComposition.identity` and `.composition`
  give the coefficient identity and tower comparisons. `restrictionComp`,
  `extensionComp`, `restrictionId`, `extensionId` are the canonical adjoint
  compositors, built from actual composition of regular-function ring maps.
* In the scheme case, `ZariskiComparison` uses actual
  `smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)`, its actual
  right-derived functor, the structure ring on `Z.left.Opens`, and the existing
  `RingedSiteCup.global`. Its scalar map is fixed on every open by restriction
  of `(g.left ≫ e.hom).appTop`. `ordinary_sections` fixes ordinary comparison by
  the restriction of `fullModuleSection`, and `on_complexes` fixes the derived
  comparison by the three universal derived units. `structure_sections` fixes
  O_Z → epsilon_*O_etale on every regular function; `structure_iso` asserts the
  quasi-coherent derived comparison for O. `ZariskiComparison.comparison` is
  derived sections followed by the inverse of this exact structure map.
  `ZariskiLaws.cup` identifies multiplication with the genuine Zariski cup after
  canonical restriction of scalars (`restrictionTensor`); `.invertible` asserts
  that the canonical cohomology comparison is an isomorphism. Bookkeeping
  additive fields supply the existing functors' additive structures as proofs;
  they supply neither a functor nor a map.

Dependency declarations used (all source signatures and docstrings read):

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its etale site, structure sheaf, and module category.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, localization and the single functor.
* `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineScalarSections`,
  `affineDerivedSections`, `affineDerivedCup` with the normalized scalar tensor.
* `Sheaf.CategoryTheory.RingedSiteModuleCupProduct`: `RingedSiteCup.relative`,
  `RingedSiteCup.global`, and its public global-derived-adjunction interface.
* `Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors`: `smallModuleUnitIso`,
  `fullModuleSection`, `affineSectionsComplexUnit`, and the recorded
  `affineDerivedSectionsComposition`/affine normalization.
* `Sheaf.AlgebraicGeometry.SpaceAffineHomComparison`: `spaceAffineSections`,
  `spaceAffineSectionAt`, `spaceAffineRingMap`, `spaceAffineDerivedSections`,
  `spaceDerivedSectionsComposition`, `spaceRightDerivedComplexUnit`, and
  `affineIdentityChart`. This is an added landed statement dependency.
* `Sheaf.AlgebraicGeometry.SpaceRelativeFlatClosedKernelBaseChange`:
  `relativeClosedKernelSmallStructureMap` and
  `relativeClosedKernelDirectImageComparison`. These helpers are general maps
  on all spaces over an arbitrary base; the theorem's closed-kernel assumptions
  do not occur in their signatures. Their data ownership is now recorded by the new existing:true definition node `def-sfb-space-small-structure-derived-comparison`, cited by the maps node.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally` and
  `MapIsFlat`, plus the existing quasi-compact map predicate. Added dependency.
* `Sheaf.AlgebraicGeometry.RingDerivedScalarExtension`:
  `moduleDerivedRestriction`, `moduleDerivedExtension`. Its public
  `ConstantRealizationDerivedScalarExtension` supplies the adjunction, actual
  representative comparison, and restriction composition. The latter three declarations are now owned by `def-sfb-module-derived-scalar-comparisons`, cited by the maps node.
* Existing public interfaces also supply `derivedDualityModel`, the actual
  `smallSchemeRestriction` and `schemeOpensRingHom`, the ringed tensor corner
  and model, and the representative-normalized `RingedSiteDualityModel`.
  Native derived-module tensor, its Koszul braiding, ordinary scalar-extension
  monoidal maps, and their complex maps are used from the explicitly imported
  Mathlib/WeilConjectures modules.

All recorded, available proof dependencies are imported without `public` unless
already statement imports. The three proof-only nodes without Lean records are
`lem-sfb-space-qcqs-derived-projection-formula`,
`lem-sfb-flat-space-derived-pushforward-base-change`, and
`lem-sfb-scheme-derived-etale-qcoh-comparison`. They are proof ingredients only;
no construction or statement binder waits for one of them. Their roles are
spelled out in the main proof docstring. The four additional landed statement
interfaces have been checked not to reach this item, so no dependency cycle is
introduced.

Edge cases checked before and during writing: the empty space (zero sections and
zero unital algebra), the zero ring (its empty affine spectrum), X or Y equal to
T (both unit constraints), identity and composite coefficient maps, nonflat scalar
change such as Z → F_2, arbitrary nonflat T-morphisms between admissible spaces,
and three factors with the middle Koszul interchange. The product and scalar
change are expressed by cartesian squares, so arbitrary choices of presentation
are retained. There are no cohomological boundedness assumptions. The scalar
extension normalization is restricted to K-flat representatives only for its
computation, not for the objects in the theorem.

Searches for an existing exact declaration:

* `msearch.py ... leanfinder "Derived external cup product R Gamma O of flat
  quasi compact quasi separated algebraic spaces and derived Kunneth base change"`:
  eight hits, all scheme fibre-product coordinate formulas, no derived theorem.
* `msearch.py ... loogle "DerivedCategory, CommMon_"`: zero hits (CommMon_ is not
  a recognized name in this index).
* `msearch.py ... grep "externalCup|external_cup|Kunneth" AlgebraicGeometry`:
  zero Mathlib hits.
* `msearch.py ... leansearch "Derived external cup product flat quasi compact
  quasi separated algebraic spaces"`: eight hits about quasi-separatedness,
  no external derived cup theorem. Exact search records are in searches.jsonl.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for external cup/Kunneth
  found narrower scheme cohomological cup and Picard constructions, not this
  flat qcqs algebraic-space theorem. Searching the item id in upstream returned
  no declaration. Further source searches located the existing scalar sections,
  regular-function structure maps, scalar adjunctions and ringed-site cup reused
  above. No private duplicate of those notions is introduced.
* DAG searches and `tools/blueprint_refs.py ancestor` found the accepted supporting
  node and its inherited ancestry (`None` for the computed unit ancestor); this
  is not the blueprint unit's own statement. The missing canonical-map interface is supplied by the new definition node
  described below. Source texts read: latest blueprint supporting path; Stacks
  spaces-perfect Tags 08IN, 08IR, 071Q; sites-cohomology 0FPL, 0FPM, 0FPN, 0H9A.

No STATEMENT-DISPUTED issue or statement correction is needed.

## New nodes

`def-sfb-flat-space-derived-external-cup-maps` defines the canonical scalar sections,
cup, unit, geometric pullback, external cup and scalar-adjoint base-change maps,
the adjoint coefficient compositors, the K-flat normalization of coefficient
tensor, and the actual Zariski comparison. It claims no Kunneth or algebra law.
Its source is the same tensor-of-counits construction in Stacks 0B6C/0FPJ,
the map underlying 08IN/08IR, and actual topology comparison in 071Q. Existing
nodes supply scalar global sections, direct-image composition, regular-function
structure maps and generic cup, but no node gives this assembled canonical
external map and its topology/scalar interfaces for algebraic spaces. The maps
module contains 26 declarations, no `sorry`; the theorem module contains the
seven law/theorem declarations. Splitting these reusable maps from the laws
keeps each compilation within the required per-file limit, without altering a
statement or increasing that limit. scompile.py checked each separately in
dependency order: maps about 54 seconds, theorem about 12 seconds, clean.

For this node, fresh LeanFinder search for canonical external cup on scalar
derived structure-sheaf sections returned eight Spec/regular-function hits;
LeanSearch for canonical derived external cup returned eight exterior-power
hits; Loogle `DerivedCategory, TensorProduct` returned zero. Mathlib grep
returned no match; `rg` in upstream and Sheaf found the existing graded
scheme/Picard constructions, which have different objects and conclusions.
`blueprint_refs.py search 'derived external cup'` found zero blueprint nodes.
DAG grep found the original theorem and narrower scheme/Picard/coherent-group
citers, not a definition of this interface. Actual returned search logs and
source/DAG matches are recorded in the new node's `mathlib_searches`.

The additional existing interfaces used by this definition are
`AlgebraicSpaceDerivedModules` (`derivedStructure`, `smallSchemeRestriction`),
`RingedSiteDualityMaps` (`RingedSiteDualityModel`),
`RingedTensorSquarePresentation` (`RingedTensorCorner`, `RingedTensorModel`),
`RingedSiteGlobalDerivedAdjunction` (`globalSections`, `derivedGlobalSections`),
`ConstantRealizationDerivedScalarExtension` (coefficient adjunction and
representative formulas), and `AlgebraicSpaceSchemeRestriction`
(`schemeRestriction`, `schemeOpensRingHom`). They are direct public imports of
the maps module and recorded statement dependencies of the new node. Its
statement cites every recorded dependency. The new node has no dependency
on the consuming theorem, and no known return path was found through its
existing foundational interfaces. Final DAG validation belongs to the server
preflight; the older local DAG has unrelated missing references and cycles.

`def-sfb-module-derived-scalar-comparisons` is an existing:true definition node
on `CategoryTheory.ConstantScalarRealization.moduleDerivedAdjunction`,
`moduleRepresentative`, and `moduleDerivedRestrictionComposition` in
`Sheaf.Paper.ConstantRealizationDerivedScalarExtension`. Its three clauses are
respectively the adjunction selected from exact derived restriction, the mate
of the localized ordinary scalar-extension unit on every complex, and the
localized ordinary restriction compositor. It retains independent localization
universes and requires no K-flatness for the map. Sources: Stacks 06YY, 07A6,
0D6D. LeanSearch and Loogle found ordinary scalar adjunctions; Mathlib grep found
no named helper; upstream grep found none; Sheaf grep found these exact existing
definitions; DAG grep found only the theorem record as owner. Blueprint searches
found no separate node. Thus the new node adds DAG ownership and reuses the
existing declarations, with no new module or definition.

`def-sfb-space-small-structure-derived-comparison` is an existing:true definition
node on `AlgebraicGeometry.AlgebraicSpace.relativeClosedKernelSmallStructureMap`
and `relativeClosedKernelDirectImageComparison` in
`Sheaf.AlgebraicGeometry.SpaceRelativeFlatClosedKernelBaseChange`. Its first
clause is the regular-function structure map conjugated by `smallModuleUnitIso`
and `fullModuleSection`; its second is the ordinary degree-zero image mapped
into the derived image through `spaceRightDerivedComplexUnit` and the single
complex identifications. The only objects required are a scheme, two spaces,
a morphism and a module, with a common arbitrary localization universe for the
second map. It asserts no invertibility and adds no closed/flat/qc hypotheses.
Sources: Stacks 03G8 and 079V. The same recorded LeanSearch, Loogle and Mathlib
grep searches found general ordinary infrastructure; upstream grep found none;
Sheaf grep found these two existing definitions; DAG grep found only their
closed-kernel theorem owner. Exact-name blueprint search found no node. This
record also reuses existing declarations and supplies no module.

## Second reading by Q18

The dispatcher explicitly prohibited starting another agent. This section records
a second pass by the same worker, not an independent review; the delivery receives
the maintainer's independent review as specified in the assignment. I checked both
nodes against their files again, concentrating on canonical-map normalization, the
absence of a B-flatness assumption, the signed tensor multiplication, all
identity/composition comparisons, and the actual Zariski cup. The first and second
projection clauses were restricted to cartesian products, matching the node's
scope. Unspecified comparison isomorphisms were replaced by section and
right-derived-unit normalizations; scalar tensor data were fixed on flat K-flat
representatives. The only postponed theorem is the item itself.


Dry-run repairs: the maps node's signature extraction originally stopped at the
named argument `(S := S)`; the record now contains the complete signature up to
the declaration body. The main item's added closed-kernel theorem dependency
was removed. The maps definition instead cites `def-sfb-space-module-structure-map`
for the regular-function structure morphism, and reuses the already published
small-model/derived insertion helpers without asserting that theorem. The returned H2 repair below supplies the missing definition-node ownership for those helpers. Comma-grouped
node citations were expanded to separate brackets to match the preflight parser.
The route-pivot advisory on `RingedSiteDualityMaps` concerns a bidual-transpose
node in that same module: this delivery uses only the normalized tensor/unit model,
not that dropped bidual assertion.

Final canonical-map check: `ScalarTensor.naturality` is included explicitly.
The K-flat representative formula fixes the tensor comparison on a resolving
subcategory; naturality transports it to all derived objects, including objects
that are merely isomorphic to a displayed localized K-flat complex. Thus the
comparison is not an unconstrained objectwise family away from representatives.


## Repair of return 68cd0e32ff83

1. Replaced `lem-sfb-ringed-site-duality-maps` in the maps definition's
   `stmt_deps` and statement citation by `def-zl-ringed-site-duality-model`.
   Read that node and the existing RingedSiteDualityModel/unit definitions;
   these are precisely the normalized tensor and unit data used here.
2. Added the existing:true definition node
   `def-sfb-module-derived-scalar-comparisons` for the three requested scalar
   declarations, and replaced the constant-realization theorem dependency and
   its statement citation by this definition node.
3. Added the existing:true definition node
   `def-sfb-space-small-structure-derived-comparison` for the two requested
   structure/insertion maps, and cited it from the maps node's statement and
   `stmt_deps`. This repairs the previously unrecorded use by `pull`.

All three numbered H2 points are repaired. The maps statement changes only the
ownership references and spells out the already-used small-model insertion;
its mathematical data and the item's statement are unchanged. No statement
correction is needed. Both Lean files are unchanged from the accepted head.
The optional recommendation to generalize localization universes is deferred;
the accepted universe-u presentation remains in the item, while both new helper
records preserve the full general universes of the existing declarations.
The current read clone's owning records and full helper signatures were checked
again. The wrapper performs the authorized refresh/rebase and server checks.

Second reading of this repair: the new scalar record describes the actual
adjunction, mate and localized restriction composition, including the arbitrary
complex case. The new geometric record describes both actual composites in
source, including the inverse final single-complex identification. Every
bracketed dependency has a matching `stmt_deps` entry. No theorem assertion is
being used in place of either helper definition, and no helper is copied.
