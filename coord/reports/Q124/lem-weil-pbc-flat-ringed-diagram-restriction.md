## Worker report

This packet states `CategoryTheory.FlatRingedDiagramInput.flatRingedDiagramRestriction`
in `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`, with proof `sorry`. It retains
the saved packet's coefficient-square and representative-normalization equations.
Three definition nodes own the input, comparison maps, and normalized adjunct
structures in separate modules. All definitions have explicit bodies; the only
postponed theorem is the owning item's statement. The item's mathematical statement,
proof and proof dependencies are unchanged. No statement correction or disputed
statement is asserted.

Hypothesis correspondence:

- The two small sites are `{C D : Type u} [SmallCategory C] [SmallCategory D]`
  with topologies `K,H`. The index is `(J : Type u) [SmallCategory J]`. The
  module, coefficient and small-site universe is the arbitrary `u` required by
  this node. Independent `w` and four `HasDerivedCategory.{w}` instances specify
  localization morphism sizes. No inhabitedness or boundedness is required.
- `FlatRingedDiagramInput.RV,SV,RU,SU` are the four commutative ring sheaves;
  `aV,aU` are the coefficient maps. `flatV,flatU` apply the recorded
  `SheafOfModules.IsFlatOnSite` to each target ring's unit module after actual
  restriction of scalars. They mean exactness of sheafified tensor, not flatness
  of every ring of sections.
- `FlatRingedModuleImage.morphism` uses the dependency's `RingedToposMorphism`.
  Its `inverse,direct,adj,leftExact` fields specify the geometric adjunction.
  The R and S presentations share it by `sameInverse,sameDirect,sameAdjunction`.
  Keeping equality between presentations does not require a functor presenting a
  morphism of the original sites.
- `FlatRingedModuleImage.inverse` is the existing
  `SheafOfModules.AlgebraicInverseImage`. Its `ringUnderlying` is the ring
  isomorphism `c_B`, with the ring and module graph equations from that recorded
  definition. `ringComparison` identifies it with the structural map governing
  the module direct image. The field `coherent` is exactly
  `a_U c_R = c_S u⁻¹(a_V)`. `eqToHom` aligns the two equal inverse-image functors.
- The module images are the recorded algebraic inverse image's `modules` and the
  ringed morphism's induced `modules`. Their chosen `adjunction` is normalized
  by `transpose`: after the given underlying-sheaf identifications, its Hom
  bijection is the original geometric sheaf adjunction. `additive` records the
  induced inverse image's additive action; it is not extra exactness.
- `diagramsRU,diagramsSU,diagramsRV,diagramsSV` are literally
  `J ⥤ ringedSiteModules ...`. `restrictU,restrictV` whisker Mathlib's actual
  `SheafOfModules.restrictScalars`. `inverseR,inverseS,directR,directS` whisker the
  specified module images. Their `...Complex` abbreviations are exactly
  `mapHomologicalComplex (.up ℤ)`. All diagram arrows are retained.
- `LR,LS` and `qLR,qLS` specify termwise localized inverse images. `FR,FS` and
  `ηR,ηS` specify total right derived direct images: `derivedR,derivedS` are
  Mathlib's universal `IsRightDerivedFunctor` properties for quasi-isomorphisms;
  `computesR,computesS` make the units invertible on every K-injective complex.
  The supplied `aR,aS` are derived adjunctions. Their `transposeR,transposeS`
  equations identify the adjunct of each localized complex map with its
  ordinary complex adjunct followed by the derived unit, exactly the stipulated
  0FND normalization. These bind the choices of derived operations in the node.

Conclusion correspondence:

- The four initial conjuncts are `PreservesFiniteLimits` and
  `PreservesFiniteColimits` for each actual restriction. Since these functors
  are additive between the abelian diagram categories, these say exactness.
- The following two conjuncts quantify over all cochain complexes of S-module
  diagrams at U and V and state that actual degreewise restriction preserves
  `CochainComplex.IsKInjective`. This is K-injectivity in the whole diagram
  category, not only in each evaluated module category.
- The final conjunct is `Nonempty (DerivedRestrictionComparison ...)`: existence
  of exactly the comparison maps and their normalization equations. Defining a
  type of this data does not assume an inhabitant or choose one from a sorry.
- `DerivedRestrictionComparison.maps.b0,d0` are the ordinary natural
  isomorphisms. Its `ordinary` field imposes
  `OrdinaryComparisonsNormalized` at every diagram index. On inverse images the
  underlying map is the composite of the specified underlying identifications;
  on direct images it commutes with those identifications. Thus both are the
  identities on the identified sheaves. `HEq` accommodates the two definitionally
  different scalar actions without omitting the specified map.
- `maps.rU,rV` are derived restrictions, and `maps.qU,qV` identify them with
  localization of the actual degreewise restrictions. `maps.b : LS ⋙ rU ≅ rV ⋙ LR`
  and `maps.d : FS ⋙ rV ≅ rU ⋙ FR` have exactly the two displayed directions.
- `inverseNormalized`, for every complex P, equates the path localizing
  `b0` with the path through `b` and the q factor isomorphisms. It is precisely
  the termwise inverse-image comparison, with no freely chosen normalization.
- `directNormalized`, for every complex I, equates
  `rV(ηS_I);d_QI;FR(qU_I)` with `qV_FS⁰I;Q(d0_I);ηR_rUI`.
  On a K-injective I the restriction-preservation conjunct and the two computes
  hypotheses make the units invertible. This gives exactly the underived
  identity computation prescribed for d at QI. Its natural equation for all
  complexes specifies the same universal derived comparison.
- `adjuncts` quantifies over all derived M,N and t. Its left side is
  `aR.homEquiv (rV.obj M) (rU.obj N) (b.inv.app M ≫ rU.map t)`;
  its right side is `rV.map (aS.homEquiv M N t) ≫ d.hom.app N`.
  Both sides go from `rV M` to `FR(rU N)`, so this is the node's exact adjunct
  identity. These are natural isomorphisms of full derived diagram functors.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, including the induced module action.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparent Mathlib `SheafOfModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of `siteSheafTensorRight`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the retained arbitrary-ring-sheaf
  `mathlib_match` of `def-pc-sheaf-restrict-scalars`. That node's current Lean
  record now selects the general Mathlib presentation;
  here its unchanged Mathlib match gives precisely the required general notion.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses` publicly exports the
  specialized `SheafOfModules.AlgebraicInverseImage` used in this node's common
  small universe. No private algebraic inverse-image structure is copied.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, null homotopy from every acyclic source.
- `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization`, imported for the proof plan.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`:
  `CategoryTheory.preDerivedAdjunctionGeneral`, imported for the normalized
  fraction proof plan. Its representing cocone, cone and splitting data are
  explained in the theorem docstring rather than omitted.
- The other recorded proof modules are imported without `public`: site tensor
  functoriality, module sheafification, preservation of K-injectives by exact
  adjoints, geometric module transport, termwise homotopy adjunction,
  ringed-site resolutions, K-injective total derived functors and exact-functor
  localizations. The geometric transport source was read with the required
  `scompile.py --source` fallback because the local snapshot lacks it.
  `lem-weil-pbc-scalar-extension-hom` and
  `lem-weil-pbc-kinjective-hom-derived` have no recorded statement module yet;
  their proof imports remain for the maintainer when they are stated.

The source text read was Stacks `sites-modules.tex`, 03D2--03D3 and 03ER(3),
and `derived.tex`, 0FND and 0DVC. The theorem docstring follows all ten proof
steps, grouping restriction exactness and K-injective preservation, ordinary
comparisons, derived comparisons, and the normalized adjunct calculation.

Edge cases: empty J gives terminal diagram categories and vacuous index
conditions; identity coefficient maps give identity restriction; an identity
geometric morphism uses the same specified normalization. Zero coefficient rings
and zero complexes need no nonzero assumptions. Complexes are unbounded and
integer-indexed. Flatness cannot be dropped: on a point, Z/p is K-injective as
a degree-zero Z/p-module but its restriction is not K-injective over Z.

Searches actually run (the wrapper records are in `searches.jsonl`):

- LeanSearch: `A geometric morphism with compatible flat coefficient ring
  isomorphisms induces normalized restriction comparisons on derived categories
  of module diagrams`. Eight hits, including `SheafOfModules.pushforwardNatIso`,
  `SheafOfModules.sheafificationCompPullback` and
  `RingCat.moduleCatRestrictScalarsPseudofunctor`. These are ordinary sheaf or
  single-ring operations, not this normalized geometric derived-diagram package.
- Loogle: `SheafOfModules.restrictScalars, CochainComplex.IsKInjective`:
  zero hits.
- Mathlib grep: `FlatRingedDiagram|DerivedRestrictionComparison|OrdinaryComparisonsNormalized`:
  zero hits. Direct `rg` with the same expression in upstream `WeilConjectures`,
  the side project's `lean/Sheaf`, DAG nodes and upstream names found only the
  unrelated completed pro-etale finite-coefficient comparison and open
  restriction comparison. Those fix particular pro-etale or open site maps;
  they do not define this arbitrary geometric coefficient-square interface.
- `blueprint_refs.py search 'flat coefficient restriction'`: zero blueprint nodes.
  The three delivered new node ids were also searched in the existing DAG, with no hits.
- The saved packet additionally records a LeanFinder query about flat restriction
  commuting with derived image and preserving K-injective diagram complexes
  (eight ordinary-operation hits), the same Loogle query, an injective restriction
  grep, and a LeanSearch query about respecting adjunction transposes. None is an
  exact match. The existing `CoefficientDerivedImage` package was inspected; the
  item uses its constituent Mathlib universal properties explicitly without
  redeclaring that package or importing its unrelated adic dependencies.

## New nodes

`def-weil-pbc-flat-ringed-diagram-input` owns
`Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs`: the compatible flat
coefficient square, normalized induced module images, termwise diagram functors
and ordinary identity predicate. It reuses the ringed-topos, algebraic inverse
image, scalar restriction and flatness definitions. It adds their joint input
and canonical functor abbreviations, not another version of any underlying notion.
The source is 03D3 and the coefficient specialization of the item's 0FND/0DVC
proof. The three recorded searches above found no exact package.

`def-weil-pbc-flat-ringed-diagram-comparisons` owns
`Sheaf.CategoryTheory.FlatRingedDiagramRestrictionComparisons`: ordinary b0,d0,
derived restrictions rU,rV with their localization factors, and the derived b,d
isomorphisms. This is a definition of data, with no existence proof or arbitrary
replacement for the canonical comparison. Its source is the coefficient-square
construction preceding the normalized 0FND calculation. The same actual searches
found no existing package.

`def-weil-pbc-flat-ringed-diagram-adjuncts` owns
`Sheaf.CategoryTheory.FlatRingedDiagramRestrictionComparisonAdjuncts`: the
`inverseNormalized`, `directNormalized`, and `adjunctNormalized` predicates and
`DerivedRestrictionComparison`, which bundles the ordinary identity predicate
with all three equations. The node states both complete normalization paths
explicitly; the inverse predicate takes both supplied localization factors
`qLR` and `qLS`. The source is 0FND/0DVC applied to the ordinary 03D3 adjunction.
The recorded searches found no existing definition. This structure's inhabitance
is asserted only by the owning item's sorry theorem. All three nodes are cited
by the item and carry its blueprint ancestor and full via path.

## Dependency modules

`def-pc-flat-sheaf-modules`: retained the saved sibling overlay
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`. Its original record documented
that compilation selected an older universe-specialized artifact. The module
preserves the published independent-site, coefficient and module universes and
body `exactFunctor _ _ (siteSheafTensorRight F)`. The dependency node changes only
`lean`, with the required explanatory note. The statement is unchanged; there is
no second tensor construction or different flatness notion. `autoImplicit false`
is explicit, and every variable and universe is bound.

## Second reading by Q124

Author self-check only; the maintainer performs the independent review. Reopened
the item, its current shared base, all five delivered modules, and their node
records. The item's statement, source, proof and proof dependencies are unchanged.
The dependency copy changes only `lean`; the item changes only `lean` and the
three added definition-node dependencies. Every recorded primary signature
matches its source verbatim. Each delivered helper is listed in its owning node.

Matched every hypothesis and clause against the correspondence above. In
particular, `coherent` has the stated ring-square orientation, the final adjunct
identity uses `b.inv`, and both full composition paths are retained in each
normalization predicate. The inverse predicate needs both `qLR` and `qLS`;
the saved invalid projection was repaired by an explicit `qLS` parameter from
the already supplied factor. The obsolete draft-normalization-node references
were replaced by the equations in the actual owning adjunct node. The proof
imports are restored, including the public upstream complex-adjunction module
used by the theorem signature. No hypothesis or conclusion was altered.

## Returned compilation repair

The saved packet was compared with the current shared node: only the item's
`lean` and the added definition-node dependencies differ; its mathematical
statement and proof are unchanged. The returned compile had timed out in
`FlatRingedDiagramRestrictionDefs`. The required first dry run of the saved
packet compiled that module in 23.3 seconds and the comparison-map module in
11.7 seconds, then diagnosed an invalid `maps.qLS` field in the adjunct module
and a line over 100 characters. The saved simplification had removed `qLS`
from the map structure but left this projection behind.

Repaired `inverseNormalized` to take the already supplied `qLS` explicitly,
and passed it from `DerivedRestrictionComparison`. This restores precisely
the existing inverse-localization equation, with no new mathematical hypothesis.
Shortened the reported line. The three normalization predicates are all listed
in the owning adjunct node's `lean.declarations`; that node now states their
equations directly rather than citing a removed draft normalization node.
Restored the saved proof-dependency imports and the public homological-complex
adjunction import required by the theorem signature. The report now describes
the three definition nodes actually present in the packet.

The author self-check reopened all five delivered modules and their node files.
The two ordinary underlying-identity equations, the two localization factors
in the inverse equation, the six maps in the direct equation, and the adjunct
formula all agree with the displayed mathematical clauses. All universes and
variables are explicit under `autoImplicit false`. No proof beyond the owning
item's `sorry` was introduced; all definition data remain explicit.

The next all-file compilation diagnosed a timeout in the adjunct module on both
local and server passes (the input and map modules compiled). The existing
termwise functor abbreviations had inferred, expanded types. Moved the existing
diagram-category abbreviations before those functors and gave all six ordinary
and all six complex functor abbreviations their explicit source and target
categories. Their bodies are unchanged. This keeps the same definitions while
avoiding repeated inference through sheaf-module and complex category instances.
A scratch profiler then compiled the complete adjunct module in 27.0 seconds;
its trace showed the repeated category-instance comparisons that the annotations
avoid. The scratch profiler and its diagnostic option are outside the delivered
modules. The four line-width warnings in that profiling snapshot were repaired
in the delivery before its final clean compilation.

The final clean all-file run compiled the four supporting modules without
warnings (input 23.4 seconds, maps 6.6 seconds, adjuncts 25.1 seconds), then
reported that the theorem's saved positional `J` argument was being supplied to
an implicit parameter. Replaced that call by `DerivedRestrictionComparison
(x := x) (J := J) ...` and synchronized the item's recorded signature. This
changes only argument syntax; it supplies exactly the same comparison data.
