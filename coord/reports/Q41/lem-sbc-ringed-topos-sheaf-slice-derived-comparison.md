## Worker report

Item: `lem-sbc-ringed-topos-sheaf-slice-derived-comparison`.
Module: `Sheaf.Paper.SheafSliceDerivedComparison`.
Main declaration: `CategoryTheory.ringedSheafSliceDerivedComparison`.

The theorem returns the ordinary ringed slice square and its unbounded derived comparison
as `∃ o : RingedSheafSliceOrdinaryComparison RX RY f A,
HasRingedSheafSliceDerivedComparison o`. The ordinary record and the derived existential proposition bundle
the conclusions; none of their conclusions are hypotheses supplied by the caller.
Labels such as `theta_representative` below refer to the corresponding commented
conjuncts in the derived proposition, rather than structure projections. There is one
postponed proof, the main theorem, whose docstring gives all nine steps of the DAG proof.
The identity comparison `sheafSliceUnderlyingRestriction` has actual data `Iso.refl _`.
No object is chosen from the existence theorem and no definition contains `sorry`.

Hypotheses and clauses, matched to the declaration:

| Node text | Lean rendering |
| --- | --- |
| Sites small in the chosen universe | Explicit `universe u w`, `C D : Type u`, `[SmallCategory C]`, `[SmallCategory D]`, topologies `J`, `K`. This is the recorded size convention after taking small presentations. |
| Commutative coefficient rings | `RX : Sheaf J CommRingCat.{u}`, `RY : Sheaf K CommRingCat.{u}`. Only the existing `localCoefficientRings` forgets commutativity when passing to module categories. |
| Arbitrary ringed geometric morphism and structural map | `f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY)`. This is the recorded geometric adjunction, finite-limit preservation, structural ring map and its induced module direct image. No functor between `C` and `D` occurs. |
| Any target sheaf, inverse-image source sheaf | `A : Sheaf K (Type u)` and the term `f.inverse.obj A` throughout. There is no representability assumption. |
| Small element sites and restricted rings | `sourceSlice`, `targetSlice` use `RingedSheafSliceAdjunctionData`; coefficients are the existing `elementRing` and its commutative version `presentationElementRing`. |
| Exact ordinary restrictions | The existing `elementModulePullback.{u,u}` on both sides; `targetRestrictionAdditive`, `sourceRestrictionAdditive`, and the four finite-limit/finite-colimit fields assert exactness in the conclusion. |
| Canonical ringed slice morphism | `slice` is a `RingedToposMorphism` between these element sites. `sliceInverse` identifies its inverse image with the arrowwise `Over.post f.inverse` through the fibre equivalences. |
| Canonical commutative ringed square | `starComparison_formula` fixes the underlying product comparison to `prodComparison f.inverse A F`. `SheafSliceSetLocalization.sections` fixes localization on fibre sections to the second projection. `sets_formula` spells out their composite, and `structural` says precisely that the slice structural map is the restricted original structural map after this comparison. These conditions exclude an arbitrary unrelated square. |
| Ordinary module pullback | `pullback`, `ordinaryAdjunction` and their slice versions specify left adjoints to the supplied induced direct images `f.modules`, `slice.modules`. This is the universal-property specification of module pullback; together with its adjunction it is unique up to the unique adjunction-preserving isomorphism. No exactness of module pullback is asserted or assumed. |
| Ordinary sigma | `sigma : rY ⋙ slicePullback ≅ pullback ⋙ rX`. `ordinary_mate` specifies its mate to be `delta.hom`. |
| Ordinary restriction/direct-image identity | `delta : f.modules ⋙ rY ≅ rX ⋙ slice.modules`; `delta_underlying` identifies its underlying sheaf map with the geometric adjunction mate of the canonical set-sheaf square, using the given underlying identifications in the two ringed morphisms. Thus it is the ordinary identity, rather than an arbitrary natural isomorphism. |
| Ordinary unbounded derived categories | The existing `DerivedCategory` of the existing module categories. Four explicit `[HasDerivedCategory.{w} ...]` binders select the localization universe; standard large localization supplies a possible choice. No boundedness predicate occurs. |
| Canonical K-flat pullback / K-injective direct image adjunctions | `globalDerived` and `sliceDerived` reuse `RingedCoefficientCounit.DerivedAdjunction`. Its fields give the two derived universal properties, comparison maps `epsilon`, `eta`, K-injective computation, and `homFormula` normalizing the adjunction by the ordinary transpose. `globalFlat_computation` and `sliceFlat_computation` assert the specified K-flat computations. |
| Exact restriction on derived categories | The actual Mathlib functors `rX.mapDerivedCategory.{w,w}` and `rY.mapDerivedCategory.{w,w}`. Their actual `mapDerivedCategoryFactors` occur in both representative equations. No second derived restriction is invented. |
| Natural isomorphism theta for every M | `theta` is a natural isomorphism `rY_D ⋙ sliceDerived.left ≅ globalDerived.left ⋙ rX_D`. |
| Theta on flat-term K-flat representatives | `theta_representative` equates theta followed by the global pullback and restriction representative identifications with the slice pullback and restriction identifications followed by `DerivedCategory.Q.map` of the termwise sigma. `IsKFlatIndependentCoefficients` and `IsFlatOnSite` are the recorded predicates, with explicit coefficient arguments. |
| Restriction of T stays K-flat with flat terms | `targetKFlat` asserts both parts, for every `T` satisfying the two recorded predicates. |
| Natural isomorphism beta for every E | `beta` is a natural isomorphism `globalDerived.right ⋙ rY_D ≅ rX_D ⋙ sliceDerived.right`. |
| Beta on K-injective representatives | `beta_representative` is the equality between the two composites formed from the actual restriction factorizations, the two `eta` maps, and `Q` of termwise delta. `sourceKInjective` asserts that the restricted representative is K-injective. Hence every arrow used as a representative identification is invertible in the stated case. |
| Beta is theta's adjunction exchange mate | `derived_mate` uses Mathlib `mateEquiv` for the two representative-normalized derived adjunctions. |
| Counit equation | `counit` reads `theta_(Rf E) ≫ rX_D.map(epsilon_E) = LfA.map(beta_E) ≫ epsilonA_(rX_D E)`. Lean composition is left-to-right, so this is exactly the displayed equation in the node. |
| No structural-map flatness, invertibility, boundedness or site presentation | No such hypotheses occur in the theorem or the output structures' parameters. |

The auxiliary universal-property presentations are coordinates for canonical objects,
not extra mathematical assumptions. In particular changing a chosen module left adjoint
transports the whole output by its unique adjunction-preserving isomorphism. The ordinary
geometric comparison, ordinary mate, normalized derived Hom formulas and representative
equations retain the canonical arrows and their counits.

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction` (publicly re-exporting its construction
  module): `RingedSheafSliceAdjunctionData`, `elementRing`, `elementTopology`,
  `elementObj`, `elementSheafPullback`, `elementModulePullback`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent Mathlib `SheafOfModules` specialization.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.star`, `Over.post`.
- `Sheaf.CategoryTheory.RingedPresentationData`:
  `CategoryTheory.presentationElementRing`, owned by the landed definition node
  `def-weil-pbc-ringed-presentation-comparison-data`, added to `stmt_deps`.
- `Sheaf.CategoryTheory.LocalCoefficientLocalization`:
  `CategoryTheory.localCoefficientRings`, owned by the landed definition node
  `def-weil-pbc-local-coefficient-localization`, added to `stmt_deps`. Its module is
  publicly imported by `RingedPresentationData`. The transport theorem
  `CategoryTheory.ringed_presentation_transport` is not used; its theorem node is
  removed from the delivery's added statement dependencies.
- `Sheaf.CategoryTheory.RingedCoefficientCounitPresentations`:
  `RingedCoefficientCounit.modules`, `underlying`, `onComplex`, `DerivedAdjunction`.
  The already landed definition node `def-pur-ringed-coefficient-counit-presentations`
  is added to `stmt_deps` to reuse this generic normalized derived-adjunction interface.
- Every stated proof dependency's recorded module is imported, including
  `Sheaf.Paper.ProjectionMateExact`, `ModulePullbackTensorIso`,
  `ModulePullbackPushforwardAdjunction`, `GeometricModuleTransport`,
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`,
  `KFlatRingedToposPullback`, `RingedSiteKInjectiveResolutionsOfUniverses`,
  `RingedTopoiDerivedPullback`, `Sheaf.SixFunctors.ResolvingDerivedAdjunction`,
  `KFlatResolutionIndependentCoefficients`, `SiteDerivedTensorDescentIndependentCoefficients`,
  and the Mathlib over-slice and K-injective Hom modules. Proof-only imports are not public.

Edge cases checked before drafting:

- `A` terminal: the slice square reduces, through its presentation equivalences, to
  the original morphism. The representative formulas and mate equation become identities.
- `A` initial/empty: the element site and all module categories on the slice are zero;
  the same formulas make sense, with no nonempty or nonzero-ring hypothesis.
- Empty site or empty covering sieve: the existing sheaf/fibre constructions and products
  still apply; no pointwise global-section inference is used.
- Nonflat structural map over a point, for example `ℤ → ℤ/2`: pullback is not assumed exact;
  its derived functor is computed only on K-flat representatives as required.
- Representable `A` agrees with the site-object special case, but the theorem does not
  assume subcanonicity or representability.
- Complexes unbounded in both directions are allowed: all shapes are `.up ℤ` and all
  derived localizations are ordinary unbounded localizations.

Searches actually run through the prescribed `msearch.py` wrapper:

1. LeanFinder: `Restriction to an arbitrary sheaf slice commutes with unbounded derived
   pullback and direct image for a morphism of ringed topoi`. Eight hits: underived
   `SheafOfModules.pullbackComp`, `pullbackPushforwardAdjunction`, their unit/generator
   identities, `pullbackIso`; no arbitrary-sheaf unbounded comparison theorem.
2. Loogle: `"SheafOfModules", "pullback"`. Twelve hits, principally presheaf pullback
   and underived site-functor adjunctions; no exact match.
3. Mathlib grep in `CategoryTheory`: `slice.*derived|derived.*slice|overFunctor.*KInjective`.
   Zero hits.
4. LeanSearch: `Unbounded derived pullback and direct image commute with restriction to
   a slice over any sheaf of sets for a morphism of ringed topoi`. Eight hits: ordinary
   module pullback/adjunction, site-object `overPullback`/`overMapPullback`, scheme
   pullback and its restriction isomorphism; no exact match.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for sheaf-slice/ringed-slice names
   found the element-site and presentation interfaces reused above, and site-object
   derived comparison modules. They assume a continuous site functor and a site object,
   unlike this statement. Grep of the item's id in `lean/WeilConjectures` returned no hit.
   Exact searches for the new declaration names in Mathlib, upstream and `Sheaf`
   returned no hit. The only project mention of this item is a proof-plan citation in
   `RingedSitePerfectProjectionFormula`, not an existing declaration.

No statement correction, dependency-module repair, new independent notion, or
`STATEMENT-DISPUTED` issue was needed. The three added existing definition dependencies have been
checked transitively not to depend on this item, so they do not create a dependency cycle.

## Second reading by Q41

Sequential second reading by the same worker; the dispatcher explicitly forbids starting
another agent, and the maintainer supplies the independent review after delivery. This
paragraph does not claim an independent reader.

I reopened the node's full statement and the declaration, and compared every row above.
The ringed morphism is arbitrary; A is a sheaf, not a site object; the slice inverse image
is `Over.post` and its ring map is the restricted original map. The ordinary direct-image
comparison is tied to the geometric mate on underlying sheaves, and sigma is its inverse
mate. The derived Hom normalization is reused, not replaced by a bare adjunction.
The theta and beta formulas include the actual exact-restriction factorizations and the
correct directions of epsilon and eta. The source K-injective preservation and target
flat-term K-flat preservation clauses are present. Finally the counit equation has the
node's orientation after translating Lean's left-to-right composition.

During drafting I removed the unnecessary symmetric source-K-flat and target-K-injective
clauses, which the item does not ask for. Compiler diagnostics also required explicit
module universes in element restriction and explicit coefficient arguments in flatness,
without changing the categories or adding a universe equality. The slice derived-category
binders use the same raw `elementRing` carrier as the actual restriction functor, avoiding
instance search through the commutative-forgetful presentation.

Compilation: the final ordinary record and derived existential proposition typechecked
without errors or warnings in both sandbox and library modes (13.7 seconds and 12.0
seconds before the final documentation/name update). The derived proposition uses the
ordinary record's exactness witnesses directly with `letI`, so there are no extra
hypotheses or duplicate exactness data. Using an existential proposition avoids generating
unneeded eliminators for the large derived data. All definitions have actual data; the
only postponed proof is the main theorem. Final delivery checks are recorded below.

Final validation: `deliver2.py Q41 lem-sbc-ringed-topos-sheaf-slice-derived-comparison --no-push`
returned `OK (dry run)` on 2026-10-21: the final module compiles and the maintainer
preflight passes. Only the item's `lean` and the three added existing definition `stmt_deps` differ
from the original node; there are no new nodes or dependency repairs.

## Repair of return L (H2), 2026-10-21

The return reviewed immutable head `b223c3c7dc81` and requested a dependency-owner
correction only. The saved packet's initial dry run passed as commit `8ae90b05250`,
but its added theorem dependency still had the reported mismatch. I replaced
`lem-weil-pbc-ringed-presentation-transport` with the actual definition owner
`def-weil-pbc-ringed-presentation-comparison-data` for `presentationElementRing`,
and added `def-weil-pbc-local-coefficient-localization` for `localCoefficientRings`.
I read both owning node records and both declarations in their source modules;
the former transport theorem record lists only `ringed_presentation_transport`.
The existing normalized-derived-adjunction dependency remains. The report's
dependency list and the item's `lean.note` now name these three definition owners.

The sandbox was compared with the current read-only main node: only `lean` and
`stmt_deps` differ. All original main statement dependencies are retained in order;
the three additions name already landed definition nodes. The Lean source is
unchanged by this repair, preserving the mathematics approved clause by clause in
the return. No mathematical statement, proof plan, dependency module or new node
is changed or added by this repair. The repaired packet passed `scompile.py` in sandbox mode (10.9 seconds) and
library mode (11.5 seconds), with no diagnostics. The field/signature check and
transitive dependency-cycle check passed for all three added definition nodes.
