## Worker report

The delivery states lem-cbc-ringed-open-scalar-adjunction in
`Sheaf.CategoryTheory.RingedOpenScalarAdjunction`, namespace
`SheafOfModules.RingedOpenScalar`. The original node text and dependency lists are
unchanged. There are no new nodes or dependency repairs. All five postponed theorems
belong to clauses of this node: `scalarExact`, `sliceExact`, `adjunctionGenerators`,
`tupleAction`, and `comparison`. Each has only `sorry` as proof and a source/proof
docstring. Definitions contain actual constructions. The remaining declarations are
transparent presentations, the canonical sectionwise restriction comparison, and
explicit standard instances used to form the transported statement.

Sources read: sites-modules.tex, lemma-extension-by-zero (03DI),
lemma-sheafification-presheaf-modules (03CY), and lemma-extension-by-zero-exact (03DJ).
The scalar compatibility is the generator calculation in the node's seven proof steps;
the cochain/tower extension is its termwise argument and the localization property.
The example CompactObject.lean is now withdrawn in the read clone; the delivery uses
the current required module/public-import/exposed-section format.

Hypotheses and clauses, individually:

* A site small in the module universe: `{C : Type c} [Category.{v} C]`,
  `J : GrothendieckTopology C`, module/coefficient universe `max c v r`.
  The object and morphism universes stay independent. `HasSheafify` and
  `WEqualsLocallyBijective` are the standard sheafification infrastructure on this
  small site. The explicit slice infrastructure is constructed in `sliceSheafify`
  and `sliceLocallyBijective`, rather than assumed as an additional restriction.
* An object and a commutative-ring-sheaf map: `U : C`,
  `{R S : Sheaf J CommRingCat.{max c v r}}`, `a : R ⟶ S`.
  `rings` forgets only commutativity via Mathlib's sheafCompose.
* The localized topology and rings: Mathlib `J.over U`, `Sheaf.over`, and the
  recorded `localizedSystemRestriction`, definitionally `overFunctor`.
  Their objects are precisely the section modules over `(V, phi)`.
* Scalar restrictions r and r_U: `scalars a` and `sliceScalars U a` are the recorded
  Mathlib `SheafOfModules.restrictScalars`, with the restricted ring map obtained
  using `J.overPullback`. No new module category or scalar restriction is defined.
* J_R and J_S are the recorded `localizedSystemExtension R U` and its S version:
  the actual `extensionByZeroPresheaf` followed by
  `PresheafOfModules.sheafification (𝟙 _)`. `generator` is the actual sheafification
  adjunction unit applied to `DirectSum.of ... phi x`.
* The specified adjunctions are `localizedSystemAdjunction R U` and its S version,
  selected by the unique summand-unit normalization of the recorded dependency.
  They are never replaced by arbitrary adjunction witnesses.
* Identity before sheafification, including reindexing/naturality: `comparison`
  first supplies a natural isomorphism p of the two presheaf-valued functors and
  asserts `(p.hom.app N).app V x = x` for every tuple x, not just generators.
  Because this is a natural transformation of presheaf-module functors, it
  respects restriction maps, scalar actions and arrows N → N'.
* Scalar-action clause: `tupleAction` identifies the R-action on the second
  direct sum with `(a.hom.app V b) • x` on the first, for every tuple x and b.
  The explicit `@SMul.smul` selects the restricted action on the same underlying
  group, avoiding Lean elaborating the S-module action instead.
* The sheaf comparison e: the second existential of `comparison` is
  `localizedSystemExtension S U ⋙ scalars a ≅
   sliceScalars U a ⋙ localizedSystemExtension R U`.
  Its normalization says that e carries the actual sheafified phi generator
  to that same phi generator with restricted scalars. This characterizes the
  isomorphism induced by the identity p under sheafification; it does not merely
  assert an unspecified abstract isomorphism.
* Commutation of restriction and scalar restriction: `restrictionIso` is the
  canonical sectionwise identity, built by `PresheafOfModules.isoMk` from
  `Iso.refl _` and lifted by the existing fully faithful forgetful functor.
* The two displayed equations: `Equations e d adjS adjR` uses Lean composition
  in its forward order. Its first clause is
  `rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
   qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)`.
  Its second is
  `e.hom.app (qS.obj Q) ≫ JR.map (d.inv.app Q) ≫
   adjR.counit.app (rT.obj Q) = rT.map (adjS.counit.app Q)`.
  The explicit d inverses insert the sectionwise identity identified in the TeX.
* The unit generator and counit evaluation clauses are both stated in
  `adjunctionGenerators`: the unit is `generator ... W.unop.hom x`, and the
  fixed counit maps `generator ... phi x` to x for every phi and section.
* Additivity and exactness of all six functors: `scalarExact` and `sliceExact`
  state finite-limit and finite-colimit preservation for r and r_U; their
  additivity is Mathlib's existing instance. The four localized functors use
  the existing `localizedSystemExtensionAdditive/Limits/Colimits` and
  `localizedSystemRestrictionAdditive/Limits/Colimits` instances. No flatness
  class or algebraic flatness assumption appears.
* Cochain complexes: the second clause of `Transport` uses
  `mapHomologicalComplex (.up ℤ)` for all six functors, both comparisons and the
  two adjunctions. Thus it asserts both equations for all cochain complexes,
  with no boundedness restriction.
* Unbounded derived categories: the third clause uses `derivedSquare`, built
  from the published `mapDerivedCategoryCompIso` and
  `mapDerivedCategoryNatIso`, with the recorded `exactDerivedAdjunction`.
  These are the standard localization factors and the localized original units
  and counits, not newly chosen derived transformations.
* Strict inverse towers: Mathlib `ℕᵒᵖ ⥤ A`, with index 0 corresponding to the
  node's index 1. The fourth clause uses `Functor.whiskeringRight` and
  `Adjunction.whiskerRight`. Its fifth applies cochain functors to these strict
  tower functors; its sixth derives them and uses `exactDerivedAdjunction` on
  the levelwise adjunctions. Tower exactness infrastructure is obtained by
  the explicit finite-limit/colimit instances inside Transport from the
  functor-category preservation API, whose limits and colimits are levelwise.
* The final assertion `transportedEquations U a e` quantifies over chosen
  derived categories of the four module categories and the four strict tower
  categories. These are only localization-size choices; the standard choices
  always exist. Mathlib's original abelian instances are used explicitly,
  without choosing an alternative abelian structure. The same e works for
  every such choice. Neither flatness nor boundedness is introduced.

Dependency declarations used (module, name):

* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`, `Sheaf.over`, `GrothendieckTopology.overPullback`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is a transparent abbreviation of the `SheafOfModules` used throughout.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, its additive instance; its presheaf analogue
  `PresheafOfModules.restrictScalars` supplies p's source.
* `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`, `extensionByZeroPresheafSection`.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`.
* `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `localizedSystemExtension`, `localizedSystemRestriction`,
  `localizedSystemExact`, the six exactness instances,
  `localizedSystemAdjunction_existsUnique`, `localizedSystemAdjunction`.
* `Mathlib.CategoryTheory.Functor.OfSequence`: inverse systems are functors on
  ℕᵒᵖ as `Functor.ofOpSequence` specifies; morphisms are natural transformations.
* `Mathlib.CategoryTheory.Abelian.FunctorCategory`:
  `CategoryTheory.Abelian.functorCategoryAbelian`.
* `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, and
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso`.
* `Sheaf.SixFunctors.OpenTensorNormalizationData`:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`.
* Proof dependency `lem-weil-pbc-localization-universal-property` is the existing
  `Mathlib.CategoryTheory.Localization.Predicate` interface, imported as a proof
  dependency: `Localization.liftNatIso`, `liftNatTrans`, `natTrans_ext`.

Edge cases checked: if V has no map to U the direct sum is zero and all generator
clauses are empty there, while p's identity clause still quantifies over its zero
tuple. Multiple arrows V → U remain distinct summands. With a unique arrow the
normalization is the usual one summand map. Zero rings, zero modules, nonflat ring
maps and the identity map are permitted. Complex degrees range over all ℤ, and
towers have every natural-number level with no eventual-constancy assumption.
No equalities of site object and morphism universes were imposed.

Searches actually run:

* LeanFinder: “Restriction of scalars commutes with sheafified slice extension by
  zero with units counits and derived towers”: eight sheafification comparison
  hits, including `sheafificationCompToSheaf`; no complete statement match.
* Loogle: `SheafOfModules.restrictScalars, SheafOfModules.overFunctor`: zero hits.
* msearch grep: `extensionByZero.*restrictScalars|restrictScalars.*extensionByZero`:
  zero Mathlib hits.
* LeanSearch: “Restriction of scalars commutes with extension by zero of sheaves
  of modules on a localized site and respects the unit and counit”: eight hits,
  including presheaf scalar restriction and ordinary module adjunctions; none
  states the normalized slice-extension square with its tower consequences.
* rg in live `lean/WeilConjectures` and `lean/Sheaf` for the node id: no match.
  The direct combined extensionByZero/restrictScalars pattern also had no match.
  A broader scalar/adjunction search found scheme and constant-coefficient
  results, not this general ringed-site statement. The upstream name catalogue
  likewise contains no RingedOpenScalar/scalarExact match.

Validation: the full module compiled in sandbox and named module modes using the
prescribed scompile.py wrapper. The clean final run emitted no errors or warnings.
No STATEMENT-DISPUTED finding or source/node correction.

## Second reading by Q45

This is the author's separate rereading; independent delivery review belongs to
the maintainer. I reopened the node, its seven proof steps, the recorded dependency
interfaces and the finished Lean file. I checked the direction of e (S-extension,
then r, to r_U followed by R-extension) and the inverses of d in both equations.
The ordinary unit normalization is the uniquely fixed recorded adjunction, and
adjunctionGenerators includes the counit on all summands, not just the identity
arrow. The presheaf identity quantifies over all tuples; the sheaf normalization
uses the actual sheafification unit. The five Transport consequences after the
ordinary equation are respectively cochains, derived modules, strict towers,
cochains of strict towers and derived strict towers. The latter adjunctions are
localizations of the whiskered original adjunctions. The initial draft's missing
concrete abelian instances were replaced by explicit applications of Mathlib's
same abelian structure; no abstract replacement category or additional equality
of universes was used. Every mathematical clause is accounted for above, and the
node's statement, statement dependencies and proof were preserved.
