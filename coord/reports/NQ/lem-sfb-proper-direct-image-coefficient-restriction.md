## Worker report

The module `Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` states
`AlgebraicGeometry.ProEtale.CondensedRing.properDirectImageCoefficientRestriction`.
Its only proof is `sorry`; it defines no new object and changes only the item's lean record.
The source read is the current `literature/blueprint/latest/blueprint/` compact-support
coefficient proof, Independence and Composition paragraphs, together with the complete DAG node.
The resolved stage-1 re-split repair note was read; its two transpose nodes are retained.

Hypothesis and clause correspondence:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`. The field and positive characteristic
  different from ell are `(k : Type u) [Field k] [Fact (ringChar k).Prime]`
  and `[Fact (ringChar k ≠ ell)]`, following the setting dependency's own convention.
- `Z Y : Over (Spec (.of k))`, each with `LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated` on its structure morphism, give exactly separated finite-type k-schemes.
  `p : Z ⟶ Y` makes p a k-morphism, with `[IsProper p.left]` for properness.
- `v : V ⟶ Y.left` with `[IsOpenImmersion v]` gives the open immersion.
  `u : ZV ⟶ Z.left`, `q : ZV ⟶ V`, and `sq : IsPullback u q p.left v`
  present ZV as the fibre product, with its two projections. This uses an arbitrary
  cartesian presentation rather than only the library's chosen pullback. Its universal
  property induces exactly the inherited k-structures and open immersion u; none is
  an additional independent hypothesis, and no finite-type condition on V is imposed.
- `Λ Λ' : ScalarSixRing.{u}` are bundled commutative condensed rings. `a : Λ ⟶ Λ'`
  and `_ha : ListedCoefficientMap ell a` use precisely the dependency's six generators
  and finite composites: finite ell-primary rings, integral/field finite extensions,
  localization, the algebraic closure inclusion, continuous integral-to-finite maps.
  Its algebraic closure endpoint uses the finite-subextension condensed convention.
- `M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z.left)` is an
  object of the ordinary unbounded derived category of modules over the pulled-back
  coefficient ring. `_hM` is the conjunction of `constantModelBoundedConstructible`
  and `DerivedCategory.finiteTorAmplitude`, exactly M in Dctf.
- `RootCoordinateFace.lower` is the named total right derived composite
  `moduleObjectDerivedPushforward`. `scalarSixPull` is exact inverse image localized
  termwise, the published canonical presentation of total derived inverse image.
  `scalarSixChange` is the published total derived extension along `coefficientMap`.
- The first and second conjuncts are `IsIso` of the actual
  `RootCoordinateFace.exchange` at M over Λ and at T_Z M over Λ', respectively.
  The exchange's real definition is `mateEquiv` of `RootCoordinateFace.squareUpper`
  with the recorded exact-pullback/derived-pushforward adjunctions. Thus it inserts the
  q-unit, uses q* v* ≅ u* p*, then the restricted p-counit, exactly as required.
- The third conjunct is the required equality. Reading Lean's ≫ from left to right,
  its left side is theta_v.hom, v* gamma_p, b over Λ', and Rq_* theta_u.inv.
  The right side is T_V(b over Λ) followed by gamma_q at u* M. Here
  `scalarDirectImagePullbackData.theta` is the inverse-image coefficient identification,
  fixed by `thetaNormalization`, and `scalarDirectImageMate` is exactly the specified
  unit/pullback-comparison/counit gamma. Both paths start at T_V(v* Rp_* M) and end
  at Rq_* T_ZV(u* M). The two theta factors supply exactly the identifications in the
  node; no additional transport, inverse exchange, or arbitrary morphism is inserted.
- The last two conjuncts specialize the actual exchange to the identity square, over
  Λ at M and over Λ' at T_Z M. Postcomposition by Rp_* of the source identity-pullback
  identification equals the target identity-pullback identification. Therefore the
  transported exchange is the identity. The identifications are the localization of
  `upperStarId` followed by `Functor.mapDerivedCategoryIdIso`, not chosen isomorphisms.

Dependency interfaces read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the standing scheme binders and `compactificationOverField` setting documentation
  (no compactification is needed for this proper/open square).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `AlgebraicGeometry.ProEtale.coefficientMap`, identity/composition and both coefficient
  naturality squares; used through the exact published `scalarSixChange` construction.
- `Sheaf.Paper.FiniteConstantRingedLocalModel`, publicly retaining
  `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and the same finite-Tor
  condition as `ConstantModelConstructibleFiniteTor`. The ringed local-model repair is
  not substituted for the internal-module notion in this statement.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`,
  `moduleObjectDerivedPullback` and the published derived-adjunction interfaces.
- `Sheaf.SixFunctors.ScalarSixDirectImage`:
  `scalarSixDirectImage`; its public dependency `ScalarDirectImageMateCoherence`
  supplies `scalarDirectImageMate` and `scalarDirectImagePullbackData`.
- `Sheaf.SixFunctors.ScalarSixPullback`, publicly imported by the previous dependency:
  `scalarSixPullback`, `ScalarSixPullbackData.theta`, its canonical normalization and
  composition law; `ScalarSixDefinitions` supplies `scalarSixPull` and `scalarSixChange`.
- `Sheaf.Paper.RootTowerCoordinateFace`, already public through the direct-image mate:
  `RootCoordinateFace.exchange`, `squareUpper`, `upperComp`, `adjunction`, and `lower`.
  The general exchange is reused without a second definition.
- Plain proof imports retain the recorded `ScalarSixCtf`, `FiniteProperBaseChange`,
  `IntegralProperBaseChange`, and `ProperBaseChangeRational` modules. The two extracted
  transpose lemmas have no Lean records yet, so there are no modules to import for them.

Edge cases checked before writing and on second reading: V empty; V = Y and identity
square; M = 0; empty schemes; identity coefficient changes (including the algebraic
closure endpoint); the zero coefficient ring; nonflat Z/ell² → F_ell; finite composites
and the continuous integral-to-finite generator. Nothing assumes flatness, density,
nonemptiness, a special finite extension, or a particular cartesian representative.
The site, coefficient, and ambient-derived universes are those of the published API:
Scheme.{u}, pro-etale site object universe u+1, and Ab.{u+1}; no site universes are equated.

Searches for an existing complete statement (no exact match):

- msearch LeanFinder: "Proper derived direct image coefficient comparison commutes with
  restriction to an open base change square". Eight ordinary scheme section-map identities
  (`Scheme.Hom.map_appLE` and relatives); none states the module-derived coefficient square.
- msearch Loogle: "CategoryTheory.mateEquiv_hcomp, CategoryTheory.mateEquiv".
  One hit, `CategoryTheory.mateEquiv_hcomp` in Mathlib.CategoryTheory.Adjunction.Mates:
  a general mate-pasting theorem, without this geometric statement or invertibility.
- msearch LeanSearch: "Derived coefficient change commutes with proper pushforward and
  open restriction". Eight underived module pushforward/restriction identities,
  including `Scheme.Modules.restrictAdjunction`; no exact derived statement.
- msearch grep: `coefficient.*restrict|restrict.*coefficient|mateEquiv_hcomp`, in
  Mathlib/CategoryTheory. Seven hits, all abstract mate-pasting declarations/usages.
- Project rg, in both lean/WeilConjectures and lean/Sheaf, for
  `properDirectImageCoefficientRestriction|proper_direct_image_coefficient_restriction`:
  no existing declaration. Upstream grep of the item id: no match.
- Concept search for open exchange and restriction/coefficient comparisons in the
  SixFunctors directories found the canonical `RootCoordinateFace.exchange` and the
  canonical scalar mate already imported by the recorded dependencies; these are reused.
  Targeted `coefficient.*[Rr]estrict|[Rr]estrict.*coefficient` on ChangeOfCoefficients and
  ScalarDirectImageMateCoherence found only scalar restriction/adjunction definitions.

No statement correction, new node, dependency repair, or statement dispute is needed.

## Second reading by NQ

A separate reading pass reopened the complete DAG statement and the written Lean
signature. No second agent was started, as the dispatch brief prohibits that; the
maintainer supplies the independent review. This pass checked each hypothesis and
conjunct using the correspondence above. In particular theta_v is the forward
comparison, whereas the final Rq_* transport uses theta_u inverse. Their domains
and codomains agree with the node's explicitly identified endpoints. The cartesian
presentation supplies the inherited structures, so no independent properness/open
assumption on q/u was added. Both identity-square equations are included; neither
is a tautological pullback-condition conjunct. The IsIso assertions concern the
specified exchange maps themselves. The compiler exposed a namespace-resolution mismatch in `upperStarId`: the unqualified
name selected the abelian-sheaf version. A public import of the module-object Coherence
module and the fully qualified module-object name repair the mismatch; the equation
and its mathematical content are unchanged. No other mismatches were found.

## Validation

`scompile.py NQ lem-sfb-proper-direct-image-coefficient-restriction <module>` passed
both sandbox (7.0 s) and library (8.4 s) compilation, with no diagnostics.
`deliver2.py NQ lem-sfb-proper-direct-image-coefficient-restriction --no-push`
printed OK: preflight and compilation pass. The final delivery uses the same wrappers.
