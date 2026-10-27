## Worker report

The module `Sheaf.CategoryTheory.ModuleShriekForgetfulCounitCriterion` constructs
`CategoryTheory.moduleShriekForgetfulComparison` with real data and states
`CategoryTheory.isIso_moduleShriekForgetfulComparison_of_localizedCounit` with `sorry`.
The source read was `literature/stacks-project/sites-modules.tex`,
`remark-when-shriek-equal` (Tag 0798), especially `equation-compare-on-localizations`,
and the preceding generator calculation of Tag 0797. The node statement is unchanged.
There are no new nodes or dependency repairs.

Hypothesis and clause correspondence:

- Small-site size convention: independent `c`, `d`, `vc`, `vd` bind the two object
  and morphism universes; all ring and module values lie in `max c d vc vd r`.
  The extra universe `r` is arbitrary. No site object and morphism universes are equated.
- Sites: `J : Precoverage C`, `K : Precoverage D`, with `hJ : J.IsSiteForCoverings`
  and `hK : K.IsSiteForCoverings`; sheaves use their generated Grothendieck topologies.
  This uses the recorded site axioms rather than the stronger indexed-composition class.
- The continuous functor u is `F : C ⥤ D`. `hcover` is Stacks 00WV(a), and
  `hpullback` is 00WV(b), preservation of pullbacks of covering arrows only. The
  `F.IsContinuous` instance exposes their consequence needed to type precomposition.
  `F.IsCocontinuous` is clause (1) of the recorded special-cocontinuity dependency;
  none of its extra special-cocontinuity clauses is imposed.
- The commutative coefficient ring is `R : Sheaf K.toGrothendieck CommRingCat`.
  Its ring sheaf is obtained by `sheafCompose` with `forget₂ CommRingCat RingCat`.
  R' is that ring sheaf's image under `F.sheafPushforwardContinuous RingCat`.
- Mod(R) and Mod(R') are exactly `ringedSiteModules` at those two ring sheaves.
  T is `SheafOfModules.pushforward` with structural map `𝟙 R'`, hence literal
  precomposition without a scalar extension or an arbitrary substitute map.
- F_C and F_D are `SheafOfModules.toSheaf`. T^Ab is
  `F.sheafPushforwardContinuous AddCommGrpCat`.
- The chosen additive left adjoint is `L`, `[L.Additive]`, `adjL : L ⊣ T`;
  eta is `adjL.unit`. The chosen abelian left adjoint is `A` with `adjA`.
  Mathlib's `Adjunction.homEquiv` is precisely the natural Hom bijection in the node.
- Localized sites are `J.toGrothendieck.over U` and
  `K.toGrothendieck.over (F.obj U)`. Their induced functor is literally `Over.post F`.
  The explicitly stipulated slice continuity is a dependent instance binder;
  slice cocontinuity is the Mathlib instance following from global cocontinuity.
- `AU U` and `adjU U` are the fixed slice abelian left adjoints and adjunctions.
  `Sheaf.over` restricts R, after its underlying additive-group functor
  `forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat`.
- The maps c_U are exactly `(adjU U).counit.app` at this restricted abelian ring
  sheaf, not arbitrary isomorphisms of its source and target. Precomposition of
  this ring on the slice has sections R(F(V)), the same as R' restricted to U.
  `hcounit : ∀ U, IsIso (...)` renders every localized counit hypothesis.
- The comparison is constructed as `((adjA.whiskerRight _).homEquiv _ _).symm`
  of `Functor.whiskerRight adjL.unit (SheafOfModules.toSheaf _)`. Its component is
  the adjunct of the underlying module unit exactly as required. The underlying
  precomposition/forgetting square agrees definitionally. Thus this definition
  constructs the natural transformation, not merely a chosen map with the same ends.
- The conclusion is `IsIso (moduleShriekForgetfulComparison ... adjL ... adjA)`.
  It asserts invertibility of the specified natural transformation itself.
  There is no equalizer-preservation hypothesis, global pullback hypothesis,
  terminal-object hypothesis, or equivalence hypothesis on a slice.

Recorded statement dependencies used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`:
  the documented first conjunct `Functor.IsCocontinuous` of
  `CategoryTheory.Functor.IsSpecialCocontinuousForCoverings`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.pushforward` and the recorded localization API. In its public
  import `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`,
  `Sheaf.over`, and `Over.post` give the actual slice sites and restriction.
- `def-weil-size-convention` is metatheoretic and has no declaration to import;
  it is rendered by the explicit universe bounds above.

Proof-only imports are all available recorded proof dependencies:
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`,
`WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`,
`WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`,
`WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
The generator-data node and co-Yoneda node have no recorded module on the read base;
no import is invented for them. They are proof inputs, not missing statement notions.
The seven-step proof in the theorem docstring preserves the node's generator,
unit-normalization, triangle-identity, coproduct, and cokernel arguments.

Edge cases checked mathematically against the statement and constructions:
identity F (the adjunction comparison is the adjoint-uniqueness identification),
empty source site (all source module objects are zero and left adjoints preserve
initial objects), zero coefficient ring (the only module sheaf is zero), empty
coverings and empty coproducts, and arbitrary non-subterminal U (all arrows into U
are retained by `Over U`, rather than replacing a slice by an open subspace).
No conclusion requires generators to be projective. The proof's presentation
uses the kernel only to make a two-term coproduct presentation.

Searches actually run through `batch2/msearch.py`:

- leanfinder: `Module lower shriek commutes with forgetting to abelian sheaves if
  every localized counit at the coefficient ring is an isomorphism`. Eight hits,
  including `SheafOfModules.map_ιFree_mapFree_hom`, module sheafification adjuncts,
  and forget-to-presheaf comparison isomorphisms. None states this criterion.
- loogle: `Adjunction, NatTrans, IsIso`. Returned no hits and the diagnostic
  `unknown identifier 'Adjunction'`; this search provided no usable result.
- grep: `shriek|forget.*[Cc]ompatib|[Cc]ompatib.*forget` in
  `Algebra/Category/ModuleCat/Sheaf`. No hits.
- Local rg searches in `lean/WeilConjectures` and `lean/Sheaf` for shriek/forgetting
  comparisons and counit criteria found the stronger consumer
  `LocalSliceModuleShriekExact` and unrelated derived/open shriek comparisons;
  none states Tag 0798's localized coefficient counit criterion. The exact item id
  has no upstream declaration. Both proposed declaration names were also searched
  in Mathlib, WeilConjectures, and Sheaf and were absent.

The initial compile exposed unconstrained universes at the identity ring map;
explicit coefficient universes and the target ring of `pushforward` resolve them.
A further probe read the comparison's universe order, so its final theorem call
supplies all five levels explicitly. No universe equality was added. Diagnostic
probes were removed. No statement fault or disputed mathematical claim was found.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
