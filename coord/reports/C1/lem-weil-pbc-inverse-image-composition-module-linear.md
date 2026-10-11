## Worker report

Module `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear` states
`AlgebraicGeometry.etaleInverseImageCompositionModuleLinear`, with its sole proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- The schemes and morphisms are `X Y Z : Scheme.{u}`, `uMap : Y ⟶ X`,
  `vMap : Z ⟶ Y`; the composite is `vMap ≫ uMap`. No etaleness, finiteness,
  separation, or nonemptiness assumption is imposed on these morphisms or schemes.
- The arbitrary commutative coefficient ring is `R : CommRingCat.{u + 1}`.
  As in the recorded dependency, sheaves and modules live in universe `u + 1`.
- Each small etale site is `T.smallGrothendieckTopology @Etale`, definitionally
  the recorded `T.smallEtaleTopology`.
- `RX`, `RY`, `RZ` and `etaX`, `etaY`, `etaZ` are lambda parameters immediately
  applied to `constantSheaf … CommRingCat` of `R` and its `toSheafify` unit.
  They introduce no arbitrary ring sheaves or additional hypotheses. RingCat
  scalars are obtained by `sheafCompose … (forget₂ CommRingCat RingCat)`.
- The category of modules is Mathlib's general-site `SheafOfModules`, explicitly
  included in the dependency's `mathlib_match` and note (the recorded scheme
  specialization `Scheme.Modules` is not the category on the small etale site).
- The three `gamma` maps are the canonical constant-section maps of
  `etaleInverseImageModulesExact`: each equation, for every site object `W` and
  `r : R`, says gamma carries the sheafification image of `r` to that of `r`
  after base change. These equations characterize the dependency's gamma maps;
  they are not new geometric assumptions.
- The lambda-bound `UX`, `UY`, `UZ` are immediately applied to the actual
  `SheafOfModules.toSheaf` functors. The lambda-bound `PU`, `PV`, `PUV`
  are immediately applied to the direct images below, and `pU`, `pV`,
  `pUV` to identity comparisons. This keeps elaboration small and introduces
  no arbitrary substitute functors. Direct images are exactly `SheafOfModules.pushforward` along base change,
  with scalars through gamma; their underlying functors are `Etale.lowerStar`.
- `LU`, `LV`, `LUV`, with `eU`, `eV`, `eUV` and `aU`, `aV`, `aUV`, are the
  module inverse-image functors, forgetful comparisons and module adjunctions
  supplied by `etaleInverseImageModulesExact`. The three hom-equivalence
  compatibility equations are verbatim the property of those data in that
  dependency: forgetting identifies the module adjunction with the abelian
  adjunction via `e`. Universal quantification makes the result independent
  of a choice of witnesses in the dependency's existential theorem. No
  exactness or arbitrary-action hypothesis is added. The hom-equivalence equations
  also transport through `pU`, `pV`, `pUV`; these are lambda-bound comparisons
  immediately applied to `Iso.refl _`, so they add no hypothesis.
- Clause (1): the existential natural isomorphism `d` has source the module
  direct image for `vMap ≫ uMap` and target the successive direct images.
  The first conjunct says that, for every module `F`, its forgotten hom
  component, transported through `pU`, `pV` and `pUV`, is `(Etale.lowerStarComp … vMap uMap).inv.app …`. The source
  declaration has the reverse orientation to the node, hence `.inv`.
  A hom in `SheafOfModules` is sectionwise linear, so this is precisely
  linearity of the prescribed abelian map and the asserted module functor iso.
- Clause (2): the existential natural isomorphism `c : LU ⋙ LV ≅ LUV` has
  the specified direction. The second conjunct, for every module `G`, compares
  its forgotten hom through `eUV` with `eV` followed by inverse image of `eU`
  followed by `(Etale.upperStarComp … vMap uMap).inv.app …`. This conjugated
  equality specifies exactly the given abelian comparison under the three
  forgetful identifications, including the twice-applied inverse image.
- The third conjunct is the unit equation
  `(aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c.hom.app G) =
  aUV.unit.app G ≫ d.hom.app (LUV.obj G)` (here `PU`, `PV` abbreviate only
  in this report the displayed pushforward expressions). It is the composite
  adjunction unit transported along `d`, for every `G`.
- The fourth conjunct quantifies over every competing module natural iso `c'`
  and requires only the same unit equation; it concludes `c' = c`.
  Thus uniqueness is not weakened by additionally assuming forgotten equality.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` (its
  `smallGrothendieckTopology @Etale` expression is used for instance inference).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`,
  `SheafOfModules.toSheaf`, and its morphisms (general-site match recorded by
  def-weil-sheaf-of-modules-category). Also read the recorded scheme specialization
  in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`; its import supplies the
  structures and underlying-abelian adjunction compatibility used above.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.pushforward`, imported through the dependency module.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`,
  `Etale.lowerStarComp`, `Etale.upperStarComp` (all under AlgebraicGeometry).
  Read full signatures and docstrings; this module is imported transitively.

Edge cases checked before drafting: empty schemes/sites introduce no nonemptiness
requirement; the zero coefficient ring and zero modules are allowed; both morphisms
may be identities or arbitrary non-etale morphisms. Composition functor order and
both iso directions were checked against the recorded declarations. Naturality
is part of the natural iso type, and linearity is part of the module hom type;
there is no extra scalar-preservation conjunct or weakened underlying-map clause.

Source checked: the local Stacks TeX is absent on this remote machine. Read
https://stacks.math.columbia.edu/tag/03D8 and
https://stacks.math.columbia.edu/tag/03D7 instead: canonical module composition
isomorphisms and the module adjunction respectively. The node already supplies
its detailed five-step proof, reproduced in the theorem docstring.

Searches (real calls recorded by msearch.py in searches.jsonl):

- LeanFinder: `composition isomorphisms inverse direct image etale sheaves modules
  linear forgetful` — eight hits, including restriction of O_X-modules along
  open immersions and `SheafOfModules.toSheafCompSheafToPresheafIso`; no match.
- LeanSearch: `composition pullback sheaves modules compatibility forgetful abelian
  sheaves` — service unavailable, Internal Server Error.
- Loogle: `SheafOfModules.pullbackComp` — five hits, module pullback composition
  and coherence; none identifies the specified abelian comparison after forgetting.
- Mathlib grep via msearch: `pullbackComp|pushforwardComp` in
  `Algebra/Category/ModuleCat/Sheaf` — ten hits, built-in module composition
  comparisons, but no constant-ring etale comparison to the abelian maps.
- `rg` on the project and source for composition comparisons and forgetful
  compatibility: source has general abelian `lowerStarComp`, `upperStarComp`,
  coherence and unrelated operations; no theorem asserting this module lift.
- Source grep of the exact item id: no match. Project/source grep of
  `upperStarComp.*toSheaf|lowerStarComp.*toSheaf`: no existing match.
- Names were checked against `dag/lean_names_upstream.json` and project/source;
  the new full declaration name is not already present.

All variables and the universe are explicit; no local notation, local instances,
private copies or `let` binders are used. The node statement is unchanged and
there is no STATEMENT-DISPUTED issue.

Validation: server single-file compile succeeded in 13.1 seconds, with no warnings
and with the default heartbeat limit. The delivery is prepared for an independent
second reader; no second-reading section has been authored by this worker.

## Second reading by C1

I read the item's node, all eight statement-dependency nodes and their recorded
signatures, the whole delivered Lean file, the whole imported
`EtaleInverseImageModulesExact.lean`, and the upstream definitions of `lowerStar`,
`upperStar`, their adjunction, `lowerStarComp` and `upperStarComp`. I also opened
Mathlib's small-etale topology, constant sheaf, general-site module category,
forgetful functor, pushforward and module composition declarations. This is an
independent reading, not a restatement based only on the worker's report.

Source: the local literature directory contains the citation lists but not the
Stacks TeX. I fetched the official source
https://raw.githubusercontent.com/stacks/stacks-project/master/sites-modules.tex
into this item's scratchpad and read lines 1133–1251: the preceding definition
of ringed-topos module pushforward/pullback, Lemma 03D7 at line 1197 and Lemma
03D8 at line 1236. I also read the rendered official tags
https://stacks.math.columbia.edu/tag/03D7 and
https://stacks.math.columbia.edu/tag/03D8. The source assumes morphisms of ringed
topoi and module sheaves; it imposes no Noetherian, finiteness, separation,
characteristic or nonemptiness hypothesis. The constant-ring specialization
is supplied by the recorded inverse-image module proposition. The node's
additional underlying-map and unit descriptions specify the canonical
composition comparisons using that proposition and the abelian-composition
node; they do not change the source's notion of composition.

The following is my object/hypothesis/conclusion list, matched to the Lean.
All entries pass.

1. Objects: schemes X, Y, Z, arbitrary scheme maps u:Y→X and v:Z→Y, and their
   composite. Lean: `(X Y Z : Scheme.{u}) (uMap : Y ⟶ X) (vMap : Z ⟶ Y)` and
   `vMap ≫ uMap`. No geometric property instance is required. The signature
   of the recorded `Scheme` is the usual scheme category, not a specialization.
2. Object: arbitrary commutative coefficient ring Lambda. Lean:
   `(R : CommRingCat.{u + 1})`. It requires neither a field nor a nonzero ring.
3. Objects: the three small etale sites and their constant ring sheaves.
   Lean: `T.smallGrothendieckTopology @Etale`, which the definition of
   `T.smallEtaleTopology` expands to; RX, RY, RZ are lambda-bound and immediately
   applied to `(constantSheaf ... CommRingCat.{u + 1}).obj R`. The eta binders
   are immediately applied to `toSheafify ... ((Functor.const T.Etaleᵒᵖ).obj R)`.
   Thus these are fixed sheafifications, not arbitrary coefficient sheaves.
4. Objects: Mod(T_et,Lambda), with sectionwise linear morphisms. Lean:
   `SheafOfModules.{u + 1} ((sheafCompose ... (forget₂ CommRingCat RingCat)).obj RT)`.
   I checked the dependency's general-site Mathlib match, not just its primary
   `Scheme.Modules` name: the latter is the Zariski structure-sheaf specialization
   and is deliberately not used. Mathlib's `SheafOfModules.Hom.val` is a morphism
   of presheaves of modules, so a module isomorphism proves the required linearity
   and linearity of its inverse. UX, UY, UZ reduce to `SheafOfModules.toSheaf`.
5. Objects: module direct images with the canonical scalar maps gamma for u,
   v and uv. Lean: gammaU, gammaV, gammaUV, followed by the three all-W, all-r
   constant-section equations; PU, PV, PUV are immediately applied to
   `SheafOfModules.pushforward` along `MorphismProperty.Over.pullback @Etale ⊤`
   with the corresponding gamma. The equations are precisely the canonical-map
   characterization provided by `etaleInverseImageModulesExact`, not new
   restrictions on the geometry. The constant-sheaf universal property makes
   this characterization unique. I checked the pushforward implementation:
   sections are the base-change sections with scalars restricted through gamma.
6. Objects: module inverse images for u, v and uv with their underlying abelian
   identifications and adjunctions. Lean: LU, LV, LUV, eU, eV, eUV and aU, aV,
   aUV. Each of the three homEquiv equations is the final hom-equivalence
   compatibility clause of `etaleInverseImageModulesExact` for that map.
   They specify the given module adjunction rather than posit a substitute
   action. The dependency supplies these witnesses; universal quantification
   handles any choice of those data. Additivity/exactness and the action
   construction need not be repeated as extra hypotheses to this comparison
   lemma. pU, pV, pUV are immediately applied to `Iso.refl _`, expressing the
   definitional underlying direct-image identifications.
7. Conclusion (1): d on every F is Lambda_X-linear and gives the specified
   natural module direct-image isomorphism. Lean: `d : PUV ≅ PV ⋙ PU`, with
   the first conjunct for every module F equating its forgotten hom, after
   the p identifications, to `(Etale.lowerStarComp ... vMap uMap).inv.app ...`.
   Upstream `lowerStarComp` runs from successive pushforwards to composite
   pushforward, so its inverse has exactly the node's direction. Module Hom
   supplies linearity; natural iso supplies naturality and invertibility.
8. Conclusion (2): c on every G is Lambda_Z-linear, including the twice-applied
   module inverse image, with the specified underlying abelian comparison.
   Lean: `c : LU ⋙ LV ≅ LUV`, and the second conjunct equates its forgotten hom
   through eUV with eV, inverse image of eU, and
   `(Etale.upperStarComp ... vMap uMap).inv.app ...`. Upstream upperStarComp
   runs from composite pullback to successive pullbacks. The inverse and the
   order of eV followed by upperStar(v).map(eU) are correct.
9. Conclusion: c transports the composite unit to the uv unit along d.
   Lean: for every G,
   `(aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c.hom.app G) =
    aUV.unit.app G ≫ d.hom.app (LUV.obj G)`.
   Both sides are module maps G→u_*v_*(uv)^{-1}G, and the composition order is
   exactly the displayed equation in the node. The homEquiv hypotheses identify
   these module units with the abelian ones under the e comparisons.
10. Conclusion: uniqueness among all module natural isomorphisms carrying that
    unit. Lean: the last conjunct quantifies `∀ c' : LU ⋙ LV ≅ LUV` and assumes
    only the same unit equation before concluding `c' = c`. In particular it
    does not weaken uniqueness by requiring c' to have the specified forgotten
    map as an additional hypothesis. The two existential isomorphisms precede
    all component clauses, so there is one natural comparison for every module.

Edge cases: the empty scheme is allowed in each scheme binder; no nonemptiness
is required of a scheme, a site object or a module. The small etale site of an
empty scheme still has its terminal object; no step presupposes a point. The
zero ring and zero module are allowed, and the resulting trivial scalar actions
cause no excluded case. Identity maps and arbitrary non-etale scheme morphisms
are covered. There is no index-family or degree parameter here, so empty-index
and n=0 cases introduce no separate condition. No characteristic is fixed.
Universe u is explicit and arbitrary; coefficients and modules use u+1 exactly
as the dependency and upstream abelian inverse-image functors do. The site is
essentially small at that level. This is a universe-polymorphic presentation,
not an additional finite-size hypothesis. All declaration variables are bound;
no independent test-object universe can make any premise vacuous.

Independent searches (different query words from the author; actual service
calls are appended to searches.jsonl):

- LeanFinder: `forgetting module sheaves preserves the composition comparison
  of inverse images and pushforwards` — eight hits. In particular
  `SheafOfModules.pushforwardComp_hom_app_val_app` describes the general-site
  composition for a literal composite site functor; it does not identify the
  scheme pullback-pasting comparison or prove the inverse-image assertion.
  Other hits concern pushforward versus forgetting and inclusion of sheaves
  into presheaves, not the present module lift.
- Loogle: `SheafOfModules.toSheaf` — twelve hits for the functor, its faithful,
  additive, limit and isomorphism reflection properties, and presheaf
  compatibility. None states this comparison lemma.
- LeanSearch: `The composition isomorphism of pullbacks of constant ring module
  sheaves agrees with the underlying abelian sheaf composition isomorphism` —
  unavailable (Internal Server Error), recorded without a no-match verdict.
- Direct rg on Mathlib's module-sheaf files found `pushforwardComp`,
  `pullbackComp`, `conjugateEquiv_pullbackComp_inv`; I read their signatures
  and bodies. They concern canonical module adjoints and composited scalar
  maps, not agreement with the prescribed abelian small-etale comparisons.
- Direct rg on the source's module-sheaf and SixFunctors/Etale directories and
  the project's etale/module-sheaf files found abelian composition/coherence,
  ring-action and forgetful constructions, but no existing theorem with both
  the module lift and the underlying-abelian identifications. The wider source
  search also finds `lowerStarComp (ModuleCat Λ)`; it is a comparison in the
  alternative fixed-ModuleCat sheaf encoding, not this recorded ring-sheaf
  module category or its forgetful compatibility assertion.
- Exact full-name and `upperStarComp.*toSheaf`, `lowerStarComp.*toSheaf` searches,
  also in reverse order, on all source/project Lean and dag/lean_names_upstream.json
  found no existing declaration. No duplicate definition or replacement
  dependency module is needed.

No mismatch was found. I changed only this report, adding the independent
reading and source/search evidence; the module, node statement, dependencies
and lean record are unchanged. There are no new nodes, dependency modules,
statement corrections or disputed statements to audit. The one import supplies
all notions used. The module and theorem docstrings give the source and exact
blueprint id; the five proof steps match the node's ring-map composition,
direct-image linearity, composite hom-bijection, inverse-image linearity, and
naturality/inverse/uniqueness arguments. There is one named theorem with sole
proof `sorry`, and no definitions, proved helper results, local notation,
private declarations, local instances or hidden `let`/`show` binders.

Validation: independent server single-file compile succeeded in 12.7 s, exit 0,
with no warnings. Every line is at most 100 characters. An exact text comparison
of the theorem signature before `:= by` with node `lean.statement` succeeded,
including its trailing newline. The server uses autoImplicit=false, and an
additional by-eye check found no unbound variable or universe.
