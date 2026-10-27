## Worker report

The module `Sheaf.CategoryTheory.Sites.UnboundedLeraySections` states Stacks
0D6H's objectwise unbounded Leray comparison, after forgetting scalars. Its only
postponed theorem is
`CategoryTheory.UnboundedSectionsLocalization.unboundedLeraySections`.
The five auxiliary definitions give ordinary and derived restriction maps, an
abbreviation of the canonical continuous module pushforward, the literal identity of its section functors, and the literal
identity between its section complexes. Every definition contains real data.
The theorem has `sorry`; nothing is proved in this delivery. The naturality
proof field in the restriction definition only checks the functorial data of
the explicitly constructed map; it is the symmetry of the existing presheaf
naturality equation.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The common module universe and small sites are `{C D : Type u}` with
  `[SmallCategory C] [SmallCategory D]`, topologies `J` and `K`, and coefficient
  values in `CommRingCat.{u}` and module values in universe `u`. The independent
  localization Hom universes are `wC`, `wD`, and `wA`; `HasDerivedCategory`
  records the selected localizations, not a boundedness or existence restriction.
- The two commutative ring sheaves are `A : Sheaf J CommRingCat.{u}` and
  `B : Sheaf K CommRingCat.{u}`. `sheafCompose` forgets commutativity solely to
  use the dependency's existing `ringedSiteModules`/Mathlib module categories.
- The given ringed-site morphism is represented by `u : D ⥤ C`, its continuity
  instance `[u.IsContinuous K J]`, and the structural map
  `a : B ⟶ (u.sheafPushforwardContinuous CommRingCat K J).obj A`.
  `[PreservesFiniteLimits (u.sheafPullback (Type u) K J)]` expresses that its
  induced sheaf adjunction is a geometric morphism, as in the ringed-topos
  dependency. The adjoint of `a` is the inverse-image structural ring map.
  No arbitrary module lift or geometric morphism disconnected from `u` is supplied.
- `lerayDirectImage A B u a` is exactly `SheafOfModules.pushforward` of the
  dependency's `sectionModuleMap u a`. Its section module at
  `V` is the source module at `u.obj V` with scalar restriction along `a` at `V`.
  `leraySectionComplexIdentity` is `Iso.refl` of the resulting abelian complexes,
  including all differentials; it is not an arbitrary comparison.
- The unbounded categories are `DerivedCategory` of these module categories
  and of `AddCommGrpCat.{u}`. `rightDerivedFunctor` is the existing total right
  derived construction using K-injective resolutions, with K-injectivity the
  existing `CochainComplex.IsKInjective` condition. The Grothendieck/K-injective
  instances come from the imported small-site infrastructure, not added hypotheses.
- `e : ∀ V : D, (lerayDirectImage ...).rightDerivedFunctor ⋙
  (sectionEvaluation ... V).rightDerivedFunctor ≅
  (sectionEvaluation ... (u.obj V)).rightDerivedFunctor` is the requested natural isomorphism
  `RΓ(V,Rf_*E) ≅ RΓ(u(V),E)` in `D(Ab)`. An isomorphism of functors includes
  naturality for every derived object `E` and every derived arrow.
- The first conjunct tests **every** K-injective `I` and site object `V`.
  It pins down the canonical comparison by the equation between the existing
  derived units, at `X = (HomotopyCategory.quotient _ _).obj I`:
  `η_source(X) ≫ e(V).inv(Qh X) = Qh(section-identity inverse at X) ≫ η_composite(X)`.
  Here `η_composite` is `Functor.rightDerivedFunctorCompUnit` including its
  canonical composition associator; its components are the target evaluation
  unit followed by `RΓ(V).map(η_f(X))`. The identity before this unit is the
  existing `NatTrans.mapHomotopyCategory` of `leraySectionFunctorIdentity.inv`.
  The equation is written with `HEq` to compare the two associatively presented
  Hom types without making elaboration repeatedly unfold the total-derived
  construction. Both sides have the same source and target after the canonical
  functor-composition definitional identifications; heterogeneous equality
  expresses equality of those actual arrows, not mere existence of an isomorphism.
  The source of the two sides is canonically the localized abelian complex
  `I(u(V)) = (f_*I)(V)`. This is the universal composition normalization,
  and fixes `e(V)` because `η_source(X)` is invertible for K-injective `I`.
  For any K-injective target resolution `j : f_*I ⟶ T`, naturality of the
  target derived unit turns this same equation into the inverse of `Q(j(V))`
  under the canonical resolution identifications in the DAG proof. It does
  not assume that `f_*I` is K-injective. The formula uses existing
  `Functor.rightDerivedFunctorUnit`, not an arbitrary chosen comparison.
- The final conjunct quantifies over every `v : V' ⟶ V` and is equality of
  natural transformations:
  `Rf_* ◁ restriction(v) ≫ e(V') = e(V) ≫ restriction(u.map v)`.
  `lerayRestriction` is the actual presheaf restriction map and
  `lerayDerivedRestriction` is its existing total-right-derived natural
  transformation. Identities and composites are included.
- The `∃!` specifies the unique derived-unit-normalized family, expressing the
  word "canonical". No boundedness, flatness, quasi-coherence, final object,
  nonzero-ring, separatedness or representability hypothesis occurs.

Dependency declarations inspected and used:

- `def-weil-size-convention`: its convention-only record is implemented by the
  explicit universes and `HasDerivedCategory` instances.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; Mathlib's
  `GrothendieckTopology`, `Functor.IsContinuous` and `Functor.sheafPullback`
  supply the topology and associated sheaf adjunction. No extra coverage axiom
  or ambient finite-limit condition is imposed.
- `def-weil-pbc-ringed-topos-morphism`:
  `Sheaf.CategoryTheory.RingedToposMorphism`,
  `CategoryTheory.RingedToposMorphism`. Here the canonical site-induced
  geometric adjunction and the adjoint of `a` encode its geometric and ring
  components; the module direct image is the canonical site pushforward.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `DerivedCategory.Q`.
- New statement dependency `def-sfb-ringed-site-section-functors`:
  `Sheaf.CategoryTheory.Sites.RingedSiteSectionFunctors`, with namespace
  `CategoryTheory.RingedSiteSectionFunctors`. `sectionEvaluation` is the transparent
  alias of `UnboundedSectionsLocalization.evaluation`; `modulesGrothendieck` aliases
  its existing Grothendieck structure; `pushforwardAdditive` aliases
  `SubterminalImageCalculus.pushforwardAdditive`; `sectionModuleMap` aliases
  `SheafOfModules.ringedSiteModuleMap`. All four original signatures and docstrings
  were read. The theorem directly uses the first and fourth aliases, and obtains
  the unchanged supporting instances through the new module's public imports.
  No conclusion of either the localization or subterminal theorem is used in the
  Leray statement. The three theorem nodes are absent from `stmt_deps`.
- `lem-weil-pbc-localize-ringed-site-morphism` remains a proof dependency,
  with its module imported as `import`, for the localized comparison in proof step 2.
- Proof imports also include the recorded K-injective existence module
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
  (`CategoryTheory.isKInjective_restrict_localized`),
  `Sheaf.CategoryTheory.FiniteTypeRestrictionExact`
  (`SheafOfModules.overFunctor_exact`), Mathlib constant-sheaf adjunction and
  left-exact sheafification, the recorded singleton-site module comparison,
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
  (`CategoryTheory.ringedToposDerivedPushforwardComposition`), and Mathlib's
  `CochainComplex.IsKInjective.Qh_map_bijective`.

The source 0D6H was read in `literature/stacks-project/sites-cohomology.tex`,
including its punctual-topos proof and the localization argument for the second
assertion. The latest blueprint direct-images proof was inspected along the
node's recorded ancestor route. The accepted stage-1 statement, proof, and
review are preserved. The prior worker ending concerned an unchanged split;
the current queue marks this as stage 2 and the live input has no `lean` record.
This delivery adds its Lean statement and does not reopen its split.

Edge cases checked: the zero sheaf and zero coefficient ring are allowed;
`u = 𝟭`, identity and composite restriction arrows are included; `I` and `T`
are unbounded ℤ-indexed complexes; non-flat coefficient maps are permitted;
the sites need not have final objects or all finite limits. Arbitrary `V` is
quantified over without a terminality or affineness restriction. If the target
site has no objects the comparison family and its naturality conditions are
vacuous, as they should be. The derived-unit condition does not assert
preservation of K-injectives by direct image.

Searches for reuse (all through the prescribed search tool, plus source reads):

- LeanFinder: "For a morphism of ringed sites unbounded derived evaluation at V
  after derived pushforward is naturally isomorphic to derived evaluation at
  u(V), compatible with restriction". Eight hits: ordinary
  `SheafOfModules.pushforwardNatIso`, `.pushforwardComp`, and sheafification /
  continuous-pushforward comparison component lemmas; no unbounded Leray theorem.
- Loogle: `Functor.rightDerivedFunctor, SheafOfModules.pushforward,
  GrothendieckTopology.overPullback`. No indexed hit; the upstream derived
  functor name is not indexed by the Mathlib service. Its source was read directly.
- Mathlib grep: `Leray|leray|rightDerivedFunctorCompIso` in `CategoryTheory`.
  No hit; the required unbounded composition infrastructure lives upstream.
- LeanSearch: "unbounded derived sections evaluation ringed site Leray morphism
  of sites". Eight hits, including `CategoryTheory.sheafSectionsNatIsoEvaluation`
  and `SheafOfModules.evaluation`, plus residue-field evaluation lemmas.
  These provide ordinary evaluation, not this statement.
- `rg` of project `lean/Sheaf` and `lean/WeilConjectures` for
  `UnboundedLeraySections|unboundedLeraySections|derived.*[Ss]ections.*[Pp]ushforward|
  [Ll]eray.*unbounded`, and `grep -rn` for this blueprint id in
  `lean/WeilConjectures`: no exact declaration. Scheme and finite-pushforward
  comparisons have additional geometric hypotheses; the existing objectwise
  localization theorem does not compare a general ringed-site pushforward.
- Source inspection of `RightDerivedFunctor/Defs.lean`, `KInjective.lean`,
  `Comp.lean`, `UnboundedSectionsLocalization.lean` and the general localization
  module supplied all constructions used. The return identifies their missing
  definition-node ownership, now supplied by the new alias node below; no
  dependency repair module is needed.

No statement correction, node fault or disputed mathematical statement is claimed.

Validation: the module compiled in module mode on the server against the live
published library, both as the sandbox module and under its intended module name.
The final dry run and delivery are recorded by the prescribed wrapper.


## New nodes

`def-sfb-ringed-site-section-functors` owns
`Sheaf.CategoryTheory.Sites.RingedSiteSectionFunctors`. Its self-contained statement
introduces small sites, ring sheaves and module sheaves, evaluation forgetting
scalars, continuous direct image with its structural scalar action, and the
underlying-ring map for commutative ring sheaves. Its four declarations are
transparent aliases with real data; no new construction, instance search rule or
postponed proof is introduced. Sources are Stacks 0D6H,
`lemma-Leray-unbounded`, and 04J0, `lemma-localize-morphism-ringed-sites`.
The existing definitions were found in the three theorem modules, but no DAG
**definition** node owns them. The return specifically authorizes aliases to give
these definitions such an owner. The item now cites this definition node instead
of the three theorem nodes. The definition cites the existing size convention,
site definitions and module-sheaf category.

New-node searches, executed through `msearch.py` and recorded in `searches.jsonl`:

- LeanSearch, `Evaluation of module sheaves on a small ringed site forgetting
  scalars and additive continuous direct image induced by a morphism of ring
  sheaves`: eight results, including `SheafOfModules.evaluation`, `.forget`,
  `.pushforward` and `.toSheaf`. These are the ordinary constructions reused
  by the aliases, not an existing definition-node owner of the joint interface.
- Loogle, `SheafOfModules.evaluation, SheafOfModules.pushforward`: zero hits.
- Mathlib grep, `def evaluation|abbrev evaluation|pushforward.*Additive|ringedSiteModuleMap`,
  in `Algebra/Category/ModuleCat/Sheaf`: zero hits from that service.
- Local `rg` of `lean/Sheaf`, `lean/WeilConjectures` and `dag/nodes` for
  `sectionEvaluation|sectionModuleMap|RingedSiteSectionFunctors` found unrelated
  scheme-diagonal and private evaluation maps, and no declaration in this new
  namespace. A DAG search for the original qualified names found the three
  theorem nodes and another localized-morphism theorem, with no definition owner.
  `tools/blueprint_refs.py search 'ringed site sections'` found zero blueprint nodes.
  `tools/blueprint_refs.py ancestor` returns `None`; the new node retains that
  ancestor and prefixes the item's existing `via` path with this item.

## Repair of H2 at immutable head 6a12d5851d01

The saved packet was inspected first, and its initial `deliver2.py --no-push`
passed at 5db5884b1ba. It nevertheless retained the explicit semantic ownership
fault in the return. This repair adds the definition node and its alias module,
removes `lem-sfb-unbounded-sections-localization`,
`lem-sp-subterminal-derived-image-calculus` and
`lem-weil-pbc-localize-ringed-site-morphism` from the item's `stmt_deps`, and adds
`def-sfb-ringed-site-section-functors`. The localize theorem remains in
`proof_deps`, unchanged. The item module now imports the new definition module
and uses `sectionEvaluation` and `sectionModuleMap` directly. The comparison,
normalization, restriction equation and all hypotheses are definitionally unchanged.
There is no mathematical statement correction and no `statement_change`.

## Second reading by Q05

This is the required self-check by the dispatcher-started worker; the current
brief prohibits starting other agents. Reading the saved and repaired signatures
side by side shows the same small-site universe `u`, commutative ring sheaves
`A,B`, continuous `u`, structural map `a`, finite-limit-preserving set-sheaf
pullback and independently sized three derived localizations. The only changed
terms are the transparent evaluation and underlying-ring-map aliases. The
`∃!` comparison family still quantifies over all `V : D`; natural isomorphisms
still include all derived objects and arrows. Its first conjunct still uses
`HEq` of the actual derived-unit arrows for every K-injective `I`, with the
same composition unit and literal section identity. Its second conjunct is
still the restriction equation for every `v : V' ⟶ V`. No boundedness, flatness,
final object, preservation of K-injectives by direct image or nonzero-ring
hypothesis was introduced. Empty target sites, identity functors, identity and
composite restrictions, zero rings and non-flat coefficient maps remain included.

The new node's `sectionEvaluation` matches evaluation followed by forgetting
scalars on objects and arrows. `modulesGrothendieck` aliases the existing
small-site instance, without asserting a new theorem or registering a new
instance. `pushforwardAdditive` aliases the original componentwise instance.
`sectionModuleMap` is literally the existing image of `a` under forgetting
commutativity. These four aliases neither change objects nor choose maps. Their
module and declaration docstrings identify their new definition-node owner.
The dependency-list fault identified in H2 is repaired; the earlier assertion
that these three theorem nodes were needed for their conclusions was removed.

Validation after repair: both delivered modules compile through scompile.py with
no errors or warnings. The first repair dry run found the newly required
`import_flags` field absent from the new definition node; it is now supplied as
`[]`. The final wrapper dry run checks the complete updated packet.
