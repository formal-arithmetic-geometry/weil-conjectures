## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` states
`AlgebraicGeometry.Scheme.locallyClosedExtensionCoherence`, with `sorry` as its only
postponed proof. It asserts existence of the exact locally closed extensions and all
normalized comparison maps simultaneously, with their laws on modules and on the
ordinary unbounded derived categories. The helper structures are the witnesses of
this single statement, not extra hypotheses. No definition selects module or functor
data from the existence theorem.

I replaced the earlier sandbox attempt in full. It assumed exactness, derived full
faithfulness and the restriction comparison; used arbitrary categories and functors;
omitted the Noetherian hypotheses; asserted a Hom bijection on arbitrary ambient
objects; and omitted the opposite factorization and actual coherence equations.
Those were faults of that sandbox rendering, not faults in the DAG statement.
The earlier second-reading section was removed: the independent reader has yet to
review this replacement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| DAG clause | Lean rendering |
| --- | --- |
| Noetherian scheme: locally Noetherian and quasi-compact | `LocallyClosedCoefficients.scheme`, `.locallyNoetherian : IsLocallyNoetherian scheme`, and `.compact : CompactSpace scheme`. |
| Arbitrary commutative coefficient sheaf on the small pro-etale site | `.ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}`. There is no constant, finite, torsion, constructibility, or flatness hypothesis. |
| Module sheaves and ordinary unbounded derived categories | `proEtaleRingModules`, transparently the published `ringedSiteModules`/Mathlib `SheafOfModules`; `DerivedCategory` with the published standard localization instance. |
| Locally closed immersion | `LocallyClosedCoefficientImmersion.hom` with `.immersion : IsImmersion hom`, Mathlib's closed-then-open notion. |
| All source coefficients are inverse image | `.coefficient : (proEtaleSheafInverseImage hom CommRingCat).obj X.ring ≅ S.ring`. Literal inverse-image coefficients use `Iso.refl`. The isomorphic presentation handles repeated inverse images without changing the coefficients. |
| Exact restriction with pulled-back coefficients | `.pull` abbreviates `proEtaleRingModulePullback` with that coefficient isomorphism; its published exactness instances apply. |
| Closed factor has direct image with induced action | `.push` is `proEtaleRingModuleDirectImage`, whose action is through the ring-adjunction unit followed by the coefficient identification. `closedComparison` identifies closed extension with this functor. |
| Open factor is the sheafified extension presheaf, equivalently the left adjoint to restriction | `openAdjunction a ha : extension a ⊣ a.pull` uses precisely the equivalent characterization explicitly allowed in the DAG. The published slice construction is the direct-sum presheaf followed by `PresheafOfModules.sheafification`; uniqueness of left adjoints identifies it with this witness. This adjunction is imposed only when `a` is open. |
| `a_! = v_! c_*` for a closed-then-open factorization | `closedOpenFactorization E v c hc hv : E.extension (v.comp c) ≅ c.push ⋙ E.extension v`, constructed from `gamma` and `closedComparison`. Functor composition is in Lean order. |
| Exactness | `LocallyClosedExtensionData.additive`, `.finiteLimits` and `.finiteColimits`, asserted as part of the existential conclusion. |
| Canonical `a^* a_! ≅ id` | `restriction a : extension a ⋙ a.pull ≅ 𝟭 _`. On opens `openNormalization` identifies its inverse with the actual open unit. On closed immersions `closedNormalization` identifies it with restriction of the closed comparison followed by the actual normalized closed counit. `Coherent.normalized` fixes it on every mixed composite. |
| Fully faithful termwise functor on unbounded derived categories | `derived a := (E.extension a).mapDerivedCategory`; `DerivedCoherence.full` and `.faithful`. The analogous module assertions are in `Coherent`. No alternative derived functor is quantified. |
| Derived restriction comparison is the same termwise comparison | `DerivedCoherence.restriction` and `.restrictionTermwise`, the latter an equation on the image of every cochain complex under `DerivedCategory.Q`. |
| Restriction Hom bijection for extension images | `DerivedCoherence.homBijection`: for `M N` in the SOURCE derived category, `f ↦ r_M⁻¹ ≫ a.pull.mapDerivedCategory.map f ≫ r_N` is bijective. It does not assert full faithfulness of restriction on the whole ambient category. `Coherent.homBijection` gives the module version. |
| Independence of every closed-then-open factorization | `factorizationComparison` compares `c.push ⋙ E.extension v` and `c'.push ⋙ E.extension v'` for the same ringed composite. It is the composite of the two explicitly defined factorization identifications. `Coherent.normalized` makes restriction the identity, and `homBijection` makes that normalized comparison unique. |
| Opposite open-then-closed factorization | `openClosedFactorization E i j hi hj : E.extension (i.comp j) ≅ E.extension j ⋙ i.push`, again constructed from the same `gamma` and closed comparison. |
| Canonical composition `a_! b_! ≅ (ab)_!`, normalized on `T` | `gamma a b : extension b ⋙ extension a ≅ extension (a.comp b)`, and `Coherent.normalized`, using the actual inverse-image composition `pullComp`. |
| Unital on modules | `Coherent.innerUnit` and `.outerUnit` are explicit equalities of natural isomorphisms, with coefficient-aware identity equalities, whiskering and functor unitors. |
| Associative on modules | `Coherent.associative` equates both paths, inserting the functor associator and the equality of composite coefficient data. |
| Same composition, units and associativity on derived categories | `DerivedCoherence.gamma`, `.identity`, `.innerUnit`, `.outerUnit`, `.associative`. The `.gammaTermwise` and `.identityTermwise` equations require these maps to be the descent of the module maps on EVERY complex. Together with `.restrictionTermwise`, this also descends normalization and factorization comparisons. |

The three intermediate/source schemes are bundled as Noetherian as well. This excludes
no immersion into a Noetherian target: locally Noetherian is inherited by immersions,
and the underlying space of an immersion is a subspace of a Noetherian space, hence
Noetherian and quasi-compact. Conversely every bundle is a scheme satisfying exactly
the node's two Noetherian hypotheses. The theorem quantifies over all these bundles,
so applies to every `X,R` in the node. Identified inverse-image coefficients are a
presentation of the literal inverse images; their canonical identity and composition
maps are retained, including in the coherence equalities. Site object universe is
`u+1`, Hom universe `u`, and module/ring section universe `u+1`; no size equality is
imposed and no finite or countable restriction appears.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`
  reexports the actual `ProEt.topology`; the arbitrary-ring category uses the same site,
  rather than incorrectly specializing its constant-coefficient abbreviation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, reused
  through the landed `proEtaleRingModules` abbreviation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`: the current recorded
  module for `def-weil-proetale-inverse-image` reexports
  `Scheme.proEtaleSheafInverseImage`, `proEtaleModuleInverseImage`, and their actual
  adjunction constructions. Its finite-coefficient helpers are not specialized here.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `.Immersion`:
  `IsClosedImmersion` and `IsImmersion`, including composition instances.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `.sheafificationAdjunction`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`. Its live source was read with
  `scompile.py --source`, since it is absent in the older local upstream checkout.
- Added landed `def-weil-pbc-proetale-operations`: `proEtaleRingModules`,
  `proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModuleAdjunction`, and the published exactness/derived instances.
- Added landed `lem-weil-pbc-profinite-coefficient-inverse-image`:
  `proEtaleRingInverseImageId` and `proEtaleRingInverseImageComp`.
- Added landed `lem-weil-pbc-proetale-derived-pullback-composition`:
  `proEtaleRingCompositeCoefficients`.
- Added landed `def-weil-pbc-strict-tower-operations`:
  `exchangeModuleComposition`, the ordinary module comparison uniquely fixed by
  sectionwise fibre-product pasting; no strict-tower category is used here.

The additional statement dependencies expose existing coefficient presentation and
comparison helpers; there are no new nodes or dependency replacements. I checked
that none of these four added nodes reaches this item through statement/proof edges.
Every helper declaration in the delivery belongs to this item's single coherence
assertion and is listed in `lean.declarations`.

Proof imports include the recorded ringed open-closed theorem, immersion inverse-image
exactness, closed counit, open comparison, ringed module adjunction, site composition,
termwise adjunction, slice sheafification and localization. The module docstring and
the main theorem's docstring give all ten DAG proof steps in their existing order,
including the mixed interchange. The main theorem is the only `sorry`.

Edge cases checked before writing:

- Identity immersion: both pure-open and pure-closed normalization apply; both actual
  unit equalities are present, rather than a vacuous composition witness.
- Empty source/open: the slice extension presheaf is the zero sum on objects with no
  map to that open, hence sheafifies to zero. All module and derived formulas retain
  the zero-category case; no nonempty hypothesis is present.
- Zero ring sheaf: permitted by `CommRingCat`; no nontriviality assumption occurs.
- Pure closed/pure open and nonreduced closed subschemes: use the actual ringed
  functors, with no reducedness or image-containment replacement for a closed map.
- Mixed compositions: both factorization orders and the three-arrow associativity
  equation are included. No false composite adjunction `a_! ⊣ a^*` is assumed.
- Unbounded complexes: descent equations quantify over every `CochainComplex ... ℤ`,
  including the zero complex and complexes unbounded in both directions.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Locally closed immersion extension by zero module
  sheaves exact fully faithful factorization independence associative composition"`:
  eight hits, on scheme immersion lifts/composition; no matching module theorem.
- `msearch.py ... leansearch "locally closed extension by zero exact fully faithful
  associative composition sheaves modules"`: eight hits on locally constant
  condensed sets, module-sheaf categories/forgetful functors and scheme modules;
  none states this theorem.
- `msearch.py ... loogle '"Sheaf", "extensionByZero"'`: zero hits.
- `msearch.py ... grep 'locallyClosedExtension|locally.closed.extension|extensionByZero'
  Mathlib/CategoryTheory`: zero hits.
- `rg` of `locallyClosedExtension|locally.closed.extension|LocallyClosedExtension`
  in upstream `WeilConjectures`, the side `lean/Sheaf`, and the upstream-name index:
  only flat-model and constructible-devissage comments/constructions appeared in the
  side library. They concern constant finite coefficients, not this arbitrary-ring
  coherence theorem. The recorded flat-model construction was opened and checked.
- `grep -rn 'lem-sfb-locally-closed-extension-coherence'` in upstream
  `WeilConjectures`: no hits.
- Existing canonical inverse-image, direct-image, coefficient composition and pure
  open slice-extension constructions were located and reused, rather than copied.

No mathematical dispute or statement correction is needed. The DAG statement is
unchanged. The previous sandbox rendering was repaired, and the statement dependencies
gain only the four landed nodes listed above. The independent second reading remains
for the next worker; this report does not claim that it has occurred.

## Earlier second reading (a previous round; superseded)

I independently read the sandbox node and the complete Lean module against the source,
not just the worker's correspondence table. The source passages opened were
`proetale.tex` lines 4944–4960 (09AA), 5019–5035 (09BM), 5041–5068
(the definition of extension by zero), 5116–5128 (09BN), and 5134–5165 (09AH);
`sites-modules.tex` lines 2057–2110 (03DI) and 2159–2189 (03DJ); and
`schemes.tex` lines 4860–4897 (02V0). In particular, 09BM assumes a retrocompact
open complement and 09AH assumes a quasi-compact open immersion. Every open
immersion into a Noetherian scheme has that property. The sources impose no
finiteness, characteristic, nonzero-ring, or constructibility condition on R.
There is no statement_change and no new definition node or dependency module.

My list of the node's objects, hypotheses and conclusions, with the actual Lean
counterpart and verdict, is:

| Node item | Lean counterpart and verdict |
| --- | --- |
| X is a scheme, locally Noetherian and quasi-compact | `LocallyClosedCoefficients.scheme : Scheme.{u}`, `.locallyNoetherian : IsLocallyNoetherian scheme`, `.compact : CompactSpace scheme`. Exact hypotheses: Mathlib's `IsNoetherian` extends precisely these two classes. |
| R is any commutative ring sheaf on X's small pro-etale site | `.ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}`. Correct: the actual small site is used, and no constant/finite/torsion hypothesis occurs. |
| Modules over R and their ordinary unbounded derived category | `proEtaleRingModules` unfolds to `ringedSiteModules` and Mathlib `SheafOfModules` over the underlying ring sheaf; `DerivedCategory` uses `HasDerivedCategory.standard`. Correct, with neither boundedness nor completion. |
| A locally closed immersion a:S→X | `LocallyClosedCoefficientImmersion.hom` and `.immersion : IsImmersion hom`. Correct: I opened Mathlib's definition and the closed factor `liftCoborder` through the open `coborderRange`. This is the closed-then-open notion. |
| R_S = a inverse image R; all subsequent coefficients likewise | `.coefficient` is an isomorphism from the actual inverse-image ring to `S.ring`. Correct identified presentation of inverse-image coefficients; literal coefficients use `Iso.refl`. Composition uses `proEtaleRingCompositeCoefficients`, not an independent coefficient map. |
| a* is actual exact inverse image with these coefficients | `.pull := proEtaleRingModulePullback ... a.coefficient`. Correct: it is actual module inverse image followed by sheafified change of rings along an isomorphism. Published exactness instances supply the termwise functor; no exactness hypothesis is added. |
| Closed c_* has its induced coefficient action | `.push := proEtaleRingModuleDirectImage ...`; `closedComparison` identifies the extension with it for closed arrows. Correct: the scalar map is the ring adjunction unit followed by direct image of the coefficient identification. |
| Open v_! is sheafified slice extension, equivalently the left adjoint to restriction | `openAdjunction a ha : extension a ⊣ a.pull`. Correct use of the node's explicitly equivalent characterization. 03DI identifies any such left adjoint with the direct-sum-presheaf/sheafification construction, by unit-compatible uniqueness. No adjunction is asserted for mixed immersions. |
| For a=v c, a_! is v_!c_* | `closedOpenFactorization` is the inverse of `gamma v c` followed by whiskered `closedComparison c hc`. Correct order, since Lean functor composition is written source first. This applies to every given closed/open factorization. |
| a_! is exact | `.additive`, `.finiteLimits`, `.finiteColimits` are fields of the existential witness `E`, hence conclusions. Correct abelian exactness, not assumed. |
| Canonical restriction a*a_! ≅ id | `.restriction`; `openNormalization` identifies its inverse with the open unit, `closedNormalization` identifies it with the normalized actual closed counit, and `Coherent.normalized` fixes the composite comparison. Correct normalization on mixed arrows. |
| Termwise derived a_! is fully faithful | `derived E a := (E.extension a).mapDerivedCategory`, with `DerivedCoherence.full` and `.faithful`. Correct functor and both clauses. Module full faithfulness is also recorded in `Coherent`, as in proof step 2. |
| Derived restriction comparison is the descent of the module comparison | `DerivedCoherence.restriction` and `.restrictionTermwise` on every integer-indexed cochain complex. Correct: the displayed equation uses both actual `mapDerivedCategoryFactors` comparisons followed by Q of the module restriction. |
| Restriction gives Hom(a_!M,a_!N) ≃ Hom(M,N), for source derived M,N | `DerivedCoherence.homBijection`, with `M N : DerivedCategory (proEtaleRingModules S.scheme S.ring)`. Correct map: inverse restriction at M, pullback of f, restriction at N; its domain is exactly the extension image. The module analogue is `Coherent.homBijection`. |
| Independence of closed/open factorization, normalized on S | `factorizationComparison` is the composite of the two `closedOpenFactorization` isomorphisms over equality of the composite ringed arrows. Correct: `Coherent.normalized`, open/closed normalization and the Hom bijection give identity on restriction and uniqueness. Coefficient equality is the agreement forced by both factorizations representing the same ringed a, not an added geometric hypothesis. |
| Given a=i u with u open and i closed, the same normalized identification a_!≅i_*u_! | `openClosedFactorization`, using that same `gamma` and `closedComparison i hi`. Correct, including the mixed case. |
| For every b:T→S, normalized composition a_!b_!≅(ab)_! | `.gamma a b` and `Coherent.normalized` with `.pullComp`. Correct: `.pullComp` is the published section-normalized `exchangeModuleComposition`, and the equation compares both restrictions to M on T. |
| Unital and associative on modules | `.identity`, `Coherent.innerUnit`, `.outerUnit`, `.associative`. Correct: both unitors and the functor associator appear, and the equalities of composite ringed arrows include coefficient composition. |
| The same identifications, units and associativity on ordinary unbounded derived categories | `DerivedCoherence.gamma`, `.identity`, `.innerUnit`, `.outerUnit`, `.associative`, with `.gammaTermwise` and `.identityTermwise`. Correct: the equations force the derived comparisons to descend the module maps on every complex. Together with `.restrictionTermwise`, this also descends mixed normalization and the two factorization identifications. |

The theorem `∃ E : LocallyClosedExtensionData.{u}, E.Coherent ∧ Nonempty
E.DerivedCoherence` packages all these conclusions simultaneously. The witness
structures are not assumptions on an input extension. No definition chooses a
functor from this existence theorem. The main theorem is the sole `sorry`; its
docstring gives all ten node proof steps, including localization, shrinking,
intersection of ambient opens, mixed interchange, composition, Hom uniqueness,
and termwise descent. Every helper has a source/blueprint docstring and real data.

I checked the dependency interfaces rather than inferring them from their names.
In particular I opened `RingedSiteModules`, `ProEtaleDerivedCategory`,
`ProEtaleInverseImage` (including the model-site transport), `ProEtaleOperations`,
`ProEtaleOperationsCanonicalAdjunction`, `ProfiniteCoefficientInverseImage`,
`ProEtaleDerivedPullbackComposition`, `StrictTowerOperations` (including
`ExchangeModuleCompositionNormalized` and its unique-existence theorem), and
`SfIntrinsicRealizationTransport`. The finite-coefficient realization helpers in
the last module are not used to specialize R. The source of
`proEtaleRingModuleAdjunction` fixes its transpose by the tensor unit, so the
closed normalization really uses a specified counit. I read the live
`ProEtaleRingedClosedCounit` via `scompile.py --source` because it is absent from
the local side checkout; its theorem is for the actual inverse-image/direct-image
adjunction with arbitrary ring sheaves. Change of rings by `.coefficient` transports
that statement. I also read the actual `extensionByZeroPresheaf` through the same
source wrapper: its sections are the direct sum over maps into the open, and its
restriction maps and scalar action are those in 03DI. The four added statement
dependencies already carry these canonical comparisons; none is redefined here.

Edge cases checked: S, V or X empty; zero modules and zero complexes; zero ring
sheaf; pure open and pure closed arrows; identity arrows; nonreduced closed
subschemes; arbitrary characteristic. No Nonempty, Nontrivial, finite-index or
boundedness hypothesis occurs. The Noetherian bundles for intermediate schemes
exclude no factorization: an immersion into a Noetherian scheme has a Noetherian
underlying subspace and is locally of finite type, hence locally Noetherian and
quasi-compact. Cochain indices are all of ℤ, including degree zero and complexes
unbounded in either direction. The small site retains objects in u+1 and morphisms
in u; ring and module values are in u+1. No equality between site universes is
introduced. There is no independent index universe or characteristic parameter to
be accidentally restricted. All variables are explicitly bound and the only
universe parameter is declared `u`.

Independent H4 searches (different wording from the worker's):

- LeanFinder through `msearch.py`: “For sheaves of modules on a ringed pro-etale
  topos, shriek along an immersion is exact and the composition comparison is
  associative”. Eight hits, including `SheafOfModules.pushforwardComp`,
  `pullbackComp`, `pushforward_assoc`, and `pullback_assoc`. I opened the
  composition declarations in Mathlib: they concern ordinary site-module
  pushforward/pullback and their adjunctions, not mixed locally closed extension.
- Loogle through `msearch.py`: `"Sheaf", "immersion"`. Twelve hits, all on
  ordinary open immersions of presheafed/sheafed/locally ringed spaces; no match.
- LeanSearch through `msearch.py`: “Restriction to the support of extension by
  zero along a locally closed immersion gives a bijection on derived morphisms,
  compatible with composition”. Eight hits: Finsupp support equivalences and
  Zariski scheme-module restriction infrastructure, not the present theorem.
- `rg` for `locallyClosedExtension`, locally-closed/extension combinations,
  `lowerShriek`, and `extensionByZero` in upstream WeilConjectures, side Sheaf,
  and Mathlib's module-sheaf/site directories. I opened
  `ProEtaleExtensionByZero` and `FlatModelGeneration`: the former is pure open
  extension for a finite constant ring; the latter's `flatModelProEtaleExtension`
  also requires finite constant coefficients and contains no arbitrary-ring
  factorization/composition theorem. The numerous Zariski stalk statements use
  the scheme structure sheaf. None is an existing exact match for this item.
  The upstream-name index has no occurrence of the new declaration names.

No mathematical mismatch was found in the replacement, so I preserved the Lean
and the node statement. The changes made by this second reading are this independent
source/interface/clause audit and its validation record below; the worker report
above remains intact.

Validation: the prescribed `scompile.py Q88
lem-sfb-locally-closed-extension-coherence
lean/Sheaf/AlgebraicGeometry/LocallyClosedExtensionCoherence.lean` completed with
exit 0 after its automatic confirmation against current server sources. The
module compiled in 12.5 seconds at nice 19, two threads, with the 60-second limit;
there were no errors or warnings. The initial local-overlay object-file miss was
resolved by the wrapper's server confirmation and required no source edit.
Mechanical inspection also found zero lines over 100 characters, exactly one
`sorry` token (the named main theorem), and exact verbatim agreement of the node's
`lean.statement` with the file's theorem signature.

## Second reading by Q88

I read the current node and all 357 lines of the current module independently of the
superseded reading. No released repair note exists for this item. The source passages
checked were proetale.tex 4944–4960 (09AA), 5019–5035 (09BM), 5041–5068
(extension by zero), 5116–5128 (09BN), 5134–5165 (09AH); sites-modules.tex
2057–2110 (03DI), 2159–2189 (03DJ); and schemes.tex 4860–4897 (02V0).
09BM requires a retrocompact open complement and 09AH a quasi-compact open
immersion. Noetherianity supplies both, including on all intermediate subschemes.
03DI and 03DJ are for arbitrary ringed sites, so using a nonconstant ring sheaf
introduces no missing coefficient hypothesis.

The following is my object/hypothesis/conclusion list, with its actual Lean rendering.
Every row passes; the functors and laws below are existential conclusions, not input
hypotheses.

| Node item | Lean rendering and verdict |
| --- | --- |
| A scheme X, locally Noetherian and quasi-compact | `LocallyClosedCoefficients.scheme`, `.locallyNoetherian`, `.compact`. These are exactly the two fields extended by Mathlib `IsNoetherian`. Pass. |
| Any commutative ring sheaf R on the small pro-etale site | `.ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}`. No finite, constant, torsion, nonzero or constructibility restriction. Pass. |
| Module sheaves over R | `proEtaleRingModules` unfolds to the recorded `ringedSiteModules` and Mathlib `SheafOfModules` over the underlying ring sheaf. Pass. |
| Ordinary unbounded derived categories | `DerivedCategory` with the published `HasDerivedCategory.standard` instance and integer-indexed `CochainComplex`. Pass. |
| Locally closed a:S→X | `LocallyClosedCoefficientImmersion.hom` and `.immersion : IsImmersion hom`. I read Mathlib's definition and its `liftCoborder` closed-then-open factorization. Pass. |
| R_S is inverse image, also on intermediate subschemes | `.coefficient` identifies actual `proEtaleSheafInverseImage` of X.ring with S.ring. Literal inverse images are obtained with `Iso.refl`; composition uses `proEtaleRingCompositeCoefficients`. This allows identified presentations without arbitrary coefficient maps. Pass. |
| a* is exact inverse image with these coefficients | `.pull` is the published `proEtaleRingModulePullback`, actual module inverse image followed by sheafified change of rings along the coefficient isomorphism. Its exactness instances add no hypothesis. Pass. |
| c_* is direct image with induced action | `.push` is `proEtaleRingModuleDirectImage`, using the coefficient adjunction unit. `closedComparison` identifies extension with this actual functor on closed arrows. Pass. |
| Open v_! is sheafified slice extension, equivalently left adjoint to restriction | `openAdjunction` gives exactly the equivalent characterization permitted by the node. 03DI identifies this left adjoint with the existing direct-sum-presheaf/sheafification construction. No mixed-immersion adjunction is asserted. Pass. |
| For each closed-then-open factorization, a_! = v_!c_* | `closedOpenFactorization E v c hc hv` has target `c.push ⋙ E.extension v`; it uses `gamma` and `closedComparison`. Lean writes functors in source-first order. Pass. |
| a_! is exact | `additive`, `finiteLimits`, `finiteColimits` in `LocallyClosedExtensionData`, existentially asserted. Pass. |
| Canonical restriction a*a_! ≅ id | `restriction`; `openNormalization` fixes it by the open unit, `closedNormalization` by the specified actual closed counit, and `Coherent.normalized` fixes it on mixed compositions through actual `pullComp`. Pass. |
| Termwise derived extension is fully faithful | `derived := (E.extension a).mapDerivedCategory`; `DerivedCoherence.full` and `.faithful`. Module full faithfulness is also in `Coherent`, as in the node proof. Pass. |
| Derived restriction is the descent of module restriction | `DerivedCoherence.restrictionTermwise` prescribes the component on `DerivedCategory.Q.obj K` for every complex K using `mapDerivedCategoryFactors` and Q of module restriction. Pass. |
| Restriction gives the displayed Hom bijection | `DerivedCoherence.homBijection` quantifies over source derived M,N; its map is restriction conjugated by r_M inverse and r_N. It is only on Hom between extension images. Pass. |
| Independence of any two closed/open factorizations, normalized on S | `factorizationComparison` composes the two `closedOpenFactorization` maps over equality of their ringed composites. `Coherent.normalized` supplies normalization and `.homBijection` supplies uniqueness. The coefficient equality means that both represent the same ringed arrow. Pass. |
| Given a=i u with u open and i closed, a_!≅i_*u_! with the same normalization | `openClosedFactorization`, from the same `gamma` and actual `closedComparison i hi`. The mixed case is included. Pass. |
| Every b:T→S has canonical a_!b_!≅(ab)_! | `gamma a b : extension b ⋙ extension a ≅ extension (a.comp b)`. Pass. |
| Composition comparison restricts to the identity on T | `Coherent.normalized` explicitly compares the composite restriction with successive restrictions through section-normalized `pullComp`. Pass. |
| Module unit and associativity laws | `Coherent.innerUnit`, `.outerUnit`, `.associative` equate actual natural isomorphisms, with both functor unitors, associator, and equalities of composite ringed arrows. Pass. |
| Same comparisons and laws on unbounded derived categories | `DerivedCoherence.gamma`, `.identity`, `.innerUnit`, `.outerUnit`, `.associative`; `.gammaTermwise` and `.identityTermwise` force descent of the module comparisons on every complex. Together with `.restrictionTermwise` this also descends factorization comparisons and normalization. Pass. |

The final signature is `∃ E : LocallyClosedExtensionData.{u}, E.Coherent ∧
Nonempty E.DerivedCoherence`: one system of extensions and comparisons with all
these conclusions simultaneously. No definition chooses functor data from that
existence theorem. The extra Noetherian fields on source/intermediate bundles exclude
no immersion into Noetherian X: the underlying embedding gives a Noetherian
subspace, hence quasi-compact, and immersions are locally of finite type, hence their
sources are locally Noetherian. All coefficient identifications retain their actual
identity and composition maps.

I opened the signatures and constructions in the recorded dependency modules:
`RingedSiteModules`, `ProEtaleDerivedCategory`, `ProEtaleInverseImage`,
`SfIntrinsicRealizationTransport`, `ProEtaleIntrinsicFiniteOperations`,
`ProEtaleOperations`, `ProEtaleOperationsCanonicalAdjunction`,
`ProfiniteCoefficientInverseImage`, `ProEtaleDerivedPullbackComposition`,
`ProEtaleCanonicalPullbackComposition`, and `StrictTowerOperations`, as well as
Mathlib's Noetherian, immersion, module sheafification and derived-category definitions.
The currently recorded inverse-image/operations modules publicly retain the arbitrary-ring
interfaces; their finite-coefficient additions impose no restriction on this theorem.
`exchangeModuleComposition` is selected from its uniquely characterized sectionwise
fibre-product pasting comparison; it is not an arbitrary isomorphism. The actual
`proEtaleRingModuleAdjunction` is fixed by its tensor-unit Hom normalization.
I read live `ProEtaleRingedClosedCounit` and `ExtensionByZeroPresheaf` with
`scompile.py --source`: the former concerns actual arbitrary-ring inverse/direct image,
and the latter has the precise direct sum over arrows, restrictions, and scalar action
of 03DI. Transport along `.coefficient` identifies the literal closed-counit case.
There are no new nodes or dependency replacement modules in this delivery, and no
`statement_change`; H12/H13 and the corrected-statement citer audit therefore add no
unreviewed material.

Edge cases: empty X, S, V and opens are allowed; zero rings, modules and complexes are
allowed; identities, pure opens, pure closed and nonreduced closed subschemes are
included. No Nonempty/Nontrivial or characteristic hypothesis appears. The empty
summand set in slice extension gives zero, as the existing presheaf states. All degrees
in ℤ, in particular zero and complexes unbounded in either direction, are included.
There is no extra index parameter. Small-site objects have universe u+1, morphisms u,
and section/module values u+1; no equality of distinct site universes is imposed.
`universe u` is explicit and `autoImplicit false` prevents hidden variables.

My independent searches used different queries from the worker:

- LeanFinder via msearch: “Extension with locally closed support for arbitrary ring
  sheaves has factorization independent and coherent composition isomorphisms”. Eight
  hits concern presieve extension, sheaf images and locally surjective factorization;
  none is this mixed-immersion theorem.
- Loogle via msearch: `"SheafOfModules", "FullyFaithful"`. Three hits are fully
  faithful forgetful functors to presheaves, not extension along an immersion.
- LeanSearch via msearch: “Shriek for a locally closed immersion of schemes is exact
  and fully faithful on unbounded derived categories of arbitrary ring sheaves”. Eight
  hits concern scheme immersion definitions, Zariski pushforward, stalk surjectivity and
  images; none has this statement.
- `rg` on upstream WeilConjectures, project Sheaf and Mathlib, with
  `locallyClosedExtension`, `LocallyClosedExtension`, `lowerShriek`,
  `extensionByZero`, `extension_by_zero`, and both orders of locally-closed/extension.
  I also searched `dag/lean_names_upstream.json`. I opened the relevant side-library
  `ProEtaleExtensionByZero`, `ProEtaleExtensionZero`, and
  `SixFunctors/FlatModelGeneration`: these are pure-open finite constant coefficients,
  or the finite-constant locally closed construction; neither gives arbitrary-ring
  factorization independence and coherent composition. The Zariski declarations use
  structure-sheaf modules, and existing generic presheaf extension is reused here.
  No exact existing match or collision for the new declarations was found.

No mismatch was found in the current replacement, so I changed neither the Lean nor
the node. My change is this fresh independent source, interface, clause and edge-case
review. The worker report and superseded historical reading remain in place. All helper
definitions have real data; the main named theorem is the only sorry. Its docstring
contains the ten node proof steps in order, including mixed interchange and unbounded
descent. Declaration docstrings carry source places and the item blueprint id.

Validation: the required `scompile.py Q88 lem-sfb-locally-closed-extension-coherence
lean/Sheaf/AlgebraicGeometry/LocallyClosedExtensionCoherence.lean` exited 0, compiling
the sandbox in 13.1 seconds and library module in 14.7 seconds, with no errors or
warnings. The compilation retained the default 60-second per-file limit. Mechanical
signature/line/sorry checks and the required delivery dry run are recorded below.

Mechanical validation passed: the node's `lean.statement` equals the theorem signature
verbatim, no Lean line exceeds 100 characters, and exactly one sorry occurs. The
prescribed `deliver2.py Q88 lem-sfb-locally-closed-extension-coherence --no-push`
printed `OK (dry run): commit 660514afae passes the preflight and compiles; nothing
pushed`. Its staged paths were only this item's Lean module, node, and report.
