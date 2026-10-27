## Worker report

Item: lem-sfb-ringed-site-connective-hypercohomology. The module
`Sheaf.CategoryTheory.RingedSiteConnectiveHypercohomology` states the node in three
named theorems in `CategoryTheory.RingedSiteConnective`. All three proofs are
`sorry`; each has the relevant complete natural-language proof from the node in
its docstring. The remaining declarations are transparent aliases, actual canonical
maps, and predicates spelling out normalization equations for this same notion.
They introduce no independent mathematical notion and contain no postponed data.
The node's statement, dependencies, and proof are unchanged.

Clause and hypothesis correspondence:

* A site small in the coefficient universe is `{C : Type u} [SmallCategory C]`
  with `{J : GrothendieckTopology C}`. The coefficient is
  `R : Sheaf J CommRingCat.{u}`. There is no terminal-object assumption on C.
* `modules R` abbreviates the recorded `ringedSiteModules` after forgetting only
  commutativity of the ring sheaf. The binders
  `[HasDerivedCategory.{w} (modules R)]` choose the localization of the unbounded
  category of integer-indexed cochain complexes. The localization universe w is
  arbitrary; it is not identified with u.
* `connective R E` is exactly
  `∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (modules R) i).obj E)`.
  It is the object's membership predicate in a full subcategory, so no morphisms
  between connective objects are excluded.
* `sections R` is the recorded additive Hom functor from `SheafOfModules.unit`.
  `derivedSections R` is its total `rightDerivedFunctor`, with the same canonical
  Grothendieck instance and standard abelian-group localization as the recorded
  `ringedSiteZerothHypercohomologyOfUniverses`. `hypercohomology R i` is its ith
  cohomology. `derivedOnConnective` directly uses that recorded degree-zero
  declaration; it does not introduce another definition of hypercohomology.
* In `connective_hypercohomology`, `e : ordinaryOnConnective R ≅
  derivedOnConnective R` is the claimed natural isomorphism. The arrow t has
  source `singleFunctor 0 (H0 E)` and target E; its H0 is the identity after the
  canonical `singleFunctorCompHomologyFunctorIso`. Its uniqueness states the
  canonical connective truncation characterization. The equation for `e.hom.app E`
  is `sheafComparison` followed by `hypercohomology.map t`, fixing the requested
  direction and canonical map, including its sign.
* The next conjunct quantifies all connective E and all integers i<0 and asserts
  `IsZero ((hypercohomology R i).obj E)`, exactly the negative-vanishing clause.
* The final conjunct quantifies all cochain complexes P with `IsZero (P.X n)`
  for every n<0. It supplies the connectivity of QP and an isomorphism k from
  `kernel ((sections R).map (P.d 0 1))` to the recorded H0 hypercohomology of QP.
  The first equation normalizes k on every actual section cycle using
  `cycleToSheaf`. The second equation identifies that same class with the actual
  representative-to-derived comparison `complexComparison`. Thus the kernel
  formula is the asserted identification, rather than an unspecified group iso.
  It makes no claim that ordinary sections compute higher hypercohomology.
* `connective_hypercohomology_localization` uses `J.over U`, `R.over U`, and the
  actual exact `SheafOfModules.overFunctor` descended by
  `ringedDerivedRestrictionGeneral`. Its slice HasDerivedCategory binders only
  select the localizations, and impose no geometric assumption on the site.
  The family e compares evaluation of H0 with derived evaluation; the first
  equation normalizes it by the same truncation arrow. Its explicit square for
  every `a : V ⟶ U` uses `evaluation.map a.op` and
  `evaluationRestriction R a 0`, the total derivation of the actual restriction
  natural transformation. The equations include identities, compositions, and
  hence repeated localization.
* The localization theorem separately asserts negative derived-evaluation
  vanishing, connectivity after exact restriction, and negative hypercohomology
  vanishing on each slice. Its b compares derived evaluation with the recorded
  slice hypercohomology on the connective subcategory. For every E the slice
  comparison eU has the same truncation normalization. The iso sU is fixed by
  evaluation at `id_U` and the element 1, using the actual exact
  `restrictionHomology` comparison. The final square identifies b with the
  canonical slice comparison. Consequently the e-family is precisely the
  asserted slice identification, with its restriction maps; it is not a family
  of arbitrary isomorphisms. Applying the global theorem to each slice also
  supplies its nonnegative-complex kernel formula.
* `connective_hypercohomology_pullback` quantifies the dependency's full
  `RingedToposMorphism` f, with no presented-site-map requirement. Here A is the
  source ring and B the target ring. Its ordinary module pullback F is specified
  by `adj : F ⊣ f.modules`; being a left adjoint to this fixed induced direct
  image determines the usual tensor pullback up to the canonical adjunction iso.
  F, additivity, and left exactness of f.modules are conclusions supplied by the
  theorem, not extra hypotheses on f.
* L and eps are the total left derived functor and its comparison on the
  homotopy category: `L.IsLeftDerivedFunctor eps (HomotopyCategory.quasiIso ...)`.
  eps is required to be invertible on flat K-flat representatives, using exactly
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `SheafOfModules.IsFlat`. This specifies K-flat computation without choosing
  arbitrary derived maps. `IsPullbackUnitNormalized` spells out the derived
  adjunction unit equation with the ordinary adjunction unit and the canonical
  `rightDerivedFunctorUnit`. Thus ad is the compatible derived adjunction.
* t identifies sections of the direct image with sections on the source.
  `IsOrdinarySectionsComparisonNormalized` fixes it on every global element
  using `f.adj.homEquiv` and `f.underlying`, so the ordinary comparison cannot
  be replaced by an arbitrary automorphism of sections. `globalElement` is the
  explicit sheaf map from the terminal sheaf obtained by evaluation at 1.
* kappa is an isomorphism of the unbounded derived-section functors themselves,
  not just their cohomology. `IsSectionsCompositionNormalized` fixes it by the
  equation for the two actual derived units on every representative P and the
  chain map induced by t. Its H0 is used in the last equation, in accordance
  with the project's derived-isomorphism convention.
* eA and eB are natural comparisons and `IsCanonicalComparison` normalizes them
  by every truncation arrow inducing the identity in H0. The natural iso d is
  `H0 Rf_*T ≅ f_*H0 T` on connective T. The theorem asserts Rf_*T connective;
  `IsDirectImageCanonicalComparison` fixes d.inv by Rf_* applied to the same
  canonical truncation arrow and by the existing sheaf-in-degree-zero
  right-derived comparison.
* The final equation quantifies E with `hE : connective B E` and precisely the
  extra condition `hLE : connective A (L.obj E)`. Its left side is eB followed by
  H0 of the actual derived adjunction unit and H0 of kappa. Its right side is
  sections of H0 of that unit, followed by d, t, and eA. This is the requested
  equality between hypercohomological pullback and the map on sections of H0.
* All complexes are indexed by ℤ, and there is no upper bound anywhere. The
  three natural isomorphisms use full subcategories, so naturality is in all
  derived morphisms in E, not just chosen chain maps.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the site is encoded by its
  associated `GrothendieckTopology`. `def-weil-size-convention` is a convention
  node, not an extra Lean predicate.
* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the existing `SheafOfModules` alias.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, `Qh`.
* `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`.
* `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, with `J.over` and `Sheaf.over` for the slice.
* `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, especially its geometric adjunction,
  module direct image, underlying comparison, and additivity instance.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; the coefficient and site
  universe specialization is the one required by the item.
* Actual canonical helper APIs are reused from
  `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral` (exact restriction),
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
  (`mapDerivedCategoryHomologyFunctorIso`),
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero`
  (`singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso`),
  `...RightDerivedFunctor.ShortExactPullback` (`rightDerivedFunctorUnitQ`),
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
  (`Adjunction.mapHomotopyCategory`), and
  `Sheaf.Algebra.Homology.LocallyFreeDerivedHom` (`locallyFreeDerivedComparison`).
  Proof-dependency modules, including Grothendieckness, injective resolutions,
  standard t-structure, K-injectivity, the module adjunction, and the derived
  composition theorem, are imported for stage 3.

Sources checked: local Stacks sites-cohomology.tex Tags 071J, 07A5, 07A6,
0D6E; quot.tex Tag 08JX and its opening proof sentence. The current blueprint
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
and `sk-thm-sf-ctf-stability-direct-images.proof.md` locate the supporting input;
this item is not the unit's own statement.

Edge cases checked mathematically before delivery: the zero complex (all groups
zero); a sheaf placed in degree zero (the canonical R0 comparison); a complex
concentrated in positive degree (H0 and negative groups zero); a nonnegative
complex with nonzero positive cohomology (only its zero-cycle kernel is used);
the empty site (the section Hom group and slice assertions still make sense);
identity and composite restrictions; identity ringed-topos morphism (the unit
normalizations force identity pullback); a non-flat ring morphism with nonzero
negative Tor (the explicit hLE condition excludes precisely that case). No
nonemptiness, terminal object, flatness of f, or upper cohomological bound was
added.

Searches for an existing statement (all returned no exact full-node match):

* msearch.py leanfinder: "For a connective complex on a ringed site
  zeroth hypercohomology equals sections of zeroth cohomology naturally under
  restrictions and pullback"; eight hits, mainly ordinary sheaf/group cohomology.
* msearch.py loogle: `DerivedCategory.homologyFunctor, Functor.rightDerivedFunctor`;
  zero hits, the latter name was unknown to that index.
* msearch.py grep: `connective|rightDerivedZeroIsoSelf|homology.*[Zz]ero` in
  CategoryTheory; ordinary right-derived-zero results, no connective unbounded
  statement with slice/pullback normalization.
* msearch.py leansearch: "connective complex zeroth derived global sections
  cohomology sheaf"; eight hits, including cochain definitions and sheaf Γ,
  no full-node match. Tool outputs are retained by the search wrapper in the
  sandbox searches.jsonl.
* rg in Mathlib, WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json
  for connective/hypercohomology and the proposed declaration names; no exact
  statement or conflicting names. Search for the item's id in WeilConjectures
  found no declaration. `lem-trf-connective-hypercohomology-sheaf` is only the
  ringed-space/open-site specialization and has no pullback clause, so it does
  not already state this node.

No statement dispute, correction, new node, or dependency re-record is needed.
Compilation uses scompile.py only. The original large pullback signature reached
Lean's default heartbeat budget; factoring its normalization equations into
transparent named predicates fixed that, without raising any time or heartbeat
limit or weakening any equation. Successful compiles check both sandbox and
final module names in approximately 20–23 seconds per file.

## Second reading by Q25

The dispatcher explicitly prohibits starting another agent, so this is a second
pass by this worker with the original node, sources, and full Lean file open;
it is not claimed to be an independent second worker's review. The maintainer's
independent review remains the next stage of delivery.

I checked every hypothesis and clause against the mapping above, rechecked
arrow directions (especially f.modules from source A to target B), and checked
that no supplied iso or adjunction is left unnormalized. The first draft supplied
a slice comparison in every degree; the final statement restricts b to the
connective degree-zero comparison needed by the node and explicitly states
negative slice vanishing. I corrected a proof-docstring typo `I[-1]=0` to say
that the degree -1 term vanishes. I extracted four normalization predicates
and renamed Prop-valued helpers with `Is` for the project's naming convention.
No mathematical statement was changed. All actual constructions remain definitions
with real data, and exactly three named clause theorems contain `sorry`.
