## Worker report

This delivery states `CategoryTheory.Functor.levelwiseKInjectiveTowerImage` in
`Sheaf.CategoryTheory.LevelwiseKInjectiveTowerImage`. Its sole theorem has proof `sorry`.
The two real-data helpers `Functor.onStrictTowers` and
`Functor.strictTowerDerivedComparison` are recorded in `lean.declarations` and belong to
this node's own constructions: the former is Mathlib whiskering, the latter is exactly
its recorded right-derived unit transported from homotopy classes to complexes.
No new node, dependency repair or statement correction is needed.

The previous interrupted sandbox contained only a preliminary module, without a node
copy or report. No delivery branch was present when resuming. The current shared node
has the Q131 stage-1 six-step split; its statement is used verbatim here. The saved draft
was replaced because it defined tower K-injectivity as levelwise K-injectivity and
claimed an actual chain isomorphism where only a quasi-isomorphism was warranted.

Hypothesis and clause correspondence:

- The sites C and D are `SiteC : Type uC`, `SiteD : Type uD` with categories of independent
  morphism universes vC and vD, and topologies JC and JD. The module/ring universes
  `max uC vC r` and `max uD vD s` contain their respective sites, including different
  object and morphism sizes. No equality between site universes is imposed. The two
  HasSheafify and WEqualsLocallyBijective assumptions provide the canonical Mathlib
  abelian module categories on these small sites. These are available for the chosen
  size convention; they do not impose a geometric condition on the sites.
- The commutative ring sheaves are R and S in RingCat, with sectionwise commutativity
  `_hRcomm` and `_hScomm`. This is exactly forgetting sheaves of commutative rings to
  sheaves of rings, retaining their commutativity. The module categories are the
  dependency's `ringedSiteModules` with both module and coefficient universes explicit.
- G is precisely a functor between those two categories with `[G.Additive]`; neither
  left exactness nor exactness is assumed.
- Tow(A) and Tow(B) are the existing Mathlib functor categories `ℕᵒᵖ ⥤ A` and
  `ℕᵒᵖ ⥤ B`. Natural index n denotes positive index n+1, an order isomorphism preserving
  all transitions, including the first positive level. Abelian structure and exactness
  are Mathlib's levelwise ones, not an additional chosen structure. `onStrictTowers`
  is `(Functor.whiskeringRight ℕᵒᵖ A B).obj G`, so it maps strict transitions too.
- The complexes are unbounded integer-indexed CochainComplex, with separately chosen
  derived morphism universes wA and wB. HasDerivedCategory is the dependency's size
  convention for the localization, not a boundedness assumption.
- The node stipulates a total right derived functor obtained by K-injective tower
  resolutions. The datum h is exactly its arbitrary-quasi-isomorphism resolution
  construction, required by the recorded
  `onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h`. It assumes no monicity.
  It is not an extra property of G: enough K-injectives holds for these small-site
  module tower categories, as used in the node's own stage-1 review. The comparison
  uses that fixed recorded derived functor and its unit, not an arbitrary map or an
  arbitrary naturally isomorphic functor.
- X is a complex of strict module towers; hX is
  `∀ n : ℕᵒᵖ, CochainComplex.IsKInjective (X.asFunctor.obj n)`. This is the dependency's
  ordinary-complex K-injectivity, namely null-homotopy of every map from an acyclic.
- Every K-injective tower resolution is quantified as Q, q with `Q.IsKInjective` and
  `QuasiIso q`. Here Q.IsKInjective is in the tower category, and is NOT defined to
  mean the desired conclusion about its evaluations.
- The first conclusion is `∀ n, CochainComplex.IsKInjective (Q.asFunctor.obj n)`.
  The second is `∀ n, QuasiIso` of G applied to the evaluated chain map q_n.
  The third is QuasiIso of the actual strict image map `onStrictTowers(q)`, expressing
  the same levelwise quasi-isomorphism in the abelian functor category. It does not
  claim an isomorphism of chain complexes.
- The strict transition clause quantifies over every arrow t:n→m in the opposite
  poset and states G(t_X) followed by G(q_m) equals G(q_n) followed by G(t_Q).
  This is the exact strict square in proof step 6, including composites of transitions.
- The canonical derived comparison clause is
  `IsIso (G.strictTowerDerivedComparison h X)`. The definition is the inverse target
  quotient comparison, then the existing derived unit, then the derived functor of
  the source quotient comparison. Thus its source is the actual localized levelwise
  image of X and its target is the recorded derived image of X.
- Naturality quantifies over every levelwise K-injective Y and every strict chain map
  a:X→Y, and gives `Q(Ta) ≫ comparison Y = comparison X ≫ RT(Qa)`. The theorem applies
  to each Y as well, so these are natural isomorphisms on precisely the stated class.
- For every K-injective complex J and endomorphism e, the final clause assumes X's
  evaluated tower equals `Functor.ofOpSequence (X := fun _ ↦ J) (fun _ ↦ e)` and states
  its actual image equals the corresponding `ofOpSequence` with term GJ and arrow Ge.
  Combined with the preceding IsIso comparison this says the derived image is
  represented by that actual strict tower, retaining its chosen transition e.

Dependency declarations read and used:

- def-weil-size-convention: its metatheoretic lean record has no declaration; explicit
  universes and HasDerivedCategory implement its convention.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the full transparent abbreviation to Mathlib SheafOfModules, including module sizes.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.quotientCompQhIso`:
  the exact unbounded localization and complex/homotopy comparison.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
  `CochainComplex.IsKInjective`: full class signature and docstring read. This is the
  recorded mathlib_match of def-pur-kinjective-complex; it needs no lean repair.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`,
  `CategoryTheory.Functor.Additive`, including evaluation and whiskering instances:
  the recorded mathlib_match of def-weil-pbc-additive-functor.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its Unit, universal property,
  uniqueness, Unit_isIso and ObjIso: full declarations and docstrings read. Its
  resolution hypothesis is used as written, not replaced by monomorphic resolutions.
- Proof dependency `lem-weil-tower-evaluation-kinjective` is imported privately from
  `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`, declaration
  `CategoryTheory.tower_evaluation_isKInjective`. Its current source was read through
  `scompile.py --source` because it is absent from the old source checkout.
- Proof dependency `lem-weil-tower-category-levelwise-abelian` is the recorded Mathlib
  instance `CategoryTheory.Abelian.functorCategoryAbelian`, with evaluation limit and
  colimit preservation. The signatures were read in their Mathlib source.
- Proof dependency `lem-weil-pbc-kinjective-hom-derived` is the recorded Mathlib
  `CochainComplex.IsKInjective.Qh_map_bijective` and `quasiIso_iff` in
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, imported transitively through
  the right-derived dependency. Full signatures and docstrings were read.

Source checked: Stacks sites-cohomology.tex Tag 0941 at the exact-left-adjoint evaluation
paragraph; derived.tex Tag 070I at the Hom bijections, 070Y at computation on K-injectives,
and 070K at the enough-K-injectives construction. The six proof steps from the current
node are reproduced in the theorem docstring, including the independent levelwise
homotopy inverses, additive homotopy equations and strict transition square.

Edge cases checked before writing: the empty site and zero complexes are allowed;
G=0 gives a zero image and valid comparison; G=id gives the identity derived comparison;
G=-⊗Z/2 is allowed despite not being left exact; no injectivity of the individual terms
of Q or epimorphic transitions is imposed. The zero transition e=0 and identity e are
included. Natural index 0 is the first positive level, not a discarded boundary case.
Arbitrary negative cochain degrees remain present. Distinct object, morphism, ring,
module and derived-category universes are retained as described above. No false or
untypable statement was found; there is no STATEMENT-DISPUTED flag.

Searches made using msearch.py (the exact service outputs are in searches.jsonl):

- LeanFinder: "A levelwise K-injective inverse tower computes the total right derived
  functor of an additive functor applied levelwise" returned 8 hits: rightDerived,
  mapDerivedCategoryFactorsh, toRightDerivedZero, mapDerivedCategoryFactors,
  isoRightDerivedObj, rightDerived_app_eq, toRightDerivedZero_eq and
  isoRightDerivedToHomotopyCategoryObj. These concern ordinary injective resolutions
  or exact functors; none states this unbounded strict-tower theorem.
- Loogle: "CochainComplex.IsKInjective, CategoryTheory.Functor.IsRightDerivedFunctor"
  returned zero hits.
- Mathlib grep: "levelwise.*[Kk][Ii]njective|[Kk][Ii]njective.*[Tt]ower" returned zero hits.
- LeanSearch: "A tower of K-injective complexes computes the right derived functor of
  an additive functor applied levelwise" returned 8 ordinary rightDerived and injective
  resolution hits, no exact match.
- rg on WeilConjectures and lean/Sheaf for PositiveTower, IsKInjectiveTower,
  levelwiseKInjective and inverseSystem found no declaration for the item. The direct
  node-id search in WeilConjectures returned no match. Follow-up exact name searches
  for onStrictTowers, strictTowerDerivedComparison and levelwiseKInjectiveTowerImage
  in Mathlib, WeilConjectures and lean/Sheaf found no collision.
- Mathlib source search found the existing asFunctor,
  complexOfFunctorsToFunctorToComplex, quasiIso_iff_evaluation and ofOpSequence;
  these are used rather than copied. Tower evaluation and general total-derived
  statements are constituents, not an existing theorem stating this entire node.

Validation: scompile.py compiled the final module both as sandbox and as its library
module, in 2.7 and 2.8 seconds respectively, with no warnings or errors. Earlier compiler
feedback about namespace field notation and explicit constant-sequence object families
was repaired before that clean compile. The only postponed proof is the named theorem
for this DAG node; both helpers have complete data, no sorry.

## Second reading by Q128

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
