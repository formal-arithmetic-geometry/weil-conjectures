## Worker report

The new module `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison` states the
entire node, with two postponed theorems: `AlgebraicGeometry.ProEtale.boundedBelowComparison`
and `AlgebraicGeometry.ProEtale.affineBoundedBelowComparison`. The five helper definitions
construct the canonical maps and the section-complex presentation of the affine formula.
They contain no postponed data or proofs. No other DAG node is stated or changed.

The initial read-only checkout had a stale, unsplit version of the item, with empty
`stmt_deps`. The first dry run detected that the current delivery base contains the
reviewed split and its coefficient/size clarification. I refreshed the sandbox node
from that current source snapshot and retained only my `lean` record as a delta. The
mathematical clauses are unchanged. The current statement dependencies are
`def-weil-pbc-site-comparison-morphism`, `def-weil-abstract-derived-category`,
`def-weil-pbc-bounded-derived-subcategories`, `lem-weil-pbc-right-derived-plus-injective`,
`sk-def-pe-morphisms`, and `def-weil-sheaf-of-modules-category`. I read each statement,
Lean record or Mathlib match, and its declaration signature/docstring. I read the item's
statement, source, proof, proof dependencies,
and all four blueprint-listed declaration names. The blueprint source is the current
`main-20261015` unit, not the older snapshot. I also read Stacks 099V and 099W in
`proetale.tex` and 03Q6 in `etale-cohomology.tex`. The source statement is mathematically
consistent; no statement correction or dispute is needed.

Hypotheses and clauses are rendered as follows.

- A scheme X is `(X : Scheme.{u})`. The arbitrary coefficient ring is
  `(Λ : Type (u + 1)) [Ring Λ]`, with left modules `ModuleCat.{u + 1} Λ`. There is no
  `Finite`, torsion, constructibility, commutativity, or scheme finiteness hypothesis.
  The ring is used as an ordinary discrete coefficient ring; no topology is needed.
- The small etale and pro-etale sites are `X.smallEtaleTopology` and
  `Scheme.ProEt.topology X`. The comparison inverse/direct images and their adjunction
  are exactly the existing `comparisonUpperStar`, `comparisonLowerStar` and
  `comparisonAdjunction`; there is no private replacement of those constructions.
- The first theorem quantifies over all bounded-below objects through the functor domain
  `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat Λ))`. Its first conjunct is
  `IsIso (comparisonAdjunction ... X).derivedPlus.unit`. This is the actual derived
  adjunction unit, not an unspecified isomorphism between its source and target.
- Full faithfulness is the second conjunct, `Nonempty (...mapDerivedCategoryPlus.FullyFaithful)`.
  This is the bijectivity of the induced maps on all Hom sets in D+.
- The last conjunct, `IsIso (boundedBelowComparisonGlobalSections X Λ)`, is the canonical
  natural comparison on derived global sections. The definition applies etale derived
  sections to the derived unit, uses the bounded-below/unbounded compatibility isomorphism,
  and composes with `comparisonLowerStarCompRightDerivedGlobalSectionsIso`. The source is
  RGamma on the etale site; the target is RGamma on the pro-etale comparison pullback.
  Inverting this canonical map gives precisely the orientation displayed in the node.
- For the affine clause, `(B : Type u) [SmallCategory B] [IsCofiltered B]` is the inverse
  index category; filtered colimits run over `Bᵒᵖ`. The diagram `(D : B ⥤ X.Etale)` with
  `[∀ b, IsAffine (D.obj b).left]` gives the affine etale schemes U_i. The cone
  `c : Cone (D ⋙ toProEt X)` has pro-etale vertex U. The hypothesis `hc` says its
  underlying cone of schemes is a limit, exactly U = lim U_i. All transition maps are
  affine because they are maps between affine schemes; U is also affine by the
  affine-limit theorem. Those properties are therefore not extra hypotheses.
- The derived affine formula is given on injective representatives, avoiding an arbitrary
  diagram of unrelated derived objects or arbitrary comparison arrows. I is any
  bounded-below complex of injective etale module sheaves, `hI : CochainComplex.plus _ I`;
  J is any bounded-below injective pro-etale complex, with a quasi-isomorphism
  `j : nu^* I ⟶ J`. For K = Q(I), the section complexes of I at U_i compute
  RGamma((U_i)_et,K|U_i), and J at U computes RGamma(U_proet,(nu^*K)|U).
  Every K in D+ has such a representative and such a resolution of its pullback, by the
  imported enough-injectives and bounded-below resolution APIs. The statement is universal
  in the representatives and resolution map, not an existence assertion permitting a
  specially chosen map, and places no additional mathematical condition on K.
- `comparisonSectionComplexes` is just Mathlib's `sheafToPresheaf`,
  `Functor.mapHomologicalComplex` and `HomologicalComplex.asFunctor` composed. The
  helpers `comparisonResolutionUnit` and `comparisonResolutionSections` use the actual
  underived unit and the supplied resolution quasi-isomorphism. The cocone legs in
  `affineComparisonResolutionCocone` then restrict along `c.π.app b`. These prescribe
  all arrows canonically, including non-posetal cofiltered categories.
- The first affine conjunct is `IsIso (DerivedCategory.Q.map (colimit.desc ...))`.
  Its source is the image in D(Mod Λ) of the termwise filtered colimit of the stage
  section complexes; its target is the pro-etale section complex of J at U. Filtered
  colimits of modules are exact, so this source represents precisely the filtered
  derived colimit in the node. A colimit in the ordinary triangulated category is not
  substituted for a derived colimit.
- The second affine conjunct is `∀ n : ℤ, Nonempty (IsColimit (...homologyFunctor ... n
  |>.mapCocone ...))`: the same canonical cocone induces the filtered colimit on every
  cohomology group, including negative degrees. It is not merely an isomorphism of
  two unspecified groups.

Dependencies and interfaces read and used:

- `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`:
  `AlgebraicGeometry.ProEtale.comparisonUpperStar`, `comparisonLowerStar`,
  `comparisonAdjunction`, including their exactness and additivity instances. Their
  coefficient category is an arbitrary Grothendieck abelian category with Hom universe
  u+1, so ModuleCat over an arbitrary ring is allowed.
- `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`:
  the general derived-functor imports, and existing comparison constructions. I read
  `isIso_derivedComparisonAdjunction_unit_app` and
  `bijective_comparisonUpperStar_mapDerivedCategory_map` in full. Their particular
  unbounded-adjunction API assumes a symmetric monoidal coefficient category, so the
  new theorem instead uses the existing bounded-below `Adjunction.derivedPlus` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`,
  which works for arbitrary rings. No commutative-ring hypothesis is imposed to use
  the more specialized API.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension`:
  `comparisonLowerStarCompRightDerivedGlobalSectionsIso`, the actual Leray isomorphism,
  valid for general Grothendieck abelian coefficients.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity`:
  read `isColimit_comparisonUpperStar_mapCocone_of_isAffine` and
  `isColimit_comparisonUpperStar_mapCocone`. These are underived section continuity;
  they do not already state the derived affine formula.
- Mathlib `Algebra.Homology.Functor`: `HomologicalComplex.asFunctor` and
  `complexOfFunctorsToFunctorToComplex`; `Algebra.Homology.HomologicalComplexLimits`:
  termwise colimits of complexes. The canonical unit helper uses the existing
  `NatTrans.mapHomologicalComplex`, identity and composition isomorphisms.
- The current split's proof dependencies with statements are explicitly imported without
  `public`: general comparison unit (Comparison.FullyFaithful), exact derived functors
  (ExactFunctor), bounded-below injective resolutions, preservation of K-injectives
  (RightDerivedFunctor.Comp), K-injective Hom localization (Mathlib KInjective), termwise
  homotopy adjunction, Leray acyclicity (LongExactSequence and Acyclic), and the
  Grothendieck category of ring modules (ModuleCat.AB). Statement-dependency modules are
  explicit public imports, including the set comparison, ringed-site modules, Mathlib
  derived-category/Plus/right-derived functor, and upstream ProAffineEtale.
- The recorded set comparison `Scheme.proEtaleSiteComparison` is the exact same
  constructed geometric comparison. Its coefficient specialization has a finite-ring
  binder; the canonical upstream `comparisonAdjunction` used here is its general
  Grothendieck-abelian construction, so the set comparison is retained without the
  irrelevant finite-ring specialization. Fixed left-module sheaves are the explicitly
  permitted equivalent encoding of `ringedSiteModules` over the constant ring sheaf.
- `sk-def-pe-morphisms` is recorded as upstream `AlgebraicGeometry.proAffineEtale`.
  The concrete cone/diagram binders unfold its cofiltered affine-etale presentation,
  retaining the underlying site object and exact IsLimit cone, rather than adding an
  arbitrary predicate or unrelated scheme.
- The current split has two unstated proof inputs:
  `lem-pe-comparison-injective-left-modules-acyclic` and
  `det-sf-comparison-affine-continuity`. They are named in the natural-language proof,
  not imported or restated separately. The former already has the general upstream
  coefficient interface `rightAcyclic_comparisonUpperStar_obj_of_injective`; the latter
  is the detailed proof input for the assigned unit's affine clause. Neither is a
  missing statement definition. The older commutative-only
  `sk-lem-pe-injective-acyclicity` is no longer a proof dependency of the current split,
  so its extra proof import was removed.

Searches for an existing full statement:

- `msearch.py leanfinder`, query: "For a scheme the derived inverse image from etale
  sheaves to proetale sheaves is fully faithful on bounded below complexes and cohomology
  agrees". Eight hits: etale over-category fully faithful functors, fully faithful sheaf
  composition, dense-site pushforward and condensed embeddings; no full match.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.ProEtale.comparisonUpperStar, AlgebraicGeometry.ProEtale.rightDerivedLowerStar`.
  Zero hits; service reports unknown identifier comparisonUpperStar. This is a search
  index limitation, not evidence that the upstream construction is absent.
- `msearch.py grep`, pattern
  `comparisonUpperStar|pro.?etale.*[Cc]omparison|[Cc]omparison.*pro.?etale`, Mathlib
  `AlgebraicGeometry`: zero hits.
- Direct rg searches in upstream WeilConjectures, side WeilConjectures and lean/Sheaf
  for the blueprint names, the item id, comparison, derived/global sections, and
  continuity found the interfaces listed above. The four blueprint-listed names are
  not a match for the whole statement: comparisonUpperStar is underived; its full and
  faithful instances are underived; the fourth name compares direct images, not the
  affine filtered derived-colimit clause. The existing Derived.Comparison theorem
  supplies the unit clause only, through the specialized monoidal API.
- Read existing `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomology` and
  `Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity` and their node records. Those
  statements impose finite coefficients and the latter also commutative coefficients;
  they cannot be attached as the arbitrary-ring statement of this item.
- Direct rg of all seven new full-name stems in Mathlib, upstream WeilConjectures and
  lean/Sheaf found no collision. DAG search found the affine detail node
  `det-sf-comparison-affine-continuity`; it is an existing theorem about this same
  clause, not a missing definition. This delivery states only the assigned unit's
  clauses and does not restate that node separately.

Edge cases: the empty scheme and zero coefficient ring or zero complex are admitted.
There is no nonempty-X or nontrivial-ring assumption. All integer cohomology degrees
are retained; boundedness is below only, never above. A cofiltered category is nonempty
by definition, so there is no discarded empty inverse diagram. Constant singleton
presentations, identity projections, non-posetal parallel arrows and all allowed
resolution choices are covered by the actual unit, functoriality and cone equations.
The sites retain object universe u+1 and morphism universe u; coefficients have values
in u+1 and the inverse index category has the scheme universe u, following the project's
size convention. No equality of site object and morphism universes is imposed.

Validation: compilation and delivery dry run are performed only with the prescribed
`scompile.py` and `deliver2.py --no-push` wrappers. The refreshed file is recompiled and the dry run repeated. Both theorem proofs remain exactly
`by sorry`; no proof work, global build or direct shared-repository mutation is included.


## Second reading by Q07

I independently read the sandbox node and module, the blueprint unit statement,
Stacks `proetale.tex` lemmas `lemma-relative-comparison` (099V) and
`lemma-compare-cohomology` (099W), and `etale-cohomology.tex`
`lemma-directed-colimit-cohomology` (03Q6), including their surrounding hypotheses.
There is no repair note for this item. The sandbox carries the current reviewed
stage-1 split and coefficient/size clarification; the read-only shared checkout's
older unsplit item is not substituted for that delivery base. No `statement_change`
was introduced in this stage-2 delivery; no new node or dependency module is included.

My object/hypothesis/conclusion checklist, in source order:

1. An arbitrary scheme X: `(X : Scheme.{u})`, without an affineness, separation,
   Noetherian, characteristic, nonemptiness or finite-dimensionality assumption.
   Verdict: matches. Stacks 099V and 099W assume only a scheme.
2. An arbitrary discrete ring Lambda, and left modules: `(Λ : Type (u + 1)) [Ring Λ]`
   and `ModuleCat.{u + 1} Λ`. Neither `Finite Λ` nor `CommRing Λ` is assumed.
   Verdict: matches the node's explicit coefficient convention. Stacks states the
   abelian-sheaf result; retaining addition and each scalar action gives precisely
   the coefficient version specified by this blueprint node.
3. The small etale and pro-etale sites and their actual geometric comparison:
   `X.smallEtaleTopology`, `Scheme.ProEt.topology X`, `comparisonUpperStar`,
   `comparisonLowerStar`, and `comparisonAdjunction`. I opened the current shared
   `Comparison.Defs` source: pushforward is restriction, inverse image is the
   specified left Kan extension followed by sheafification, and the adjunction is
   the continuous-site adjunction. Its coefficients are arbitrary Grothendieck
   abelian categories with Hom universe u+1. The public site-comparison dependency
   uses these same constructions. Verdict: same objects, no arbitrary replacement.
4. Every K in D+: `boundedBelowComparison` asserts `IsIso` of the entire natural
   unit `(comparisonAdjunction ...).derivedPlus.unit`, whose domain is
   `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat Λ))`.
   I read `Adjunction.derivedPlus` and `derivedPlus_unit_app_fac`: the unit is
   induced by the actual underived unit and right-derived-functor comparison.
   `DerivedCategory.Plus` is the full subcategory for `exists n, IsGE n`, not
   bounded complexes or complexes concentrated in nonnegative degrees. Verdict:
   exactly the node's derived adjunction unit, for every bounded-below K.
5. Full faithfulness: the second conjunct is
   `Nonempty (...mapDerivedCategoryPlus.FullyFaithful)`. This means bijective maps
   on all Hom sets for that exact inverse-image functor. Verdict: matches.
6. The canonical global-sections isomorphism: the third conjunct is
   `IsIso (boundedBelowComparisonGlobalSections X Λ)`. Opening this definition
   shows derived etale sections of the unit, bounded/unbounded compatibility,
   then `comparisonLowerStarCompRightDerivedGlobalSectionsIso`. I read that
   existing Leray definition and its terminal-object section comparison. The
   resulting arrow runs from etale to pro-etale sections; its inverse has the
   displayed orientation of the node. Verdict: canonical and correctly oriented.
7. A nonempty small cofiltered affine-etale presentation: `{B : Type u}`,
   `[SmallCategory B] [IsCofiltered B]`, `(D : B ⥤ X.Etale)`, and
   `[∀ b, IsAffine (D.obj b).left]`. These are absolute affine source schemes,
   not merely affine morphisms to X. The cone `c : Cone (D ⋙ toProEt X)` gives
   U and its compatible projections, and `hc` asserts the underlying scheme
   cone is limiting. For a nonempty cofiltered category this is equivalent to
   its limit over X. I opened `proAffineEtale`, whose definition is
   `MorphismProperty.pro.{u} (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)`;
   these binders expose exactly that presentation. U is already a pro-etale
   site object; its affineness follows from the affine limit. Verdict: matches.
8. The same arbitrary bounded-below K in the affine formula: `I`, `hI`, and
   termwise injectivity give an injective representative; `J`, `hJ`, termwise
   injectivity, and `[QuasiIso j]` give a resolution of its actual comparison
   pullback. I read the Mathlib injective derivability interface: injective
   bounded-below representatives exist for every D+ object and the derived
   functors are computed on them. Restriction to an object is localization of
   its site, so evaluating I and J computes the two local derived sections.
   The universal quantification over these representatives and every resolution
   j adds no condition on K. Verdict: an equivalent resolution presentation,
   covering all K, with no bounded-above restriction or arbitrary comparison map.
9. Filtered derived colimit comparison: `comparisonSectionComplexes` evaluates
   each complex functorially. `comparisonResolutionUnit` is the actual unit
   followed by R(j); `comparisonResolutionSections` evaluates it; the affine
   cocone composes with restriction along the projections of c. Thus
   `IsIso (DerivedCategory.Q.map (colimit.desc _ ...))` is precisely the canonical
   map from the termwise filtered colimit of stage section complexes to the
   pro-etale section complex of J at U. Exact filtered module colimits compute
   the filtered derived colimit. Verdict: matches; an ordinary colimit of
   triangulated-category objects has not been substituted.
10. Cohomology of that colimit, for every degree: the second affine conjunct is
    `∀ n : ℤ, Nonempty (IsColimit ((...homologyFunctor ... n).mapCocone ...))`.
    It uses the identical canonical restriction cocone, and includes degree zero
    and negative degrees. Verdict: all clauses match, including compatibility
    with the given transition arrows.

Dependency review: I read the six dependency node statements and their recorded
interfaces, not just their names. The derived category is Mathlib's localization
`DerivedCategory` with `Q`; the bounded subcategory is Mathlib `Plus`; the
right-derived input is `Functor.rightDerivedFunctorPlus`, its unit and injective
calculation. `ringedSiteModules` is transparently `SheafOfModules`; the node
explicitly permits the fixed-left-module sheaf encoding used here. The finite-ring
binder of `proEtaleSiteComparisonModules` is not imported as a hypothesis: the
actual general coefficient `comparisonAdjunction` is already upstream. No
interface repair or missing definition is required. I also read
`coord/pefw-upstream-framework.md` and the relevant shared pro-etale sources.
The proof docstrings track steps 1--6 and the affine step 7 of the current node,
with source references and the blueprint marker on each declaration.

Edge cases: empty X, empty affine schemes, the zero ring and zero complex are
allowed. No nontriviality, torsion, invertibility or characteristic assumption is
present. The empty inverse index is excluded by the node itself (`IsCofiltered`
includes nonemptiness), not by an extra Lean restriction. Singleton presentations,
identity maps, general parallel arrows, all integer degrees and all resolution
choices are covered. The site object universe is u+1 and its Hom universe u;
module values and coefficients use the common u+1 universe, and the small inverse
index uses u as in the recorded `proAffineEtale` interface. No equality of site
object and morphism universes is imposed. All variables and universes are bound.

Independent duplicate searches used different wording from the worker:

- `msearch.py ... leanfinder "derived etale proetale comparison for discrete module
  sheaves unit isomorphism and continuity on affine inverse systems"`: eight
  condensed/discrete-module and solidification hits, none the node's statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction,
  CategoryTheory.Functor.FullyFaithful"`: ten generic adjunction results, notably
  `fullyFaithfulLOfIsIsoUnit`. I checked its signature: it supplies only the
  formal full-faithfulness implication, not the comparison unit or continuity.
- `msearch.py ... grep "rightDerivedGlobalSections|derivedComparisonAdjunction"`:
  zero Mathlib-index hits. Direct rg in Mathlib, upstream WeilConjectures, the
  shared lean/Sheaf tree and the upstream name inventory supplemented this.
  I opened upstream `Derived.Comparison`: its existing unit and Hom-bijection
  theorems require the monoidal coefficient hypotheses, which do not apply to
  left modules over every noncommutative ring. The existing continuity theorem
  is underived. I opened `ComparisonGlobalCohomology` in full: both its helper
  and theorem require `[Finite Λ]`, so they cannot express the arbitrary-ring
  comparison here. `DerivedCohomologyContinuity` additionally requires
  commutativity and finite coefficients. No full match or name collision was
  found. No second general coefficient category or site construction is defined.

Mismatch found and repaired: the first version proved the affine cocone's
naturality inline by tactics, contrary to the stage-2 no-proof requirement.
Instead of introducing another theorem, I replaced that structure literal by
Mathlib's existing `Cocone.precompose`, `Functor.whiskerLeft`, `Functor.mapCocone`
and `Cone.op`. This gives exactly the same vertex and comparison/restriction
legs, with naturality supplied by the existing categorical constructions. All
five helpers contain real data, with no sorry, arbitrary Nonempty choice, local
notation or private definition. The two main theorem proofs remain `by sorry`.
I also made `lean.statement` the literal multiline primary signature from the
module. No mathematical statement, hypothesis or conclusion was changed.

Validation: the repaired sole delivery module compiled cleanly via `scompile.py`
in both sandbox and library contexts (12.9 s and 6.8 s). No errors or warnings
were emitted. Delivery dry run and delivery are performed through `deliver2.py`.
