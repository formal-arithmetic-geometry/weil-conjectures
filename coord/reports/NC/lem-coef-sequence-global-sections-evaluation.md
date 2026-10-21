## Worker report

The module `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections` states
`SheafOfModules.coefficientSequenceGlobalSectionsEvaluation`. Its only postponed theorem
is that declaration, with proof `sorry`; its docstring contains the seven steps of the
node's proof, with dependency identifiers. Every helper has real data. There are two new definition nodes owning existing declarations. There are no
dependency-module repairs, statement corrections, or disputed statements.

The natural-language statement is unchanged. The statement dependencies directly cite
`def-pur-system-level-left-extension-basic`, `def-coef-system-derived-transition`, and
`def-coef-tower-derived-evaluation-transition`. The latter two are new definition nodes
with existing:true records on the published modules. They own the actual localized
semilinear transition and actual tower evaluation transition. The theorem nodes
`lem-pur-system-derived-transition` and
`lem-weil-pbc-tower-derived-evaluation-normalization` are not statement dependencies;
their theorems are unused by this statement.

The conclusion is an existential package of functors, universal derived units, natural
isomorphisms and their normalization equations. The package does not select data from a
mere existence assertion. In particular, `global`, `restrictedEvaluation` and
`finiteEvaluation` are explicit functor/iso compositions of that package's data, not
choices made from the final postponed theorem. Exact restriction is determined up to the
specified sectionwise identity natural isomorphism. Right derived functors use Mathlib's
`Functor.IsRightDerivedFunctor` universal property, and both comparison isomorphisms
are fixed by their derived-unit equations.

Hypothesis and clause correspondence:

- Small site: `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}` and
  `[EssentiallySmall.{w} C]`. The associated Grothendieck topology is the sheaf-theoretic
  presentation of the recorded site convention. Object, arrow and coefficient universes
  remain independent. The standard sheafification, locally bijective and commutative-ring
  forgetful-sheaf instances are explicitly bound, exactly as in the recorded arbitrary
  sequence-site dependency. None is an exactness or flatness assumption on a ring map.
- The inverse coefficient sequence is `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}`. As in
  `def-weil-inverse-system`, index `n : ℕ` means positive level `n+1`. All composite and
  identity coefficient maps are retained.
- Strict semilinear systems are the existing `SheafOfModules.StrictRingSystem B`.
  Its `systemLevel`, `systemRestriction`, componentwise abelian structure and exact
  `systemEvaluation` are used unchanged. `strictSystemSequenceEquivalence` in the
  sequence-site dependency identifies this category with `systemSequenceModules B`;
  no second strict-system category is defined here.
- A common ring and compatible maps are `A : Sheaf J CommRingCat.{w}` and
  `α : (Functor.const ℕᵒᵖ).obj A ⟶ B`. The naturality of α is exactly compatibility
  with every coefficient transition, not an extra hypothesis.
- The ordinary exact restriction is `SequenceCoefficientRestrictionData.functor`.
  Its `evaluation` identifies evaluation with `systemEvaluation B n` followed by the
  actual Mathlib `restrictScalars` for `α.app (op n)`. `evaluation_sections` says that
  this identification is the identity on each section. `transitions` says that tower
  arrows, under those same identifications, are the original semilinear transitions.
  Naturality of `evaluation` fixes the maps on system morphisms as well. Thus this
  specifies termwise scalar restriction, not merely an unrelated exact functor.
  `additive`, `limits` and `colimits` assert its componentwise exactness.
- The ordinary functor `sequenceCoefficientSections R` is explicitly
  `toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat ⋙ lim`, with the recorded conversion
  from commutative ring sheaves to ring sheaves. This is global sections on any site,
  including one without a terminal object. `sequenceAbSiteLimits` obtains the needed
  limits from essential smallness in the coefficient universe. This is the standard
  limit presentation of `Sheaf.Γ`, not a new sheaf or an unspecified section object.
- `sequenceTowerSections A` is whiskering by that sections functor, so sends a tower
  to its actual tower of abelian global sections, on objects and morphisms.
- Unbounded derived categories are the existing `DerivedCategory` on integer cochain
  complexes. The localizations of modules are the recorded standard instances; the
  three additional standard instances specialize `HasDerivedCategory.standard` to
  constant-coefficient towers, abelian groups and strict abelian towers.
- `SequenceSectionsDerivedPair` packages the existing Mathlib total right derived
  universal property, its complex-level unit, and invertibility of that unit on every
  K-injective complex. `finite R` is that package for sections in R-modules;
  `tower` is that package for constant-A tower sections. The computation clause
  `computes` is precisely the K-injective computation. K-injective replacements exist
  in these module/tower categories by the recorded resolution dependencies.
- Exactness supplies `restriction.functor.mapDerivedCategory`, the U of the node.
  `SequenceSectionsComparisons.global` is explicitly U followed by `tower.functor`.
  It is an actual functor out of `DerivedCategory (StrictRingSystem B)` into
  `DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{w})`, including maps of derived objects.
- The constant-A evaluation comparison is `SequenceSectionsComparisons.evaluation`.
  `Normalized.evaluation_unit` says that, after exact-localization factors, evaluation
  of the tower unit followed by this comparison equals the finite unit evaluated on
  the same tower complex. It is imposed on every K-injective constant-A tower.
  This fixes the same-resolution comparison of the node.
- `sequenceRestrictionDerivedEvaluation` explicitly localizes the ordinary restriction
  evaluation isomorphism, using the exact-functor composition comparisons.
  `restrictedEvaluation` composes it with the preceding tower comparison. Its endpoints
  are exactly e_n G and RΓ_A(Res J_n), as in the first displayed isomorphism.
- The scalar comparison is `scalar f : (finite S).functor ≅
  (sequenceCoefficientRestriction f).mapDerivedCategory ⋙ (finite R).functor`.
  `Normalized.scalar_unit` is its derived direct-image composition normalization:
  η_S followed by σ and the restriction/localization factor equals η_R on the
  restricted complex. It holds for every complex, not just a bounded or specially
  resolved one. The underlying section functors agree literally, since restriction
  does not change their abelian presheaves. The universal property makes this the
  canonical composition comparison and forces identity/composition normalization.
- `finiteEvaluation` is `restrictedEvaluation` followed by the inverse of that scalar
  comparison at `A → B_n`. Its endpoint is `derivedSystemEvaluation B n` followed by
  derived sections computed in B_n-modules with values in abelian complexes. This is
  exactly the second displayed isomorphism.
- `Normalized.evaluation_transition` intertwines the actual transitions of the derived
  constant-A tower with the maps induced by its own transitions after finite sections.
  `Normalized.finite_transition` intertwines the actual transition of G with
  `(finite B_n).functor.map ((systemDerivedTransition B h).app M)` followed by the
  inverse scalar comparison for `B_n → B_m`. Thus the right-hand side is precisely
  the derived sections map of `J_n → Res J_m`. The formula quantifies over every
  `h : m ≤ n` and every derived input M, including identities and iterated transitions.
- All comparisons are `NatIso`s of actual functors. Naturality for every derived input
  morphism is built into their type, rather than asserted only for strict chain maps.
- There is no assumption or conclusion that varying-ring evaluation preserves
  K-injectives. The only K-injectivity in the comparison normalization concerns a
  constant-A tower. No normalization, flatness, boundedness, nonzero-ring assumption,
  or exactness of infinite products is imposed.

Dependency declarations read and used:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, with its sectionwise scalar-action construction
  and additive instance.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, including its homotopy-zero definition.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `HasDerivedCategory.standard`, and Q.
- `Mathlib.CategoryTheory.Functor.OfSequence`:
  `Functor.ofOpSequence`, `NatTrans.ofOpSequence`; inverse systems are functors from
  ℕᵒᵖ, after the recorded shift of positive indices.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the associated topology presentation
  is the one used by the module/sheaf sequence-site interfaces.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, a transparent abbreviation of Mathlib's
  `SheafOfModules`, with the existing abelian instance.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `systemSequenceModules`, `strictSystemSequenceEquivalence`; it publicly exposes
  `StrictRingSystem`, `systemEvaluation`, `systemRestriction`, `derivedSystemEvaluation`
  from `Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic`, and their exactness.
- `Sheaf.CategoryTheory.SystemDerivedTransition`:
  `systemDerivedTransition` only, now owned by
  `def-coef-system-derived-transition`. Its theorem `systemDerivedTransition_rep` is unused.
- `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`:
  `CategoryTheory.towerDerivedEvaluationTransition`, the localized ordinary tower map.
- `Mathlib.CategoryTheory.Functor.Derived.RightDerived`:
  `Functor.IsRightDerivedFunctor`, used rather than a private universal-property copy.
- `Mathlib.CategoryTheory.Limits.EssentiallySmall`:
  `hasLimitsOfShape_of_essentiallySmall`; and `Mathlib.CategoryTheory.Sites.GlobalSections`,
  read for the canonical limit interpretation of global sections.

All recorded proof-dependency modules are imported, as ordinary imports. These include
exact derived factorization, Grothendieck small module diagrams, functorial resolutions,
K-injective total derivation, Hom localization into K-injectives, constant-coefficient
K-injective evaluation, restriction as ringed-topos direct image, ringed-topos derived
pushforward composition, the singleton-site comparison, and constant sheaves.

Edge cases checked before and while writing: the empty site (limits are terminal zero
abelian groups); zero rings and zero modules; constant rings with identity maps; a site
without a terminal object (global sections are a limit, not evaluation at a chosen object);
the initial positive level (encoded by 0); identity transitions (`m = n`); arbitrary
iterated transitions; and unbounded complexes in both cohomological directions.
Independent u/v/w and essential smallness allow equivalent small site models without
forcing object and arrow universes equal. All equations are well typed in these cases.
The scalar unit condition applies to identity maps as well as composites, so those cases
are not silently omitted.

Searches made using the prescribed wrappers and local source reads:

1. `msearch.py ... leanfinder` with query "Derived termwise global sections of strict
   varying coefficient module sheaf towers commute with finite evaluation and scalar
   restriction": eight hits, including `SheafOfModules.Presentation.map_π_eq`,
   `map_ιFree_mapFree_hom`, `GeneratingSections.opEpi_comp`,
   `CategoryTheory.Sheaf.ΓRes_map_assoc` and free-module/sheafification statements.
   None states this unbounded coefficient-system comparison.
2. `msearch.py ... loogle` with query
   "SheafOfModules.restrictScalars, CategoryTheory.Functor.IsRightDerivedFunctor":
   zero hits for the combined search. The individual recorded APIs were read directly.
3. `msearch.py ... grep` with expression
   `rightDerived.*[Ee]val|[Ee]val.*rightDerived|KInjective.*[Ee]val|[Ee]val.*KInjective`
   in Mathlib/CategoryTheory: zero hits.
4. `msearch.py ... leansearch` with query "Global sections of strict coefficient systems
   on sequence sites have an unbounded right derived functor compatible with finite
   evaluations and transitions": eight hits, including `CategoryTheory.Sheaf.Γ`,
   `Functor.HasPointwiseRightDerivedFunctorAt.mk`, `PresheafOfModules.sections`,
   and presheafed/sheafed-space sections. No exact match.
5. `rg` searches in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream names index
   for the item id, global sections/evaluation/K-injective terms, strict-system scalar
   restriction, and all proposed declaration names. The specialized pro-etale DVR
   construction in `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` was read, as were
   `CoefficientRingedSequenceSite`, `SystemScalarModel`, `SystemScalarCoherence`,
   `SystemDerivedTransition` and `TowerDerivedEvaluationNormalization`. The specialized
   construction fixes a prime, a field, a scheme and a DVR quotient sequence; it does
   not state the present theorem for an arbitrary site, arbitrary B and common A.
   The general transition and scalar APIs found by these searches are reused here.

Source checked directly: `literature/stacks-project/sites-cohomology.tex`, proof of
`lemma-derived-limit-is-ok` (0941), including the exact left adjoint to evaluation,
and `lemma-derived-pushforward-composition` (0D6E). The supplied seven-step combination
of these two results is retained in the theorem docstring.

Validation: the full statement compiled cleanly using scompile.py, both as sandbox and
library module (30.7 and 33.5 seconds respectively), before the final explicit dependency
import list was completed. Final delivery runs recompile that exact final module.


## New nodes

`def-coef-system-derived-transition` owns the unchanged declaration
`SheafOfModules.systemDerivedTransition` in
`Sheaf.CategoryTheory.SystemDerivedTransition`, with existing:true and no copied module.
It defines the localization of the strict semilinear transition followed by the exact
composition comparison. The site, inverse ring sequence, module categories, restriction,
strict-system evaluations and unbounded localization are explicitly introduced and cited.
The source is Zheng Construction 4.1, with exact localization from Stacks 015F.
The map is explicit data, not chosen from `systemDerivedTransition_rep`.

`def-coef-tower-derived-evaluation-transition` owns the unchanged declaration
`CategoryTheory.towerDerivedEvaluationTransition` in
`Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`, with existing:true and no
copied module. It defines localization of the actual degreewise tower arrow between exact
evaluations for any abelian category with chosen derived categories. It needs neither
Grothendieck hypotheses nor a derived adjunction. The source is the paragraph preceding
Stacks 0941 defining the derived finite-level maps, and Stacks 05RU/015F for localization.
It does not use the postponed normalized-evaluation theorem in the same module.

For each new node, the prescribed msearch.py LeanSearch and LeanFinder queries returned
eight related results but no exact construction. The exact queries and result names are
in each node's mathlib_searches and in the launcher search log. The Mathlib grep queries
`systemDerivedTransition|strictSystemTransition` and
`towerDerivedEvaluationTransition|evaluation.*mapDerivedCategory` returned zero hits.
Direct rg searches of WeilConjectures returned no matching definition; Sheaf searches
found exactly the two reused declarations and their consumers. DAG searches found them
attached only as helpers to theorem nodes, with no owning definition node. Blueprint
searches for “derived transition”, “derived evaluation transition”, “strict systems” and
“tower evaluation” all returned zero matches. The ancestor command returns
`prop-coef-integral-exceptional-adjoint`; both new nodes retain the item's chapter and
unit and prepend this item to its blueprint via path.

## Repair of the returned delivery

H2: the saved packet differed from the read clone only in lean and stmt_deps. Its first
deliver2.py --no-push run passed, but that mechanical result does not resolve ownership.
The two theorem-node references have now been replaced by the two new existing:true
definition nodes above. The direct dependency
`def-pur-system-level-left-extension-basic` was added because StrictRingSystem,
systemEvaluation, systemRestriction and derivedSystemEvaluation are used in the signature.
The complete Lean module is retained byte-for-byte, as permitted by the independent
review of immutable head 30cd11879cc5; its mathematical statement and proof plan are
unchanged. No theorem has been used as the source of either transition definition.

Repair self-check: opened both complete transition definitions and their source
localization API, including Localization.liftNatTrans and its canonical lifting factors.
Matched all binders of the system map (independent site/coefficient universes, the
sheafification instances, B, and every m ≤ n) to the first new node. Matched the arbitrary
abelian A, both chosen derived categories, m/n in ℕᵒᵖ and t : m ⟶ n to the second.
Both signatures in lean.statement are verbatim through the colon/type before :=.
Identity, composite and zero transition arrows remain included; the system identity
transition is not incorrectly asserted to be a literal identity across scalar restriction.
Neither new definition introduces K-injectivity, flatness, boundedness or new hypotheses
into the accepted main theorem. The advisory about Sheaf.Γ and the standard tower-Ab
instance is recorded; the accepted source was preserved for this dependency-only repair.
No second worker was started: the brief reserves independent review to the maintainer.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
