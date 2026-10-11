## Worker report

The module `Sheaf.Paper.SiteRestrictionExact` states exactness of restriction to the localized site.  It uses Mathlib's `Precoverage` and `toGrothendieck` encoding for a site, `Sheaf ... AddCommGrpCat` for abelian sheaves, and `ShortComplex.ShortExact` for a short exact sequence.  The functor is Mathlib's `GrothendieckTopology.overPullback`; `siteRestrictionShortComplex` is its image short complex.  The auxiliary theorem `siteRestriction_preservesZero` supplies the zero-morphism preservation needed to form that image.

The binders `{C : Type u} [Category.{v} C]`, `J` with `HasIsos`, stability under composition and base change, and `HasPullbacks` express the site.  `W : C` is the localization object.  The two `HasSheafify` instances provide the abelian sheaf categories on the site and slice.  `S` and `hS : S.ShortExact` express an arbitrary short exact sequence.  The conclusion `(siteRestrictionShortComplex J W S).ShortExact` expresses exactness after restriction.

Dependency declarations used: `def-weil-pbc-sites-and-cohomology` is represented by Mathlib's `Precoverage`, `Precoverage.toGrothendieck`, `GrothendieckTopology.over`, and `GrothendieckTopology.overPullback` in `Mathlib.CategoryTheory.Sites.Over`; `def-sp-abelian` is Mathlib's `CategoryTheory.Abelian` in `Mathlib.CategoryTheory.Abelian.Basic` (with `AddCommGrpCat` from `Mathlib.Algebra.Category.Grp`).

Edge cases checked: `W` is arbitrary, including an initial or terminal object; no nonemptiness of covering families or objects is assumed; the index and category universes are explicit; zero objects and zero morphisms are included by the additive sheaf categories.

Searches: LeanFinder query “restriction of abelian sheaves to a localized site is exact” found only generic sheaf pullback infrastructure; Loogle query “PreservesFiniteLimits, sheafPullbackConstruction” had no exactness result; grep of `Mathlib/CategoryTheory/Sites/Over.lean` found `overPullback` but no exactness theorem; `rg` over `WeilConjectures/` found no project declaration. No existing declaration matches the node.

## Earlier second reading (a previous round; superseded)

The node and module were read together. The site hypotheses correspond to the localized Grothendieck topology, `W` introduces the slice object, `S.ShortExact` gives the three-term short exact sequence, and the conclusion applies the restriction functor to all three terms and morphisms. No hypothesis or conclusion clause is omitted.


## Second reading by G1

Read the node's statement and both proof steps, its two dependency nodes and their
recorded declarations, and the Stacks source in the local reference copy
`c1-stacks-review/sites.tex` (00VH, lines 679–735; 00XZ, lines 5164–5221)
and `sites-modules.tex` (localization, lines 1992–2045; 03DJ, lines 2160–2190).
The repository literature directory does not contain those TeX files on this machine.
03DJ itself asserts exactness of extension by zero; the restriction functor and its
section formula are in 00XZ and the surrounding Modules on Sites localization section.
The node's restriction assertion is correct; its source citation is contextual rather
than a literal assertion of 03DJ. The module docstrings now make this distinction.
No mathematical statement correction was needed, and no new/dependency node is delivered.

Clause-by-clause inventory and verdicts:

- Objects and morphisms forming sets: `{C : Type u} [SmallCategory C]`.
  This is precisely the small-site encoding required by the dependency's `lean.note`.
  Every site fits after choosing a universe containing its objects and morphisms.
- Coverings of the site: `J : Precoverage C`, `[J.HasIsos]`,
  `[J.IsStableUnderComposition]`, `[J.IsStableUnderBaseChange]`, `[J.HasPullbacks]`.
  Read `Precoverage.lean`: these encode 00VH's isomorphism, composite-covering,
  base-change-covering and existence-of-covering-pullbacks axioms. They do not
  assume arbitrary pullbacks in C. The dependency records exactly this encoding;
  its reindexing convention is automatic for presieves. Verdict: exact match.
- Localization object: `W : C`, unrestricted. Verdict: exact match.
- Localized topology, underlying coverings: `J.toGrothendieck.over W`.
  Read `Precoverage.toGrothendieck`, `isSheaf_toGrothendieck_iff`, and
  `GrothendieckTopology.over` / `mem_over_iff` in `Sites.Over`:
  slice covering sieves correspond to covering sieves of the underlying object.
  Verdict: same localized sheaf category, not an unrelated slice topology.
- Abelian sheaf categories: `Sheaf J.toGrothendieck AddCommGrpCat.{u}` and
  `Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{u}`. The recorded sheaf definition
  is the full subcategory of sheaf presheaves. Read `sheafIsAbelian` and the
  `Abelian` class in `Abelian.Basic`; these supply the dependency's abelian
  structure. Verdict: no change of coefficient category or extra mathematical
  assumption. `Sites.LeftExact` plus `Grp.FilteredColimits` supplies sheafification
  on these small sites; both former `HasSheafify` hypotheses are removed.
- Restriction `j_W^*`: `J.toGrothendieck.overPullback AddCommGrpCat.{u} W`.
  Read its abbreviation and `Functor.sheafPushforwardContinuous`: this is
  precomposition with `(Over.forget W).op`, and its maps are the original
  natural transformations on underlying objects. Verdict: exactly G(V).
- Arbitrary short exact input: `S : ShortComplex (...)`, `hS : S.ShortExact`.
  The three objects and two differentials of S are G1, G2, G3 and their maps;
  `ShortExact` means middle exactness, mono of the first map, epi of the second.
  Verdict: exactly the short exact sequence with zero endpoints, with quantifiers
  after the site and W as in the node.
- Conclusion: `(S.map (J.toGrothendieck.overPullback AddCommGrpCat.{u} W)).ShortExact`.
  `ShortComplex.map` applies this same restriction to all three objects and both
  maps. Verdict: every conclusion clause, with no added exactness claim.

Edge cases: there is no nonempty-site assumption (if C is empty, there is no W
and the universal assertion has its intended vacuous meaning). Initial and terminal
W are allowed without requiring either to exist. Empty covering families are
allowed by Precoverage; their sheaf conditions are preserved on the slice.
Zero sheaves and zero differentials are allowed. No schemes, characteristic, or
degree n occur in this lemma, so empty schemes and n = 0 impose no hidden condition.
The single site universe u is arbitrary; it bounds both objects and morphisms as
in the recorded small-site convention, and abelian group carriers lie in the same
arbitrary universe. All variables are explicitly bound; compilation disables
both autoImplicit and relaxedAutoImplicit.

Independent searches, with different wording from the first worker:

- LeanFinder: “localization slice site abelian sheaves restriction short exact
  sequence”: returned Mayer–Vietoris short complexes and their exactness, which
  concern a particular square, not arbitrary restricted sequences.
- Loogle: `CategoryTheory.GrothendieckTopology.overPullback`: returned the
  restriction abbreviation, topological-space comparison isomorphisms and local
  isomorphism detection, none a declaration of this full assertion.
- LeanSearch: “restriction to a slice site preserves short exact sequences of
  abelian sheaves”: service unavailable (Internal Server Error), no verdict.
- Direct rg over Mathlib Sites, upstream WeilConjectures (including its Sites
  complements), the project's lean/Sheaf and dag/lean_names_upstream.json:
  searched overPullback, siteRestriction, localized/exact, restriction/exact,
  PreservesZeroMorphisms and sheafPushforwardContinuous/additive. Found the
  upstream `Functor.preservesLimitsOfShape_sheafPushforwardContinuous` and
  `preservesFiniteLimits_sheafPushforwardContinuous`, whose signatures were read.
  These already give the zero-preservation needed by `ShortComplex.map` after
  importing the sheafification instances. Also read upstream
  `preservesColimits_overPullback` / `preservesFiniteColimits_overPullback`
  in `ConstantSheafOver.lean`: these require pointwise right Kan extensions and
  state preservation of colimits, not this full short-exact-sequence assertion.
  The generic `ShortComplex.ShortExact.map_of_exact` has finite-limit/colimit
  hypotheses on an arbitrary functor, so is not an identical statement either.
  No existing declaration states the entire node; no duplicate notion is needed.

Mismatches repaired: the previous independent hom universe plus assumed
sheafification obscured the recorded small-site convention and added two
unnecessary hypotheses. Replaced it with the dependency's `SmallCategory` form
and imported the standard sheafification instances. Removed the redundant
`siteRestriction_preservesZero` sorry and `siteRestrictionShortComplex` definition,
using existing zero-preservation infrastructure and `ShortComplex.map` directly.
Expanded the theorem docstring to carry both proof steps, the kernel-gluing
argument, and both applications of the locally-surjective epimorphism lemma.
Added the standard copyright header and clarified the contextual 03DJ citation.
The remaining theorem proof is exactly `sorry`; nothing is proved, and no hollow
definition, local notation, private definition or local instance remains.
Updated `lean.statement` verbatim from the new signature. Local file compilation
passed cleanly in 1.6 seconds; delivery runs the required server compilation.
