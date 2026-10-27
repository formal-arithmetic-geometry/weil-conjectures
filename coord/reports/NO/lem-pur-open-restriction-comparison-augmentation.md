## Worker report

Item: lem-pur-open-restriction-comparison-augmentation, stage 2, group NO.
Module: `Sheaf.Paper.PurityOpenRestrictionAugmentation`.
Main declaration: `AlgebraicGeometry.ProEtale.supportComparisonOpenRestrictionAugmentation`.
The only postponed proof is this theorem (`by sorry`). The two owning-node helpers
construct actual canonical maps; neither uses a postponed existence theorem or arbitrary choice.
No statement correction, new node, or dependency repair is needed. The previous worker's
stage-1 live-wins objection does not apply to this stage-2 statement delivery: the live
node has a reviewed split and no Lean attachment.

Hypothesis and clause correspondence (compositions in Lean are written left to right):

- The finite commutative ring is `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`.
  `T V : Scheme.{u}`, `j : V ⟶ T`, `[IsOpenImmersion j]` give the schemes and open
  immersion. The coefficient size follows the recorded ordinary fixed-ring comparison
  API: both sites have object universe u+1, morphism universe u, and module coefficients
  in u+1. No equality of these site universes, geometric finiteness, or nonemptiness is assumed.
- Ordinary constant-A module sheaves are `Sheaf _ (ModuleCat.{u + 1} A)`, precisely the
  encoding of `Scheme.proEtaleSiteComparisonModules`, rather than structure-sheaf modules.
  `comparisonAdjunction` provides the specified adjunction and ordinary unit.
  Etale and pro-etale `openImmersionRestriction` are the canonical sectionwise restriction
  presentations of the given inverse images, as in the recorded open-unit theorem.
- `F : Sheaf T.smallEtaleTopology (ModuleCat A)` is completely arbitrary. `J` is a
  `CochainComplex.Plus` of ordinary pro-etale module sheaves, indexed by all integers.
  `h` starts at inverse image applied termwise to `supportComparisonSource T A F`.
  The two hypotheses `QuasiIso h.hom` and `∀ n : ℤ, Injective (J.obj.X n)` say exactly that
  this is a bounded-below injective resolution. Plus packages boundedness; it does not
  force all negative terms to vanish as an N-indexed resolution would.
- `F_V` is the object image of `Etale.openImmersionRestriction`; `J_V` is the termwise
  image of `openImmersionRestriction`. `supportComparisonOpenResolutionMap` is h_V.
  Its source is transported by `supportComparisonOpenSourceIso`: inverse of
  `HomologicalComplex.singleMapHomologicalComplex` for etale restriction, then
  `NatIso.mapHomologicalComplex (comparisonPullbackOpenUnitGamma A j)`. This is exactly
  beta followed by restriction of h, with the unavoidable degree-zero source
  identification explicit. The beta is the dependency's canonical gamma, not an
  independently chosen isomorphism.
- The first two conjuncts give `QuasiIso h_V.hom` and injectivity of all J_V terms.
  Boundedness and preservation of the original lower bound are built into
  `Functor.mapCochainComplexPlus` (termwise restriction preserves zero objects).
- The next conjunct is the actual equality `nu_V,* J_V = j_e^{-1}(nu_T,* J)` of Plus
  complexes. This uses the literal section identity, not a newly postulated isomorphism.
  The following injectivity and `QuasiIso (supportComparisonAugmentation V ...)` conjuncts
  state that a_V is the etale bounded-below injective resolution.
- The next equality of sheaf morphisms is the ordinary unit equation
  `j_e^{-1}(eta_F) = eta_{F_V} ≫ nu_V,*(beta_F)`. The direct-image restriction
  comparison c is definitionally the identity (`comparisonPullbackOpenUnitC`).
- The following augmentation equality explicitly expands a_V into its ordinary unit,
  direct image of the source transport/beta, and direct image of j_p^{-1}(h).
  The next equality identifies this very map with `j_e^{-1}(a)`, preceded only by the
  canonical inverse single/restriction identification on its source. Thus both
  augmentation equalities in the node are retained as equalities of chain maps.
- The conjunct quantified over `W : V.Etale` identifies BOTH the etale restricted
  direct-image complex and J_V evaluated at W with J evaluated at W over T.
  These are equalities of entire `CochainComplex` objects, including the differentials.
  The next conjunct over `W₁ W₂`, `b : W₁ ⟶ W₂`, and every integer n identifies BOTH
  restriction arrows with the actual arrow of J over T. No mere cohomology comparison
  replaces any of these assertions.
- The existential theta is an isomorphism in `DerivedCategory.Plus`, from localization
  of `nu_V,* J_V` to `Rnu_V,* nu_V^* Q(F_V[0])`. Its equation
  `theta.hom ≫ supportComparisonDerivedResolutionMap = rightDerivedFunctorPlusUnit`
  characterizes the canonical injective computation as alpha followed by inverse R(Qh_V).
  The second equation `Q(a_V) ≫ theta.hom = derivedComparisonAdjunctionPlus.unit`
  is precisely the derived-unit normalization. This retains a derived isomorphism,
  not only per-degree isomorphisms.
- The final quantified clause includes every second resolution F', J', h', its same
  quasi-isomorphism and injectivity conditions, every sheaf map f and every chain map t,
  and exactly the compatibility equation `h ≫ t = nu_T^*(f[0]) ≫ h'`.
  It concludes `h_V ≫ t_V = nu_V^*(f_V[0]) ≫ h'_V` and
  `a_V ≫ nu_V,*(t_V) = f_V[0] ≫ a'_V`.
  The final theta' has the same canonical characterization by alpha and h'_V,
  and the last equation is `Q(nu_V,* t_V) ≫ theta' = theta ≫ Rnu_V,*(nu_V^* Q(f_V))`.
  This is the required naturality of the canonical computations. No arbitrary lift,
  supported comparison, global comparison, or connecting map enters the statement.

Dependencies read and reused:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and Hom.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`, `IsOpenImmersion`.
- def-weil-pbc-derived-categories: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `Etale.DerivedCategoryModule` (defined in the imported coefficient module);
  Mathlib `DerivedCategory.Plus` and `DerivedCategory.Plus.Q`.
- def-weil-pbc-proetale-modules: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
  `finiteCoefficientRingSheaf`, `FiniteCoefficientModules`, `finiteCoefficientRealization`:
  the finite coefficient realization explains the ordinary fixed-ring module encoding;
  the current node explicitly asks for ordinary constant-A module sheaves.
- def-weil-size-convention: the explicit scheme/site/coefficient universe binders.
  This is a size convention and introduces no extra datum to choose or redefine.
- def-weil-pbc-site-comparison-morphism: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`; its ordinary functors and adjunction are
  the upstream `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction`.
- def-weil-pbc-inverse-image: upstream
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.upperStar` and
  `Etale.upperStarLowerStarAdjunction`, identified with open restriction by the open-unit API.
- def-weil-proetale-inverse-image: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `Scheme.proEtaleSheafInverseImage`; its canonical open restriction identification
  is reused through the recorded open-unit module and its upstream restriction functors.
- lem-weil-pbc-comparison-pullback:
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
  `supportSiteComparisonCoefficientPullbackIso`, transported to restriction form by gamma.
- lem-pur-comparison-pullback-open-unit:
  `Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit`,
  `comparisonPullbackOpenUnitGamma`, `comparisonPullbackOpenUnitC`,
  `comparisonPullbackOpenUnit`; the full signatures and their construction were read.
- def-sp-injective-resolutions: Mathlib `CategoryTheory.Injective`, with its extension
  property, and `InjectiveResolution`; the latter's N-indexing is not used to exclude
  arbitrary negative-degree terms. Instead the same defining conditions are imposed
  on the integer-indexed Plus complex, exactly as in the recorded common-injective node.
- lem-weil-pbc-right-derived-plus-injective: Mathlib
  `Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  `Functor.rightDerivedFunctorPlus`, `Functor.rightDerivedFunctorPlusUnit`.
- lem-pur-support-comparison-common-injectives: `Sheaf.Paper.PuritySupportCommonInjectives`,
  `supportComparisonSource`, `supportComparisonAugmentation`,
  `supportComparisonDerivedResolutionMap`, `supportComparisonCommonInjectives`.

All stated proof-dependency modules are imported, directly or publicly through the two
statement imports; the restriction-injectives and Grothendieck modules are explicit
non-public proof imports. No proof-import cycle is introduced by this new module.
Sources checked in local literature: sites.tex lemma-localize-morphism (03CF), including
its sectionwise calculation; proetale.tex lemma-relative-comparison (099V) and
lemma-compare-derived (09B1), especially the bounded-below fixed-coefficient statements.

Edge cases checked before writing: empty V or empty T; j an identity; F=0; the zero
coefficient ring; a finite nonfield ring such as Z/4; resolutions having nonzero negative
terms and any lower bound. The signature imposes no nonemptiness, invertibility of a
characteristic, freeness, constructibility, or degreewise vanishing at negative indices.
The source iso and all equalities still type in these cases. Equalities of section
complexes cover the actual differentials, not only their induced homology.

Searches (2026-10-22):

- msearch.py leanfinder: "Open restriction of an etale proetale common injective resolution
  preserves its comparison unit augmentation and is natural in chain maps". Eight hits,
  including InjectiveResolution.isoRightDerivedObj_hom_naturality and
  InjectiveResolution.Hom.ι'_comp_hom'; generic resolution naturality, no full match.
- msearch.py loogle: "CategoryTheory.InjectiveResolution,
  CategoryTheory.Adjunction.unit_naturality". Zero hits for that combined name query.
- msearch.py grep: `comparison.*[Aa]ugmentation|[Aa]ugmentation.*[Rr]estrict`.
  Three augmentation-ideal hits; no sheaf comparison result.
- msearch.py leansearch: "The comparison between etale and proetale module sheaves
  commutes with restricting an augmented injective resolution to an open subscheme".
  Eight hits, mainly Scheme.Modules Zariski restriction; no full match.
- rg of lean/WeilConjectures and lean/Sheaf for this node id,
  `supportComparison.*[Rr]estrict`, `[Rr]estrict.*[Aa]ugmentation`: related general
  restrictions and Zariski/etale Cech resolutions, no statement of this node.
- Focused rg of Mathlib's Homology sources found
  `HomologicalComplex.singleMapHomologicalComplex`; this existing canonical construction
  is used for the degree-zero transport rather than duplicated.

No STATEMENT-DISPUTED issue found. Compilation is exclusively via the authorized
scompile.py wrapper; validation results are recorded below after the final dry run.

## Second reading by NO

The dispatcher explicitly prohibits starting another agent. This is a separate self-review
pass, not a claim of an independent worker review; the maintainer's independent delivery
review remains required. I reopened the node and complete generated signature and checked
all conjuncts against the displayed equations. In particular I checked the direction of
beta (gamma, not gamma inverse), the direction of the single/restriction source transport,
the order of compositions for theta and theta', the every-resolution quantifiers, the
absence of a nonnegative-degree restriction, and both evaluation/restriction-arrow clauses.
The canonical computation is fixed by its alpha equation, so its existential presentation
does not permit an unrelated isomorphism. The only elaboration repair was to give the
bounded-below source and target of the degree-zero f_V chain map explicitly; this changes
no mathematical hypothesis or conclusion. No node statement was changed.

Validation: scompile.py compiled the final module in sandbox mode (16.5 s) and library
mode (17.2 s), with no errors or unexpected warnings. The prescribed deliver2.py
--no-push completed successfully: `OK (dry run): commit 6473ecaabe5 passes the preflight
and compiles; nothing pushed`. The packet contains exactly this node's Lean attachment,
its single module, and this report. No upstream file or launcher script was edited.
