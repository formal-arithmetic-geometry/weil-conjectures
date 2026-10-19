## Worker report

The module states `CategoryTheory.siteConstantMorphism_local`, with `sorry` as the entire
proof. It introduces no definitions or new nodes and changes only the item's `lean` record.
The source is Stacks Project, Modules on Sites, Tag 093S (3), applied to each slice.
The source's final object is the identity object of that slice, so no final object of the
original category is needed.

Hypotheses and clauses:

- The small site is `{C : Type u} [SmallCategory C]`, with `J : Precoverage C` and
  `J.HasIsos`, `J.IsStableUnderComposition`, `J.IsStableUnderBaseChange`, `J.HasPullbacks`.
  These are exactly the site convention of def-weil-pbc-sites-and-cohomology. Covering
  sieves belong to `J.toGrothendieck`. As in the node's first proof step, choose one universe
  containing the site and coefficients: `B : Type u`, `M N : ModuleCat.{u} B`. Smaller
  presentations can be lifted to this common universe; no fixed universe is imposed.
- The commutative ring is `[CommRing B]`; the two B-modules are `M N`. The sole finiteness
  assumption is `[Module.Finite B M]`. There is no finite-presentation assumption on M
  and no finiteness assumption on N or B.
- The constant sheaves and their morphism are the displayed `constantSheaf` objects in
  `Sheaf J.toGrothendieck (ModuleCat B)` and the binder `φ` between them. This uses the
  module-valued constant-sheaf encoding explicitly prescribed by the recorded
  lem-weil-pbc-site-constant-restriction. A B-module-valued sheaf has the canonical
  constant-ring-sheaf action: locally represent a scalar section by b in B, act by b,
  and glue. Morphisms are precisely the morphisms linear for that action: B-linearity
  implies linearity for locally constant scalar sections locally, hence globally by
  separatedness; the reverse follows on constant scalars. Thus these are the stated
  constant ring module sheaves, with the same morphisms, not arbitrary abelian sheaves.
- `U : C` is arbitrary, and `∃ S ∈ J.toGrothendieck U` gives its covering sieve.
- `∀ ⦃V : C⦄ (g : V ⟶ U), S g → ...` quantifies over every arrow of that sieve.
- `(⊥ : Sieve V) ∉ J.toGrothendieck V` is exactly the exception for an object covered by
  the empty sieve. It is a premise only for this member, not a global site restriction.
- `∃ f : M ⟶ N` supplies the B-linear map. The equality compares restriction of `φ`
  with `(constantSheaf (J.toGrothendieck.over V) (ModuleCat B)).map f`, using on either
  side the `.hom.app` of `Functor.pushforwardContinuousSheafificationCompatibility`
  at the appropriate constant presheaf. These canonical isomorphisms have the unit
  compatibility and naturality recorded in the restriction dependency. Restriction
  itself is `J.toGrothendieck.overPullback ... V`, i.e. sectionwise restriction along
  `Over.forget V`.
- There are no point, terminal-object, connectedness or nonemptiness assumptions.

Dependency declarations read and used:

- Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck: `Precoverage.toGrothendieck`,
  with the site classes from the sites-and-cohomology record.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `CategoryTheory.constantSheaf`.
- Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`.
- Mathlib.CategoryTheory.Sites.Over: `GrothendieckTopology.over`, `overPullback`, and the
  continuous/cocontinuous instances of `Over.forget`.
- Mathlib.CategoryTheory.Sites.CoverLifting:
  `Functor.pushforwardContinuousSheafificationCompatibility` and its unit equation
  `Functor.toSheafify_pullbackSheafificationCompatibility` (the latter used in the
  natural-language proof, not added as a theorem here).
- Read Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation of `SheafOfModules`; and the localized-site Mathlib match
  `SheafOfModules.over`, `Hom.over`, `overFunctor`, `overMap`, `overFunctorMap` in
  Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous. For the constant
  modules the restriction dependency gives the equivalent ModuleCat-valued encoding
  used here; no replacement ringed-site category or module structure is defined.
- Proof dependencies imported without `public`: Sheaf.CategoryTheory.SiteCoveringsCommonRefinement
  (`Precoverage.siteCoverings_finite_common_refinement`),
  Sheaf.Paper.SiteSheafificationSectionsLocal (`sheafification_sections_local`), and
  Mathlib.CategoryTheory.Sites.PreservesSheafification (underlying-set comparison).
  Mathlib's sheafification and its unit are already public through ConstantSheaf.

Searches performed:

- msearch.py leanfinder, query "A morphism between constant module sheaves with finitely
  generated source is locally a linear map": eight finite-type/local-generator hits;
  none state this theorem.
- msearch.py loogle, query "constantSheaf, Module.Finite": no hits; unknown identifier
  constantSheaf in that search service.
- msearch.py grep, query "constantSheafOverHom|exists_mem_forall_exists_linearMap": no
  Mathlib hits.
- rg in WeilConjectures for that expression found ConstantSheafSections and
  ConstantSheafOver and their consumer ConstructibleSheaf/KernelCokernel. Read the full
  upstream signatures/docstrings. In particular
  `exists_mem_forall_exists_constantSheafOverHom_comp_map_eq` has extra HasWeakSheafify
  and WEqualsLocallyBijective premises, explicitly rejected by the item's split report.
  This delivery states the small-site version without those premises. It uses the
  already recorded slice comparison, rather than defining another comparison.
- rg in lean/Sheaf/CategoryTheory for constantSheafOverHom and constant module/morphism
  patterns found no matching theorem. The upstream search for the blueprint item id
  had no hits.

Edge cases: the zero module permits zero generators and the identity covering; a site
with empty coverings has the stated memberwise exclusion, so it never forces injectivity
of the constant unit there. The empty category has no U, hence the universally quantified
statement applies vacuously. Disconnected objects allow a different f on each member.
Infinite N, infinite B, and finitely generated but not finitely presented M remain allowed.
All relations are checked using unit injectivity rather than finite presentation.

Compilation: scompile.py on the server completed cleanly in 1.3 seconds, nice 19, two
threads, with the standard 60-second per-file limit. The initial instance failures were
resolved by importing ModuleCat limits and filtered colimits and using the node's common
universe convention; no typeclass assumptions were added. No local compiler was run.
No statement correction or disputed mathematical clause is needed.

## Second reading by NY

I independently read the node, all six statement-dependency records, the Lean
module, Stacks sites-modules.tex lemma-morphism-locally-constant (093S), and the
upstream ConstantSheafOver declaration. The source assumes a final object X;
on C/U this is the identity of U. Its third clause concerns finite-type source
modules, not finitely presented ones. The node specializes the source to already
constant modules and commutative coefficients, and explicitly permits degenerate
cover members. No correction of the node is necessary.

Object/hypothesis/conclusion inventory and matching:

- Small site C: `{C : Type u} [SmallCategory C]`, `J : Precoverage C`, and
  `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`, `HasPullbacks`.
  These are precisely the sites-and-cohomology record's encoding. Covering sieves
  are measured in `J.toGrothendieck`. Verdict: exact.
- Commutative ring B: `{B : Type u} [CommRing B]`. No field, characteristic,
  Noetherian or finite-ring requirement. Verdict: exact.
- Two B-modules M,N: `(M N : ModuleCat.{u} B)`; finite generation only of M:
  `[Module.Finite B M]`, whose definition is finite generation of the top
  submodule. N is arbitrary; finite presentation is not required. Verdict: exact.
- Constant module sheaves: the two objects of `constantSheaf J.toGrothendieck
  (ModuleCat B)`. I read constantSheaf's definition: it is the constant
  presheaf followed by presheafToSheaf. This is the module-valued encoding
  expressly used by the constant-restriction dependency. Its B-action extends
  canonically to the constant ring sheaf: represent scalar sections locally by
  elements of B, act locally, and glue. Conversely, restriction to constant
  scalars gives the B-action. Thus the morphism binder `φ` describes exactly
  constant-ring-linear maps: B-linearity gives linearity on local scalar
  representatives and separatedness gives it globally. This is compatible
  with the recorded ringedSiteModules = SheafOfModules abbreviation, which I
  also opened, rather than a new definition. Verdict: exact.
- Arbitrary U: `(U : C)` follows φ. There is no terminal-object, point,
  connectedness, or nonempty-site binder. Verdict: exact.
- Covering sieve: `∃ S ∈ J.toGrothendieck U`. It may depend on φ and U.
  Verdict: exact.
- Every member arrow: `∀ ⦃V : C⦄ (g : V ⟶ U), S g → ...`.
  No choice of just generating cover members is substituted. Verdict: exact.
- Exception: `(⊥ : Sieve V) ∉ J.toGrothendieck V` is a premise for each
  member only; it is not imposed globally. Verdict: exact.
- Locally inducing linear map: `∃ f : M ⟶ N` follows those premises,
  allowing f to depend on the member. ModuleCat morphisms are B-linear.
  Verdict: exact.
- Restricted-map equality: the displayed square says comparison(M) followed
  by `overPullback.map φ` equals the slice `constantSheaf.map f` followed by
  comparison(N). I opened Over.lean: overPullback is sectionwise restriction
  via Over.forget, and over topology has precisely the underlying covering
  sieves. I opened CoverLifting.lean lines 382–411: the displayed comparison
  is a natural isomorphism and toSheafify_pullbackSheafificationCompatibility
  is its unit equation. These are the exact declarations recorded for
  lem-weil-pbc-site-constant-restriction. Verdict: exact, with the correct
  direction and both canonical comparisons.

Edge cases: M = 0 permits the zero-generator identity cover; N = 0 and the
zero ring are allowed. A site with empty covers retains the memberwise
exception; no injectivity is asserted at a degenerate member. If C is empty
there is no U. A disconnected object can have different f on different cover
members. No degree n or scheme-specific restriction occurs. The universe u
is bound, not fixed: it is a common universe for the small site and all
coefficients, as the node's proof explicitly prescribes; smaller presentations
can be lifted to it. There is no equality between two independently specified
site object/morphism universes. All other variables are explicitly bound.

Independent searches used different phrasing: LeanFinder, "A homomorphism of
constant sheaves of modules of finite type becomes a constant homomorphism
after passing to a covering sieve", returned eight constant/condensed-sheaf
hits, none this arbitrary small-site theorem. Loogle, `"constantSheaf",
"Module.Finite"`, returned zero hits. Mathlib grep,
`constant.*(finite|generated)|finite.*constant` in CategoryTheory/Sites,
returned zero hits. I also searched the project's Sheaf modules and upstream
Sites modules for constantSheafOverHom, exists_mem_forall_exists_linearMap,
and the delivered declaration name. The upstream ConstantSheafOver theorem
uses the abstract HasWeakSheafify/WEqualsLocallyBijective interface and the
adjunction-defined comparison; it is the node's cited source, not the recorded
small-site statement with the recorded Mathlib comparison. I read its full
signature and the construction of its comparison rather than relying on its
name. No second definition is introduced here, and no exact recorded
statement has been duplicated.

No new nodes or dependency modules are included, and there is no
statement_change. The proof docstring follows all five node steps: canonical
restriction comparison; finite generator/common cover construction; unit
injectivity away from empty covers; all relations checked simultaneously;
equality throughout the slice by local representatives and separatedness.
The one theorem is left wholly sorry, with no definitions, auxiliary axioms
or proved facts. No mismatch required a Lean or node edit; I added this
independent reading and its search evidence only. I verified programmatically
that lean.statement is verbatim the theorem signature. Server scompile.py
accepted the sole module in 1.3 seconds, nice 19, two threads, 60-second limit,
without diagnostics.


## Maintainer correction of the existing-declaration audit

This correction supersedes the Worker report and Second reading by NY conclusions
that the upstream theorem has unavailable extra assumptions and is not an exact
existing statement. Their clause-by-clause mathematical reading of the delivered
statement remains valid, but the H4 conclusion was incorrect.

The existing declaration is
`CategoryTheory.exists_mem_forall_exists_constantSheafOverHom_comp_map_eq` in
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`, lines 130–156.
It quantifies over an arbitrary T, not a final object. In the common universe
specified by the node, all three sheafification premises are automatically inferred.
A server-only scompile.py input using #synth for ambient HasWeakSheafify,
WEqualsLocallyBijective and slice HasWeakSheafify, and #check of the theorem applied
to J, T, M, N and φ, succeeded without any such premise being assumed.
Imports used were the upstream module, PreservesSheafification, ModuleCat limits
and filtered colimits, and Sites.LeftExact. The check completed in 1.6 seconds,
nice 19, two threads, 60-second limit. This is an instance check, not a new proof.
The original immutable delivered file also reproduced cleanly in 1.3 seconds.

The two displayed comparisons coincide by the sheafification universal property:
upstream toSheafify_constantSheafOverHom_hom (lines 79–89) and Mathlib
Functor.toSheafify_pullbackSheafificationCompatibility (CoverLifting.lean:391–411)
say their composites with the slice constant-presheaf unit are the same restricted
ambient unit. Their domain and codomain are the same sheaves, and this unit
uniquely determines a sheaf morphism. Thus the different expressions for the
comparison do not justify restating the theorem. Both encode constant B-module
sheaves, with the canonical action of the constant ring sheaf. No arbitrary map
is introduced.

The replacement lean record has existing: true, branch slopmaster2, the exact
source signature, and a note explaining the specialization and inferred instances.
merge_delivery.py --stage 2 --apply-fixes automatically omits the now-unowned
SiteConstantMorphismLocal.lean when a record is switched to existing: true.
There is no mathematical statement correction, new node, missing prerequisite,
universe restriction, dependency repair, or downstream citer change. All six
statement dependencies and the node's proof remain unchanged.
