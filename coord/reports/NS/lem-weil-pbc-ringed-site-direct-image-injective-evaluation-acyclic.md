## Worker report

The module `Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic` states
`CategoryTheory.ringedSite_directImage_injective_evaluation_isZero`, with `sorry` as
its entire proof. It introduces no definitions or instances and changes only the
item's `lean` record. Source read: `literature/stacks-project/sites-cohomology.tex`,
labels `lemma-direct-image-injective-sheaf` (072Z) and `lemma-limp-acyclic` (0731),
including the former's proof and its explicit warning that flatness is needed for
preservation of injectives, but not for the asserted evaluation acyclicity.

Hypothesis and conclusion correspondence:

- Small sites C and D in a common universe: `{C D : Type u}`, `[SmallCategory C]`,
  `[SmallCategory D]`; precoverages `J`, `K`, each with `HasIsos`,
  `IsStableUnderComposition`, `IsStableUnderBaseChange`, `HasPullbacks`.
  Their generated Grothendieck topologies have exactly the covering-family sheaves.
  This is the encoding specified in def-weil-pbc-sites-and-cohomology's record.
- The continuous functor u presenting f is `F : C ⥤ D`. `hcover` says a covering
  presieve maps to a covering presieve. `hpullback` says F preserves the pullback
  of each covering arrow with every arrow to the same target. These are exactly
  Stacks 00WV(a),(b), following the recorded general-site convention. The
  `[F.IsContinuous ...]` instance expresses their consequence on sheaves so the
  pushforward is typeable; it does not impose a new condition.
- The condition that this continuous functor presents a morphism of sites is
  `[PreservesFiniteLimits (sheafPullback F (Type u) ...)]` and
  `[PreservesFiniteColimits (sheafPullback F (Type u) ...)]`, as specified in the
  site-definition record (00X1). The functor is Mathlib's Kan-extension and
  sheafification pullback, not an arbitrary chosen inverse image.
- The sheaves of rings are `R : Sheaf J.toGrothendieck RingCat.{u}` and
  `S : Sheaf K.toGrothendieck RingCat.{u}`. No commutativity is imposed.
- The structure map is `rho : R ⟶ (F.sheafPushforwardContinuous RingCat ...).obj S`.
  `SheafOfModules.pushforward rho` is Mathlib's actual construction: its sections
  at U are I(F(U)), with scalar restriction through rho at U. Thus the object in
  the conclusion is the specified direct image, not an arbitrary object with
  assumed vanishing or injectivity.
- Both module categories having enough injectives is the two explicit
  `[EnoughInjectives (ringedSiteModules.{u} R)]` and corresponding S binders.
  Mathlib's abelian and injective-resolution structures are inferred on these
  small sites; `Grp.FilteredColimits` supplies the needed sheafification instances.
- `I : ringedSiteModules.{u} S` and `[Injective I]` state injectivity on the source,
  with no injectivity assumption on its direct image or underlying abelian sheaf.
- Every object U is the unrestricted binder `(U : C)`. Positive integer degrees
  are `(q : ℕ) (hq : 0 < q)`: positive integers and positive naturals correspond
  bijectively, and Mathlib's injective-resolution right derived functors use ℕ.
- The additive left exact evaluation functor to Ab is exactly
  `SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
  (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)`.
  Its objects are the abelian groups P(U) and its maps are component maps.
  Forgetting scalars precedes evaluation but derivation is of this composite
  functor on the MODULE category. It is not evaluation derived on abelian sheaves.
- `IsZero ((... .rightDerived q).obj ((SheafOfModules.pushforward rho).obj I))`
  states precisely the vanishing in Ab. `rightDerived` computes homology of the
  evaluation of an injective MODULE resolution. The conclusion is one vanishing
  assertion, without extra clauses. No flatness binder appears.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H'`
  and `cohomologyPresheafFunctor`, used in the proof plan through the imported
  vanishing criterion. `CategoryTheory.Precoverage`, its four site classes,
  `Precoverage.toGrothendieck`, `Sheaf`, `sheafSections`, `Functor.IsContinuous`,
  and `Functor.sheafPushforwardContinuous` from the site-definition record are
  used directly or through the explicit evaluation composite. Their actual declarations and the existing
  `SiteContinuousPushforwardSheaf`/`SiteMorphismComposition` conventions were read.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the dependency's transparent abbreviation for `SheafOfModules`, used for I
  and both module categories. The full abbreviation and its docstring were read.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`;
  `...Injective.Resolution`: `InjectiveResolution`. The former is explicit; the
  latter is the resolution construction underlying Mathlib `rightDerived`.
- Mathlib `SheafOfModules.forget`, `PresheafOfModules.toPresheaf`, functor-category
  `evaluation`, and `SheafOfModules.pushforward` in `Algebra.Category.ModuleCat.Sheaf`,
  `ModuleCat.Presheaf` and `Sheaf.PushforwardContinuous`; their definitions were
  read to check sections, arrows and the scalar structure. This explicit evaluation
  composite uses existing additivity instances; no new instance is introduced.
- Proof-only imports include `Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic`
  (`CategoryTheory.injective_module_cech_cohomology_isZero`) and
  `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
  (`CategoryTheory.Sheaf.isZero_H'_of_siteCech_vanishing`), both read with docstrings.
  `SiteCechComplex` is already public through these modules; abelian sheafification
  and locally bijective characterizations are available through Mathlib imports.
  The proof dependency
  `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` has no Lean record
  yet, hence no module import can be added for it. It is named in the proof docstring;
  no replacement comparison is invented.

Edge cases checked before writing: the zero injective module gives zero positive
cohomology; empty sites make the object assertion vacuous; empty covering families
are allowed by precoverages and impose the usual zero sections at such objects.
Degree one is included, degree zero is excluded as required (sections need not
vanish). Identity site functors and arbitrary nonflat ring maps remain admissible:
restriction of scalars does not need to preserve injectives for this assertion.
Rings, module values, object and arrow types share universe u; no independently
smaller coefficient universe or additional finite-limit assumption on the entire
site excludes a case. Covering presieves can be indexed by the type of arrows of
that presieve, in u, so the covering-size restriction agrees with the node.

Searches for an existing statement (2026-10-15):

- `msearch.py leanfinder`: "Direct image of an injective sheaf of modules on a
  ringed site has vanishing positive right derived evaluation at every object".
  Eight hits, including `Functor.isZero_rightDerived_obj_injective_succ`,
  `CochainComplex.isKInjective_of_injective` and injective-resolution results.
  None gives acyclicity of the module pushforward without assuming it injective.
- `msearch.py loogle`: `SheafOfModules.pushforward, CategoryTheory.Functor.rightDerived`:
  zero hits.
- `msearch.py grep`: `(pushforward|directImage).*(acyclic|injective)|(acyclic|injective).*(pushforward|directImage)`
  in `Algebra/Category/ModuleCat`: zero hits.
- `msearch.py leansearch`: "Direct image injective sheaves of modules acyclic for
  sections on ringed sites": service unavailable (Internal Server Error).
- `rg` on the upstream `WeilConjectures` and project `lean/Sheaf` for direct image,
  injective evaluation and acyclicity: existing results concern schemes, opens,
  or étale coefficient categories, in particular
  `Scheme.Modules.module_pushforward_injective_acyclic`; its full signature was
  read and it does not cover arbitrary ringed sites. No equivalent general result.
- `grep -rn` for this exact node id in upstream `WeilConjectures`: no match.
  `rg` for the proposed declaration name in `dag/lean_names_upstream.json`, upstream
  and `lean/Sheaf`: no existing declaration with this name.

No statement correction, new node, dependency module, or disputed statement.

Validation: `scompile.py NS lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic <module>`
passed cleanly on the server, nice 19, two threads, 60 seconds per file.
The module compiled in 1.3 seconds; its side-only RingedSiteModules dependency
compiled separately in the private overlay in 0.9 seconds. No local compiler or
global build was run.


## Second reading by NS

I independently read the node, all three statement dependency records and their
actual declarations, the delivered module, and Stacks sites-cohomology.tex,
lemma-direct-image-injective-sheaf (072Z) and lemma-limp-acyclic (0731)(1).
The source allows arbitrary ringed topoi; the node selects the small-site,
continuous-functor presentation used in the proof of 072Z. I also read sites.tex,
definition-continuous (00WV) and definition-morphism-sites (00X1), and the
site-definition dependency's explicit encoding convention. No source-wide
flatness, commutativity, characteristic, finiteness or nonemptiness condition
is being suppressed.

Object, hypothesis and conclusion checklist (each verdict: exact):

- Small sites C and D: `{C D : Type u}`, `[SmallCategory C]`,
  `[SmallCategory D]`, precoverages J and K with all four site instances.
  These are the dependency's recorded site notion, not categories assumed to
  have every pullback or a terminal object. Generated-topology sheaves are the
  covering-family sheaves under this convention.
- The common universe for objects, arrows, coefficients and cover indices:
  the bound `universe u`, SmallCategory, `RingCat.{u}`, `ringedSiteModules.{u}`
  and `AddCommGrpCat.{u}` implement exactly the explicit node restriction.
  Presieves are sets of arrows in u and admit u-small family presentations;
  there is no independently smaller universe or hidden universe equality.
- The continuous functor presenting f: `(F : C ⥤ D)`, `hcover` and
  `hpullback` encode 00WV(a),(b). Preservation of `cospan f g` is precisely
  the canonical covering-pullback comparison being invertible. The site
  instances supply those pullbacks. `F.IsContinuous` is the consequence
  ensuring precomposition preserves sheaves, not an additional mathematical
  restriction; this is also the recorded dependency convention.
- That f is a morphism of sites: the finite-limit and finite-colimit
  preservation instances on the set-valued `sheafPullback` encode 00X1.
  I read its construction: inclusion, left Kan extension, sheafification,
  with its adjunction to continuous pushforward. It is the canonical inverse
  image and introduces no arbitrary choice of functor or stronger condition.
- Sheaves of rings: R on C and S on D have type `Sheaf ... RingCat.{u}`.
  These are rings, with no commutativity or field assumption.
- Structural map: `rho : R ⟶ (F.sheafPushforwardContinuous ...).obj S` has
  exactly the node's direction. I read both module pushforward definitions:
  `PresheafOfModules.pushforward₀` precomposes by F.op and `pushforward`
  then restricts scalars along rho; `SheafOfModules.pushforward` keeps this
  data with the induced sheaf proof. Thus `(f_*I)(U) = I(F.obj U)` with the
  specified rho_U action, rather than an unconstrained substitute.
- Both module categories have enough injectives: precisely the two
  `EnoughInjectives (ringedSiteModules.{u} ...)` instances. The transparent
  dependency abbreviation is Mathlib's `SheafOfModules`; its objects and
  morphisms are module presheaves with the abelian sheaf condition and
  sectionwise linear natural maps. Its abelian instances impose no extra
  mathematical assumption on these small sites.
- Injective source module: `(I : ringedSiteModules.{u} S) [Injective I]`.
  I read `Injective.factors` and `InjectiveResolution`: extension along every
  mono, and an N-indexed complex of injectives with the required augmentation
  quasi-isomorphism. No injectivity is assumed of the direct image or of its
  underlying abelian sheaf.
- Every object and every positive degree: `(U : C) (q : ℕ) (hq : 0 < q)`.
  Positive integers are exactly positive naturals, with no degree omitted.
  U and q are unrestricted after I as required.
- Evaluation as an additive left exact functor from MODULES to Ab:
  `SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
  (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)`.
  Reading the two forgetful constructions confirms its object is P(U) and
  its map is the component homomorphism; derivation is applied to the entire
  composite, so resolutions are taken in the module category.
- The single vanishing clause is `IsZero ((... .rightDerived q).obj
  ((SheafOfModules.pushforward rho).obj I))`. Mathlib's rightDerived and
  InjectiveResolution.isoRightDerivedObj identify this with homology of
  evaluation of an injective module resolution. Nothing is weakened to
  vanishing of a different cohomology theory. No flatness hypothesis occurs.

Edge cases: empty sites are allowed (the U-quantifier is then vacuous);
empty covering families are not forbidden; zero rings and zero injective
modules are allowed. Degree one is included and degree zero is intentionally
excluded, because sections need not vanish. Identity functors and nonflat
ring maps remain allowed. There is no scheme or nonempty-scheme binder and
no characteristic restriction. The bound u is explicit and covers every
common universe permitted by the node.

Independent duplicate searches used different wording: msearch leanfinder
"Higher section cohomology of pushforward of an injective module sheaf
vanishes without a flat ring map" returned eight hits, including K-injective
and sheaf cohomology declarations, but no matching assertion. Loogle
`SheafOfModules.pushforward, CategoryTheory.Functor.rightDerived` returned
zero hits (an earlier query using unqualified IsZero was unresolved and is
not relied on). msearch grep `rightAcyclic.*pushforward|pushforward.*rightAcyclic`
returned zero hits. Direct rg of Mathlib's ModuleCat files, upstream
WeilConjectures and the project's lean/Sheaf for pushforward/direct-image
and injective/acyclic found only special cases and other assertions.
I opened `Scheme.Modules.module_pushforward_injective_acyclic` in
Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic: its schemes and
open-subscheme sections exclude general sites. The topological pushforward
injectivity results are for abelian sheaves, also not this statement.
Thus the delivered statement is not a second definition or existing result.

There are no new definition nodes, dependency modules or statement_change
in this delivery. I checked the available proof dependency signatures and
imports, and the four-step proof docstring against the node: covering Cech
comparison, injective-module Cech vanishing, the site vanishing criterion,
and module/abelian derived-evaluation comparison. The comparison and two
sheafification nodes have no recorded Lean module locally and are named in
the proof plan rather than replaced with private constructions. They are
proof dependencies, not missing objects needed to type this statement.

Mismatches found: none. Changes: appended this independent second reading;
Lean and the node record are unchanged. There are no definitions, local
notations or local instances, and the only theorem proof is `sorry`.
The source/blueprint docstrings contain the node's proof step by step.
I checked that every universe and variable is bound and that lean.statement
is verbatim the theorem signature in the file.
