## Worker report

This delivery states `sk-lem-sf-flat-model` in
`lean/Sheaf/SixFunctors/FlatModel.lean`. It contains five theorems, all with `sorry`
proofs, and two fully written predicates spelling out this node's closure-generator
formulas. There are no new DAG nodes or dependency-node changes. The item's only changed
field is `lean`; its mathematical statement, dependencies and proof remain unchanged.
The current blueprint unit, main-20261015, was read in full alongside the DAG statement
and all seven proof steps. No statement correction or dispute is needed.

The retained earlier attempt compiled but did not state the full node. I replaced it:
its pro-etale flat model omitted termwise constructibility; its stratification omitted
projectivity; it gave only etale generation, omitting pro-etale generation and the
first paragraph's equality; and its predicates did not use the current recorded
constructibility and intrinsic Tor interfaces. Its second-reading paragraph described
those obsolete files, so it has been removed. The independent second reader should
review the rewritten statements below.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Standing field `k = Fbar_q` | `D : WeilConjectures.FiniteFieldDatum.{u}`, with its actual `D.k`, field structure and algebraic-closure data |
| The standing prime `ell != p` | `l : ℕ`, `hl : l.Prime`, `hlp : l ≠ D.p` in each first-paragraph theorem |
| A finite commutative ring annihilated by a power of ell | `A : Type u`, `[CommRing A] [Finite A]`, `hA : ∃ n, 0 < n ∧ (l ^ n) • (1 : A) = 0`; killing 1 kills every element, so this is annihilation of the ring |
| X finite type over the standing field | `[X.Over (Spec (.of D.k))]` with `LocallyOfFiniteType` and `QuasiCompact` of its structure morphism |
| Ordinary pro-etale module sheaves and their unbounded derived category | `proEtaleRingModules X (proEtaleConstantRing X A)` and the recorded `proEtaleDerivedCategory X A`; this is neither a completed category nor an etale-origin subcategory |
| Bounded constructible cohomology | `hbc`: every `DerivedCategory.homologyFunctor` value satisfies `IsConstructibleProEtaleModuleSheaf`, and it vanishes outside some ordered integer interval |
| Finite Tor amplitude | The recorded `HasFiniteProEtaleTorAmplitude X A K`; its interval tests every module sheaf in degree zero using the recorded K-flat derived tensor, not only constant or constructible test modules |
| Bounded complex representing every such K | `proEtaleFlatModel`: a `CochainComplex ... ℤ`, an ordered pair `a b`, `IsZero (P.X q)` outside `[a,b]`, and `Nonempty (K ≅ DerivedCategory.Q.obj P)` |
| Flat constructible terms | Both `SheafOfModules.IsFlatOnSite ... (P.X q)` and `IsConstructibleProEtaleModuleSheaf X A (P.X q)` for every q; flatness means exactness of sheaf tensor, not sectionwise module flatness |
| Finite stratification of a flat constructible sheaf | `proEtaleFlatStratification`: the same standing hypotheses, `F`, `hF`, `hflat`, and `∃ str : LocallyClosedStratification X` |
| Locally constant restrictions with finite projective local models | For every stratum an actual pro-etale covering `U,f`, and for every cover member a `ModuleCat (ULift A)` object `M` with `Finite M`, `Module.Projective (ULift A) M`, and a module-sheaf isomorphism from the actual coefficient pullback restricted to `U` to `proEtaleConstantModuleSheafOver ... M` |
| Finite projective means a summand of finite free | A finite set M is finitely generated over the finite ring; finite generation plus `Module.Projective` is precisely being a direct summand of finite free. This permits nonfree projectives and varying modules on different cover members. |
| Locally closed extension by zero | Both `sf...ClosureGenerators` use the actual `str.immersion i`, its `Scheme.Hom.image` and `imageι`, an open `j` into that image, and `j ≫ imageι = str.immersion i` |
| L is lisse with flat stalks | Etale generators use `IsFiniteLocallyConstantSheaf L` and `ObjectProperty.flat L`; pro-etale generators use the existing `IsLisseProEtaleFixedModuleSheaf` of the canonical realization inverse and `SheafOfModules.IsFlatOnSite L`. Flatness of module sheaves is equivalent to stalk flatness here. For finite local models over a finite ring, flatness is equivalent to projectivity. |
| The generator a_!L = g_*j_!L | `DerivedCategory.singleFunctor ... 0` of the ordinary open extension by zero followed by the closed direct image along the canonical `imageι`. The pro-etale expression uses the exact canonical `sfIntrinsicModuleEquivalence` to transport these actual module functors and their scalar actions. No arbitrary equivalence, coefficient map or compactification is supplied as a hypothesis. |
| Rg_*j_!L in the complement | On degree-zero inputs closed direct image is exact, hence `g_*j_!L[0]` represents precisely `Rg_*j_!L`. The node's proof steps 6--7 explicitly make this identification on both sites. No higher derived direct image is discarded. |
| First paragraph: generated using shifts, finite extensions and direct summands | `proEtaleThickGeneration_eq`: the anonymous object property of bounded constructible cohomology and finite Tor amplitude equals `(sfProEtaleClosureGenerators X A).triangEnvelope`, with the same standing hypotheses as the model. This includes both containments. |
| Noetherian complement: general finite ring and general Noetherian X | Both `proEtaleThickGeneration` and `etaleThickGeneration` use `[IsNoetherian X]`, arbitrary finite commutative A, and no field, invertible-exponent, separatedness or compactification hypothesis |
| Complement property formulation | `P : ObjectProperty ...`, `[P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]`, `hP : sf...ClosureGenerators X A ≤ P`, and conclusion `P K` for the stated bounded-constructible finite-Tor input |
| Complement on either small site | Separate pro-etale and etale theorems. The etale one uses the recorded `DerivedCategory.isBoundedConstructible` (finite constant module values) and the recorded `hasTorAmplitudeIn`, with one ordered interval for every test sheaf. |

The two generator predicates are helper declarations of this node, listed in
`lean.declarations`, spelling out the generator sets already introduced by its own
statement. Their data are the displayed existential formulas, not `sorry`. They do not
introduce another stratification, constructibility, Tor, sheaf, or extension functor.
Using the scheme-theoretic image fixes the closure convention exactly; merely prescribing
an arbitrary closed immersion with the same underlying image was not used. On a Noetherian
scheme every locally closed immersion can occur as a stratum of a finite stratification:
use its image, the closed boundary inside its closure, and the open complement of that
closure (omit or retain empty pieces). Thus these generator predicates also cover all the
locally closed `a_!L` of the first paragraph, not only a predetermined stratification.

Dependency declarations inspected and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, including all field
  and algebraic-closure fields and instances.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and its jointly
  surjective covering-family characterization; `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `Scheme.ProEt.topology` and the weakly etale small site, reached by the recorded module.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`,
  the intrinsic constant-ring `SheafOfModules` derived category; this module is imported
  directly, rather than substituting the source's fixed-module derived category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`; the
  cohomology and triangulated structures are those of this localization.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: the re-exported bounded
  `Etale.DerivedCategory.hasTorAmplitudeIn`; the new lower-bounded variant is unnecessary.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`: `Scheme.HasProEtaleTorAmplitude` and
  `Scheme.HasFiniteProEtaleTorAmplitude`, read in full including the representative,
  K-flat-resolution and all-module-sheaf quantifiers.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`; the bounded cohomological use is the existing
  `Etale.DerivedCategory.isBoundedConstructible` from
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`.
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`: the recorded module publicly
  re-exports `Sheaf.Paper.ProEtaleConstructibleSheaf` and its original
  `Scheme.IsConstructibleProEtaleModuleSheaf`. The delivered pro-etale statements use this
  small-coefficient specialization, which is exactly compatible with the recorded
  Tor predicate, rather than substituting the newer Type-(u+1) coefficient presentation.
  The site object universe stays u+1 and the morphism universe stays u throughout.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, and `IsNoetherian`, whose
  fields are local Noetherianity and quasi-compactness (`CompactSpace`).
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification`, with finite disjoint locally closed parts,
  actual stratum schemes, immersions and their image equalities. No constructibility or
  frontier condition is silently added to this data.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`, the actual sheafified extension presheaf.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `ProEtale.openImmersionLowerShriek`, read from the current source through
  `scompile.py --source` because this reorganized module is absent from the old source
  checkout. It is `localizationLowerShriek`, definitionally sheafification of the left
  Kan extension along the opposite localization functor.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`, `imageι`,
  `toImage` and the factorization equation; `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
  supplies openness of `toImage` for quasi-compact immersions. The generator formulas
  refer to this actual scheme-theoretic image.
- Existing canonical transports and auxiliary predicates are reused from
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
  (`sfIntrinsicModuleEquivalence`), its intrinsic-realization dependency,
  `Sheaf.Paper.ProEtaleLisseOrigin` (`IsLisseProEtaleFixedModuleSheaf`), and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` (`SheafOfModules.IsFlatOnSite`).
  The projective local model uses the recorded constant coefficient pullback and
  `proEtaleConstantModuleSheafOver`, including its actual module action.

All presently stated proof dependencies' modules are imported non-publicly: the finite-value
etale flat model, exact comparison pullback, comparison flatness, finite-ring constructible
origin, short-exact-sequence triangles, immersion/image factorization, etale recollement,
pro-etale ringed recollement, and the exact/derived-functor comparison. The three elementary
Noetherian facts, `det-pe-finite-tor-comparison-noetherian`, and
`det-sf-flat-model-generation` currently have no `lean` record and are not stated here;
they remain the node's existing proof obligations. Every theorem docstring follows the
node's relevant numbered proof steps, names their cited nodes, and gives the finite
filtration/stupid-tail inductions; no source theorem is used beyond its statement.

Edge cases checked before rewriting:

- Zero ring: the annihilator condition holds; zero modules are finite projective, so
  none of the clauses implicitly assumes `Nontrivial A`.
- Empty scheme and empty strata: `LocallyClosedStratification` allows an empty partition;
  a one-empty-stratum partition also works. Covers of the empty scheme may be empty;
  empty trivializing members may use M = 0. No nonempty-index assumption occurs.
- Zero complex and a one-term complex: an ordered singleton interval suffices, and
  `IsZero` outside the interval includes zero terms without choosing literal zero objects.
- Cohomological boundedness alone does not imply finite Tor amplitude: `hTor` is separate
  and uses the same interval for all ordinary module sheaves.
- Finite projective local modules need not be free: no constant-rank or freeness
  hypothesis was introduced. Different strata and cover members can have different models.
- A general Noetherian scheme in the complement need not be separated or finite type over
  a field. Neither theorem adds these hypotheses. A stratum's canonical closure may carry
  nilpotents; `Hom.image` retains the scheme-theoretic closure, not an arbitrary reduction.
- Site sizes are unchanged: pro-etale objects live in Type (u+1), morphisms in Type u,
  module values in Type (u+1). Small finite coefficient rings use the recorded `ULift`
  on scalars, rather than forcing equality of site object and morphism universes.

Searches actually run in this resumption:

- `msearch.py ... leansearch "A bounded constructible complex with finite Tor amplitude on
  a pro-etale site has a bounded complex of flat constructible module sheaves as a
  representative, and flat constructible sheaves stratify into locally constant finite
  projective modules."`: 8 hits, headed by `Module.Flat.of_projective`,
  `Module.isLocallyConstant_rankAtStalk` and generic sheaf finite-presentation/generator
  results. No flat constructible model, finite projective sheaf stratification or
  two-site generation result was returned.

- `msearch.py ... leanfinder "A finite Tor amplitude constructible complex has a bounded
  flat constructible model and is thickly generated by locally constant finite projective
  sheaves on strata"`: 8 hits, including `SheafOfModules.LocalGeneratorsData.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`, `DerivedCategory.IsGE`,
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, and generic condensed/module results.
  None gives the model plus projective strata and generation on the two sites.
- `msearch.py ... loogle "DerivedCategory, IsConstructibleSheaf"`: service returned zero
  hits with `unknown identifier 'IsConstructibleSheaf'`; this is an unusable query result,
  not evidence of the absence of constructible sheaves from the project.
- `msearch.py ... grep "flatConstructible|ctfGenerators|IsFiniteLocallyConstantSheaf"`:
  zero Mathlib hits for that query.
- `rg` in `WeilConjectures/` for `sk-lem-sf-flat-model` found the existing flat-model
  modules and the constructible-presentation input. The full signatures/docstrings of
  the etale and pro-etale flat-model theorems and the etale generation theorem were read.
  The pro-etale theorem lacks constructible terms, projective strata, and generation;
  the etale theorems alone do not state this node. The existing finite-value etale flat
  model is imported for the proof rather than restated in this delivery.
- `rg` of source/project for projective local-model/lisse predicates found site-perfect
  complex statements, not this sheaf stratification statement. `rg` of Mathlib,
  `WeilConjectures/` and `lean/Sheaf` for each delivered full declaration name found no
  existing declarations before the rewrite. Searches of the project's existing intrinsic
  realization, constructibility, Tor, flatness, and extension-by-zero interfaces led to
  the reused declarations listed above, rather than private substitute definitions.

Validation: the original file compiled but was rejected by this worker's mathematical
check. The rewritten module compiled cleanly through `scompile.py` after fixing explicit
site arguments for flatness and importing Mathlib's triangulated-generator API. The final
signature/import version is compiled again by the required dry delivery; the wrapper
reports compilation and preflight results. No library/global build or direct git command
was run, and no shared or upstream file was edited.


Dry-run repair: the first preflight on the rewritten file found the metadata signature's
trailing `:=` and the expected missing independent second-reading section. I removed only
that delimiter from `lean.statement` to match the preflight signature extractor. The Lean
statement itself is unchanged. The wrapper had compiled both sandbox and library forms
cleanly; the preflight reported no mathematical-file, line-width, import or declaration
shape defect. The prescribed no-push command is rerun for the final record.

Resumption after the worktree-slot failure (2026-10-16): I reread the retained module,
the current node, all statement-dependency records and the declarations used in the
statement, and the current blueprint unit. No further mathematical or Lean changes were
needed. In particular, Mathlib's `ObjectProperty.triangEnvelope` explicitly includes
retracts as well as shifts and finite extensions, so the equality is the requested thick
generation statement. The original small-coefficient constructibility predicate is
publicly re-exported by the dependency's new coefficient-universe module; it remains the
interface matching the recorded Tor predicate. I checked that the sandbox node differs
from the current shared node only in `lean`, that `lean.statement` exactly matches the
main declaration's signature, and that every Lean line is at most 100 characters.
The prescribed `scompile.py` completed both the sandbox and library forms with no warnings
or errors (46.7 s and 17.7 s respectively). All five theorem proofs remain `sorry`.

Fresh searches in this resumption: LeanSearch for "A bounded constructible finite Tor
amplitude complex has a bounded flat constructible representative and is generated by
lisse projective sheaves extended from strata" returned eight general bounded-complex,
flat/projective-module and finite-presentation hits, with no matching sheaf-model or
generation theorem. LeanFinder for "Finite Tor amplitude constructible complexes admit
bounded flat constructible models and thick generation by finite projective lisse sheaves
on locally closed strata" returned eight bounded-derived-category and sheaf-presentation
hits, none stating this node. Loogle `DerivedCategory, Module.Projective` returned zero
hits. The Mathlib grep `flatConstructibleModel|proEtaleFlatModel|ctf_generated_by` returned
zero hits. Direct source grep by the blueprint id found the existing etale and pro-etale
model statements and the etale generation theorem; their signatures were read and have
the interface differences already described above. The current pro-etale open lower-shriek
definition was read again using `scompile.py --source` and is the canonical localization
left Kan extension followed by sheafification. The final dry run is performed with this
updated report; independent second reading remains for the next worker.

## Second reading by Q12

Independent review, 2026-10-16. I read the current DAG statement and all seven
proof steps, the complete main-20261015 unit statement, and the delivered Lean
side by side. The sandbox node differs from the shared node only in `lean`;
there is no `statement_change`, new definition node, or dependency-node repair.
The following is my object/hypothesis/conclusion inventory and its check against Lean.

| Node object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| The standing algebraic closure of a finite field, of characteristic p | `D : WeilConjectures.FiniteFieldDatum.{u}`. I opened `FiniteFieldFiber.lean`: its fields give a prime p, positive exponent, finite base field of the specified cardinality, and `IsAlgClosure D.k₀ D.k`. Correct. |
| The standing prime ell distinct from p | `l`, `hl : l.Prime`, `hlp : l ≠ D.p` in the three first-paragraph declarations. Correct; these are standing coefficient conventions, not hypotheses on the general complement. |
| A finite commutative ring killed by a power of ell | `A`, `[CommRing A] [Finite A]`, and `hA`. Annihilation of 1 annihilates every element. Requiring a positive exponent is equivalent, including the zero ring (which is also killed by ell). Correct. |
| X finite type over that standing field | `X : Scheme.{u}`, `[X.Over (Spec (.of D.k))]`, `LocallyOfFiniteType` and `QuasiCompact` on its structure map. These encode finite type and allow nonseparated schemes. Correct. |
| Ordinary pro-etale sheaves of modules over the constant ring, and their unbounded derived category | `proEtaleRingModules X (proEtaleConstantRing X A)` and the recorded `proEtaleDerivedCategory X A`. I opened the derived-category and Tor modules; their scalar sheaf and `HasDerivedCategory.standard` are the same localization. No completed or etale-origin subcategory is substituted. Correct. |
| Input in Dctf: bounded constructible cohomology | `hbc` requires the recorded `IsConstructibleProEtaleModuleSheaf` on every homology object and vanishing outside one ordered integer interval. The recorded coefficient-universe module publicly re-exports this original small-coefficient predicate. Its definition uses actual coefficient pullback, finite locally closed constructible strata, local constancy, and finite geometric stalks. Correct. |
| Input in Dctf: finite Tor amplitude | `hTor : HasFiniteProEtaleTorAmplitude X A K`. I read its full definition: one ordered interval works for all ordinary module sheaves, all isomorphic representatives, and all K-flat resolutions. Thus the test is neither limited to lisse sheaves nor allowed a different interval for each test. Correct. |
| Every such K has a bounded representative | `proEtaleFlatModel` supplies a cochain complex P, an ordered interval, zero terms outside it, and `Nonempty (K ≅ DerivedCategory.Q.obj P)`. Correct orientation and existential order; the node does not require the model's interval to be the particular supplied Tor interval. |
| Every term is flat and constructible | Separate universal conjuncts use `SheafOfModules.IsFlatOnSite` and `IsConstructibleProEtaleModuleSheaf` on `P.X q`. I opened `FlatOnSite.lean`: flatness is exactness of the sheaf tensor functor. Correct; sectionwise flatness is not assumed. |
| A flat constructible sheaf has finite projective local models on finite strata | `proEtaleFlatStratification` quantifies F with its two hypotheses, then `∃ str : LocallyClosedStratification X`. For every stratum it gives an actual pro-etale covering and a model M on every cover member, with `Finite M`, `Module.Projective (ULift A) M`, and an isomorphism of module sheaves to the constant model. I read the stratification structure, constant-module construction and pullback interfaces. Finite modules over a finite ring are finitely generated, so projective here means a summand of finite free, as required. Correct; no global freeness or common model is imposed. |
| Locally closed extension by zero through scheme-theoretic closure | Both `sf...ClosureGenerators` quantify an actual stratum immersion, an open j into its `Hom.image`, and the equation `j ≫ imageι = immersion`. Mathlib defines `image` as the subscheme of the kernel ideal and `imageι` as its closed inclusion. The equation fixes the factor; monicity of the closed inclusion makes it unique. Correct. |
| L locally constant with finite projective models / lisse with flat stalks | The pro-etale predicate uses `IsLisseProEtaleFixedModuleSheaf` after the inverse canonical realization, together with intrinsic sheaf flatness. I read its definition: local constancy and finite geometric stalks. The etale predicate uses `IsFiniteLocallyConstantSheaf` and `ObjectProperty.flat`. For these finite local models, finite flat is finite projective, and flatness is stalkwise. Correct. |
| Generators a_!L and Rg_*j_!L | The definitions use the existing open lower-shriek followed by closed lower-star, placed in degree zero. The pro-etale formula transports along `sfIntrinsicModuleEquivalence`, whose data come from the specified realization functor's equivalence, not an arbitrary choice. Exact closed direct image identifies this with Rg_*j_!L; the Noetherian hypothesis ensures the required retrocompact complement on the pro-etale site. Correct. |
| Equality with the category generated by shifts, finite extensions and summands | `proEtaleThickGeneration_eq` equates the entire bounded-constructible finite-Tor object property with the generators' `triangEnvelope`. I opened Mathlib's generator API: it includes shifts, finite binary products, retracts and finitely many extensions, with isomorphism closure. Binary products are already finite extensions via split triangles. Both containments are asserted. Correct. |
| General Noetherian base and arbitrary finite commutative coefficients | `proEtaleThickGeneration` and `etaleThickGeneration` require only `[IsNoetherian X]` and finite commutative A. I checked Mathlib: `IsNoetherian` extends local Noetherianity and `CompactSpace`. No prime, field, invertible exponent, separatedness or supplied compactification occurs. Correct. |
| The complement holds on either small site | The two separate generation theorems cover both sites. The etale theorem uses the recorded finite-value `DerivedCategory.isBoundedConstructible` and existing `hasTorAmplitudeIn`, which tests every module sheaf in degree zero. Correct. |
| Property formulation of thick generation | P is arbitrary, with `IsTriangulated`, `IsStableUnderRetracts`, `IsClosedUnderIsomorphisms`; `hP` assumes every specified generator and the conclusion is `P K`. Correct quantifier order and all three closure conditions. |

Source checks: Stacks `etale-cohomology.tex`, `section-ctf` (0F4M) and
`lemma-when-ctf` (03TT), explicitly assume a Noetherian coefficient ring and
qcqs X for the flat constructible representative. A finite ring is Noetherian;
the first-paragraph X and the complement X are Noetherian, hence qcqs. I also
read the standing ringed-site paragraph in `section-more-constructible` (095M),
`proetale.tex` `lemma-compare-constructible` (09AK), and
`lemma-closed-immersion-complement-retrocompact-exact` (09BM). These agree with
the proof docstrings' use of comparison and exact closed pushforward. No
hypothesis assumed throughout those source places is missing in this application.

Generator coverage: any locally closed immersion into a Noetherian X occurs as
one stratum of a finite partition. Add the closed boundary inside its closure
and the open complement of that closure, giving three locally closed parts
(with empty pieces allowed), rather than incorrectly treating the complement
of a locally closed subset as a single locally closed part. Thus using strata
in both predicates loses none of the first paragraph's locally closed a_!L.

Edge cases: the zero ring is allowed (`Nontrivial` never occurs); the zero
complex is covered by a singleton interval; arbitrary integer bounds permit
negative and zero degrees. Empty schemes and empty covering indices are
allowed. More precisely than the worker report's empty-partition sentence,
the reused pro-etale constructibility predicate requires a positive number
of strata: on the empty scheme one empty stratum witnesses it. The output
stratification itself can have zero strata. The generator set remains nonempty
also on the empty scheme by taking one empty stratum and L = 0. Projective
models can be nonfree and can vary with the covering member. The complement
allows coefficients of any characteristic. The standing clause allows every
ell distinct from p, including the zero-ring exponent-zero case via a positive
exponent. All variables and universes are explicitly bound. Site objects and
module values are in u+1, site morphisms in u; no equality of these universe
levels is imposed. The pro-etale small coefficient universe is the recorded
interface, while the etale interface permits coefficients in u+1. Any finite
coefficient ring can be represented in the smaller universe; this is a size
presentation, not a restriction to a class of finite rings.

Independent searches (run in this reading, with different wording):

- LeanFinder: `Constructible finite flat dimension sheaf complex admits finite flat constructible resolution and generation by locally constant projective strata`. Eight hits: generic sheaf finite-presentation/local-generator definitions, formal smoothness flatness, and `Module.Flat.projective_of_finitePresentation`; none states the node.
- LeanSearch: `The bounded constructible finite Tor dimension category is the thick envelope of locally closed extensions of finite locally constant projective sheaves`. Eight hits: projective dimension, condensed objects and finite limits/colimits of sheaves; none matches.
- Mathlib grep through `msearch.py`: `finite.*projective.*strat|flatConstructible|ctf_generated`; zero hits.
- Direct `rg` on Mathlib, upstream `WeilConjectures/`, and the project's `lean/Sheaf/` for projective stratification and all new generator/model/generation names found no exact statement or generator predicate. Upstream blueprint-id searches located the existing pro-etale flat-model theorem and etale generation theorem; I opened both complete signatures. The former omits constructibility of terms. The latter uses the upstream constructibility and stratification interfaces, arbitrary closures with set-range constraints, and derived compactification lower-shriek. It is not the node's recorded-interface formulation with canonical scheme-theoretic closure. The existing finite-value etale model is reused as an import. No complete match warrants dropping this module.

I independently read the current pro-etale open lower-shriek module through
`scompile.py --source`: the construction is left Kan extension along the
opposite localization functor followed by sheafification, exactly the recorded
dependency. I also opened the etale open lower-shriek and direct-image
signatures. Both helper predicates have real existential formulas; all five
named theorem proofs are exactly `sorry`. Their docstrings carry source,
blueprint id, and the relevant numbered proof steps, including the sheaf
filtration, the explicit stupid-tail triangle induction, closure factorization,
and reverse containment. No private definition, local notation or hollow data
was introduced. The node's `lean.statement` agrees verbatim with the main
signature, excluding the proof delimiter as required by preflight.

Mismatches and changes: no mismatch requiring a Lean or DAG change was found.
I retained the worker's correct statements and added only this independent
review, clarifying the positive-stratum empty-scheme case. The first compiler
invocation used the repository working directory, so its relative sandbox
path was not found; I reran the prescribed wrapper from the actual sandbox.
Validation and delivery results follow below.

The independent `scompile.py Q12 sk-lem-sf-flat-model
lean/Sheaf/SixFunctors/FlatModel.lean` run passed both sandbox and library
forms (43.7 s and 26.1 s), with no errors or warnings. A separate source check
confirmed exact metadata-signature equality, no Lean line over 100 characters,
and exactly five named theorems with five whole-proof `sorry`s.
