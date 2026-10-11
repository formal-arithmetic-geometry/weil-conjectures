## Worker report

The module `Sheaf.Topology.RestrictInjectiveResolution` states
`AlgebraicGeometry.RingedSpace.restrict_injectiveResolution`. Its only theorem proof
is `sorry`; there are no new definitions, dependency modules, or statement corrections.

Hypothesis and clause correspondence:

- Ringed space X: `(X : RingedSpace.{u})`, Mathlib's sheafed space of commutative rings,
  with no assumption that its stalks are local rings.
- Open subspace U: `(U : Opens X)`. The localized open site `Over U` is equivalent
  to the open-subset site of U: an object is an open V of X equipped with V ≤ U.
  Its restricted ring sheaf `(moduleRings X).over U` is precisely O_U.
- O_X-module F: `(F : SheafOfModules.{u} (moduleRings X))`.
- Given injective resolution F → I: `(I : InjectiveResolution F)`. This is the
  recorded Mathlib N-indexed cochain complex, with injective terms and a
  quasi-isomorphism `I.ι` from F concentrated in degree zero.
- Restriction: `R := SheafOfModules.overFunctor.{u} (moduleRings X) U`, the
  existing restriction functor; it acts by retaining sections on opens inside U.
- The restricted augmented complex is an injective resolution: the first conjunct
  supplies `J : InjectiveResolution (R.obj F)` and an equality `h` of its entire
  complex with `(R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex`.
  Thus the objects AND differentials are the termwise restrictions, not merely
  an unrelated injective resolution of the restricted module.
- The augmentation is the original restricted augmentation: the equality
  `J.ι.f 0 ≫ eqToHom (congrArg (fun K => K.X 0) h) = R.map (I.ι.f 0)`
  identifies the maps after transport along the equality of target complexes.
  The degree-zero source of `single₀` is definitionally F. At every positive
  degree its source is zero, so all other components are uniquely determined.
- In particular every I^n|_U is injective: the second conjunct is
  `∀ n : ℕ, Injective (R.obj (I.cocomplex.X n))`, explicitly including n = 0.

Dependency declarations read and used:

- `def-weil-locally-ringed-space-morphism`: its Mathlib match is
  `AlgebraicGeometry.LocallyRingedSpace.Hom` in
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`; the needed ringed-space
  clause is `AlgebraicGeometry.RingedSpace` in `Mathlib.Geometry.RingedSpace.Basic`,
  alias of `SheafedSpace CommRingCat`, not the locally ringed specialization.
  No morphism of locally ringed spaces is needed here.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` and its morphisms in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, preserving the exact module notion.
- `def-sp-injective-resolutions`: `CategoryTheory.InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, and
  `CategoryTheory.Injective` in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
- `lem-sc-ringed-space-module-sheaves-enough-injectives`:
  `AlgebraicGeometry.RingedSpace.moduleSheaves_abelian_enoughInjectives` in
  `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`, imported directly.
  Its imported `Sheaf.Paper.DerivedHomMayerVietoris` supplies the existing
  `AlgebraicGeometry.moduleRings` and the additive open-restriction instance.
- Mathlib `SheafOfModules.overFunctor` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `CategoryTheory.Functor.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`
  supply restriction of modules and complexes. No private copies were introduced.

Source verification: the local literature checkout is absent, so I opened
https://stacks.math.columbia.edu/tag/01E1. Part (1) states preservation of injectives;
the proof of part (2) explicitly states that a restricted injective resolution
is an injective resolution. Its proof uses the exact extension-by-zero left adjoint,
matching the node's three proof steps, which the theorem docstring carries.

Edge cases checked: U empty, U = X, X empty, F zero, resolutions with zero terms,
and degree n = 0. None is excluded by a binder or requires a nonempty hypothesis.
The localized-site description remains valid on the empty open; the sheaf condition
forces its modules to be zero. The equality of complexes ensures the differential
and augmentation data are retained even in degenerate cases. The universe u is
explicit and arbitrary, as in the recorded module-category dependency; increasing
it accommodates larger spaces, rings, and module sheaves. No field, characteristic,
Noetherian, scheme, or locality hypothesis was added.

Searches (actual tool calls recorded in searches.jsonl):

- LeanFinder: "Restriction of an injective resolution of sheaves of modules to an
  open subset is an injective resolution". Eight hits concern generic injective
  resolutions, degreewise injectivity, and sheafification; none is this restriction theorem.
- Loogle: `CategoryTheory.InjectiveResolution, Functor`: zero hits.
- Mathlib grep: `injective.*restrict|restrict.*injective|mapInjectiveResolution`:
  hits are unrelated restriction of algebraic maps; no ringed-space resolution theorem.
- LeanSearch: "injective resolution restriction sheaves modules open subset":
  service unavailable (Internal Server Error); no inference from this unavailable search.
- `rg` over both `WeilConjectures` and `lean/Sheaf` for
  `injective.*restrict|restrict.*injective|lem-sc-ringed-space-restrict-injective-resolution`:
  found etale/scheme-specific results and unrelated injectivity assertions, no exact match.
- Read `Sheaf.Paper.DerivedHomMayerVietoris` and searched project topology/paper
  modules for `restrict|moduleRings`: found the existing ring sheaf and restriction
  infrastructure, reused rather than defined again.
- Read Mathlib `SheafOfModules.overFunctor`, `Functor.mapHomologicalComplex`,
  `CochainComplex.single₀`, `InjectiveResolution` and `Injective` signatures and docstrings.
  The former two implement exactly the termwise restriction used in the statement.

No `STATEMENT-DISPUTED` issue or node fault was found. Server compilation completed
without errors or warnings (2.1 seconds). Independent second reading is left to the
second worker, as required by the brief.


## Second reading by M1

I independently opened the delivered node and Lean module, all four statement
 dependency nodes, their recorded Mathlib declarations, and the landed
`RingedSpaceModuleEnoughInjectives` and `DerivedHomMayerVietoris` modules.
There are no new nodes, dependency modules, or statement corrections to review.
No mismatch was found; no Lean or node field was changed. This section records
my independent reading rather than relying on the first worker's conclusions.

Source: the repository has no Stacks checkout. I fetched the actual Stacks
`cohomology.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex
into this item's sandbox, and read lines 483–533, including the section introduction,
`lemma-cohomology-of-open`, and its complete proof. The lemma introduces only a
ringed space and an open subspace; no preceding locality hypothesis is assumed.
Part (1) asserts preservation of injectivity, and the proof of part (2) explicitly
asserts that the given restricted augmented complex is an injective resolution.
The source uses the exact extension-by-zero left adjoint in the same orientation
as the node. Thus the node itself agrees with the cited source.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

1. Ringed space X: `(X : RingedSpace.{u})`. The dependency
   `def-weil-locally-ringed-space-morphism` defines ringed spaces in its first
   clause, before adding stalk-locality for locally ringed spaces. I read
   `AlgebraicGeometry.RingedSpace` in Mathlib `Geometry/RingedSpace/Basic.lean`:
   it is `SheafedSpace CommRingCat`. Using this clause requires neither
   `LocallyRingedSpace` nor its `Hom` structure. The rings are commutative,
   exactly as in that dependency, with no field or scheme hypothesis.
2. Open subspace U: `(U : Opens X)`. Objects of `Over U` are opens V with an
   inclusion V ≤ U; their morphisms and open covers are precisely those of
   opens in the subspace U. I also read `GrothendieckTopology.over` in Mathlib
   `CategoryTheory/Sites/Over.lean`: covering sieves are pulled back along
   the forgetful equivalence of sieves. Thus the localized site describes
   the same open subspace, including its sheaf condition.
3. O_X-module F: `(F : SheafOfModules.{u} (moduleRings X))`. I read
   `SheafOfModules`, `SheafOfModules.Hom`, and `moduleRings` themselves:
   the underlying presheaf of modules is an abelian sheaf, its restrictions
   are semilinear, and morphisms are sectionwise linear. `moduleRings` simply
   forgets commutativity of the given structure sheaf, retaining its rings
   and restrictions. This uses the recorded sheaf-module notion.
4. Given injective resolution F → I: `(I : InjectiveResolution F)`. I read
   `CategoryTheory.InjectiveResolution` in the dependency's recorded file:
   `cocomplex` is N-indexed, `injective` asserts injectivity in every degree,
   and `ι` is a quasi-isomorphism from `single₀ F`. This is the dependency's
   recorded interpretation of the augmented resolution in the node; no
   particular resolution is selected and no additional instance is assumed.
5. Restriction of the given complex: `let R := SheafOfModules.overFunctor.{u}
   (moduleRings X) U`. I read its definition as `pushforward (𝟙 _)`, which
   retains the module sections over opens contained in U. Its target rings
   are `(moduleRings X).over U`, hence O_U. I read `mapHomologicalComplex`:
   its objects are `R.obj (I.cocomplex.X n)` and its differentials are
   `R.map (I.cocomplex.d i j)`. The existential equality `h` identifies J
   with this entire complex, not just its cohomology or its terms.
6. Restricted augmentation and resolution property: J is an
   `InjectiveResolution (R.obj F)`, and
   `J.ι.f 0 ≫ eqToHom (congrArg (fun K => K.X 0) h) = R.map (I.ι.f 0)`.
   The transport has direction J^0 → R(I^0), so this is the original
   restricted augmentation. I read `CochainComplex.single₀_obj_zero` and
   `fromSingle₀Equiv`: the source in degree zero is definitionally F,
   and a map out of `single₀ F` is determined by its degree-zero component.
   Consequently the equality specifies the entire augmented complex.
   Existence of such J states a resolution structure on that complex;
   it neither weakens to an unrelated resolution nor asks for extra data.
7. Each restricted term injective: the second conjunct is
   `∀ n : ℕ, Injective (R.obj (I.cocomplex.X n))`. It explicitly includes
   degree zero and every term of the given resolution. The node's order
   of quantification is preserved: arbitrary X, U, F, and I precede J and h.

The fourth dependency's declaration
`RingedSpace.moduleSheaves_abelian_enoughInjectives` states exactly abelianness
and enough injectives for this module category, as its node says. Its import
provides the already landed additive restriction instance; additivity and
abelianness are supplied infrastructure, not extra binders. All notions are
existing Mathlib/project notions, with no private or hollow definition here.

Edge cases: U empty, U = X, X empty, F the zero sheaf, zero terms, and n = 0
are admitted. There is no index family or nonempty requirement. The localized
site still models opens of the empty subspace. Rings of all characteristics,
including the zero ring, are admitted. The arbitrary universe u accommodates
the space, rings, and module values in a common universe as in the landed
`moduleRings` dependency; independently sized data can be placed in a common
larger universe. No unbound term variable or additional universe appears in
the signature, and no locality, Noetherian, finiteness, or field instance is added.

Independent searches (actual calls appended to searches.jsonl):

- LeanFinder: "An exact restriction functor on module sheaves carries an injective
  cochain resolution to an injective cochain resolution". Eight hits concern
  generic resolutions and K-injectivity; no ringed-space restriction result.
- Loogle: `SheafOfModules.overFunctor`. Three hits: the existing restriction
  functor, its composition iso, and the scheme-specific comparison with
  `Scheme.Modules.restrictFunctor`; none states this theorem.
- LeanSearch: "open immersion inverse image preserves injective sheaves of
  modules". Service returned Internal Server Error; recorded unavailable.
- Mathlib grep: `overFunctor|preservesInjective|injectiveResolution` in
  `Algebra/Category/ModuleCat`. Found the restriction infrastructure and an
  unrelated module-universe lift preserving injectivity, not this theorem.
- Independent `rg` of `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for resolution/open/overFunctor combinations,
  `restrict_injectiveResolution`, and restricted injectivity found no exact
  match. I opened `Etale.injective_upperStar_obj_of_etale`: it concerns
  constant-coefficient sheaves on small etale sites of schemes, not modules
  over an arbitrary ringed space; it is not a substitute for this node.

H5–H9 checks: the module contains no definition and just one theorem with
`sorry` proof. Both docstrings identify Stacks 01E1 and the correct blueprint
id; the theorem docstring carries all three proof steps with their dependency
ids. Imports supply the module/ring/restriction infrastructure and the resolution
structure. Namespace, header, and line widths meet the conventions. I checked
programmatically that `lean.statement` is verbatim the delivered theorem
signature up to `:=`. No correction or disputed statement is needed.

Second-reader verification: `scompile.py M1
lem-sc-ringed-space-restrict-injective-resolution` compiled the delivered module
on the server in 2.2 seconds, exit 0, with no errors or warnings.
