## Worker report

The module `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage` defines
`AlgebraicGeometry.RingedSpace.derivedModuleDirectImage`, the unbounded derived direct image
for a general morphism of commutative ringed spaces. No proof was supplied. Three named
proof obligations have `sorry`: `moduleDirectImage_additive_proof`,
`resolvedModuleDirectImage_inverts`, and
`derivedModuleDirectImage_computed_by_resolution`. Their docstrings carry the complete
natural-language arguments and the item's blueprint tag. No definition has postponed data.
No statement correction, new node, dependency repair, or disputed statement is needed.

Clause-by-clause correspondence:

- The arbitrary ringed spaces `(X,O_X)` and `(Y,B)` are `X Y : RingedSpace.{u}`;
  the map `(g,g-sharp)` is `g : X ⟶ Y`. It is a sheafed-space morphism:
  `g.hom.base` is the continuous map and `g.hom.c` its structure-sheaf morphism.
  No local-ring condition, scheme hypothesis, or finiteness condition is imposed.
- The two abelian categories are `SheafOfModules.{u} (moduleRings X)` and
  `SheafOfModules.{u} (moduleRings Y)`. The open sites are `Opens X` and `Opens Y`.
  They are small in universe u; the standard sheafification instances supply
  the Abelian structures. The shared carrier `moduleRings` forgets commutativity
  only in order to use Mathlib's sheaves of modules.
- `moduleDirectImage g` specializes `SheafOfModules.pushforward`, with site functor
  `Opens.map g.hom.base` and sheaf map
  `Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)`.
  Reading Mathlib's `pushforward` and `PresheafOfModules.pushforward` shows its
  value at V is the module of sections over the inverse image of V; scalars
  restrict along exactly g-sharp. Restrictions are those of the original sheaf,
  and maps have component the original map at the inverse-image open.
  These are the existing constructions, not a separate sectionwise copy.
- `moduleDirectImage_additive_proof` states additivity, registered by the global
  instance `moduleDirectImage_additive`. `mapHomologicalComplex (ComplexShape.up ℤ)`
  is its termwise action on integer-indexed complexes. Mathlib's action of an
  additive functor on homotopies supplies the asserted preservation of homotopies.
- The localization functors are `DerivedCategory.Q`. The two explicit
  `HasDerivedCategory.{wX}` and `HasDerivedCategory.{wY}` instances choose the
  morphism sizes of the derived categories, exactly as the dependency's size
  convention allows; they impose no geometric hypothesis.
- `moduleGrothendieckAbelian` obtains the Grothendieck structure from the first
  conjunct of the recorded small-ringed-site resolution theorem. This permits
  reuse of the existing `CochainComplex.kInjectiveResolutionFunctor.{u}`;
  `CochainComplex.toKInjectiveResolution.{u}` is its natural quasi-isomorphism.
  Its objects are K-injective by the existing instance
  `isKInjective_kInjectiveResolutionFunctor_obj`. No second resolution construction
  is defined. Degreewise injectivity is not an additional requirement of this node.
- `resolvedModuleDirectImage g` is precisely I followed by termwise g-star and Q.
  `resolvedModuleDirectImage_inverts` states that this functor inverts all
  quasi-isomorphisms, with the node's two-out-of-three and homotopy-equivalence
  argument in its docstring.
- `derivedModuleDirectImage g` is `Localization.lift` of that actual functor
  using the named inversion theorem. This is a genuine functor on the whole
  unbounded derived category, with objects and maps supplied by Mathlib's
  localization equivalence, rather than chosen from an unconstrained existence
  assertion.
- `derivedModuleDirectImageFactorization` is the canonical natural isomorphism
  `Q ⋙ derivedModuleDirectImage g ≅ resolvedModuleDirectImage g`, obtained from
  `Localization.fac`. Its components render the formula Rg-star(QK) = Q(g-star I(K)),
  up to the canonical isomorphism inherent in localization. Its naturality renders
  the corresponding formula on every Q(f); it is not merely an objectwise assertion.
  Uniqueness of this factorization is Mathlib's localization universal property.
- For every `s : K ⟶ J` with `[QuasiIso s]` and `[J.IsKInjective]`,
  `derivedModuleDirectImage_computed_by_resolution` states the existence of an
  isomorphism from Rg-star(QK) to Q(g-star J). Its proof docstring spells out the
  comparison homotopy class and homotopy equivalence from the node. It does not
  restrict J to the chosen replacement or to bounded complexes.

Dependency declarations read and used:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom` (recorded match) was read together with
  `Mathlib.Geometry.RingedSpace.Basic` / `SheafedSpace` / `PresheafedSpace`.
  The dependency explicitly defines general ringed spaces and their morphisms
  as well as the locally ringed specialization; its general clause is Mathlib's
  `AlgebraicGeometry.RingedSpace` and `SheafedSpace` category. Using these avoids
  silently imposing the additional local-stalk hypothesis of the narrower match.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` (the dependency's
  general-site mathlib_match), and its Abelian instance. The dependency's
  `AlgebraicGeometry.Scheme.Modules` record is explicitly the scheme specialization;
  its note directs general ringed spaces to `SheafOfModules`, which is used here.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, and `QuasiIso` for resolutions.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective` and `quasiIso_iff` are the
  recorded comparison tools used in the postponed proof arguments.
- Shared representation: `AlgebraicGeometry.moduleRings`, imported from
  `Sheaf.Paper.DerivedHomMayerVietoris`, as required by the project convention.
- Existing resolution implementation:
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`,
  `CochainComplex.kInjectiveResolutionFunctor` and `toKInjectiveResolution`.
- Existing pushforward:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.pushforward`; localization: `Localization.lift` and `Localization.fac`.

Edge cases checked before writing: empty underlying spaces are allowed (no `Nonempty`);
zero sheaves and zero complexes cause no exception; all integer degrees occur, without
boundedness; identity morphisms and zero/terminal structure rings are allowed; no
hypothesis on stalks or characteristic is introduced; the two localization morphism
universes are explicit and independent. Any K-injective resolution, including one
not degreewise injective, is covered by the comparison statement.

Searches for an existing declaration (msearch.py outputs are also in searches.jsonl):

- LeanFinder: "derived direct image for a morphism of ringed spaces computed by
  K-injective resolution": eight hits, including `SheafOfModules.pushforward`,
  its natural transformations, and scheme pushforward; none defines the requested
  unbounded ringed-space derived functor.
- Loogle: `Functor.totalRightDerived, SheafOfModules.pushforward`: unknown identifier
  `Functor.totalRightDerived`, zero hits.
- Mathlib grep: `totalRightDerived|derivedPushforward|derivedDirectImage` in
  `Algebra/Homology/DerivedCategory`: three hits, all bounded-below derived functors.
- LeanSearch: "unbounded derived pushforward sheaves of modules ringed space":
  service unavailable (Internal Server Error); recorded as unavailable.
- rg in source `WeilConjectures/AlgebraicGeometry`: derived direct/pushforward searches
  find module-cohomology constructions whose docstrings explicitly say that the
  derived pushforward is unavailable. The exact blueprint id has no hits.
- rg in `lean/Sheaf`: no general ringed-space unbounded direct-image definition;
  moduleRings and restriction constructions exist and are reused. Search for
  resolution functors found the upstream generic functor, which is reused.
- Name collision check in `dag/lean_names_upstream.json`, Mathlib, and
  `WeilConjectures`: none of the new full declaration names is already present.

The cited local Stacks source is not present on this machine. Read the authoritative
[Tag 079W](https://stacks.math.columbia.edu/tag/079W) and the
[preceding construction in Tag 079V](https://stacks.math.columbia.edu/tag/079V)
via the web instead. The node describes that construction, not the adjunction theorem
itself; no correction is needed.

Validation: server single-file compile via scompile.py succeeded in 7.7 seconds,
with no errors or warnings. The delivery dry run is recorded below after completion.

Delivery dry run: `deliver2.py G1 def-pc-ringed-spaces-derived-direct-image --no-push`
printed `OK (dry run)` for commit `6e392fc01`: compiles and passes preflight except
for the independent second reading, which the second reader must supply. Nothing pushed.


## Second reading by G1

I independently read the item JSON and the complete delivered Lean file, all six
statement-dependency nodes, and the declarations below. No mathematical or Lean
mismatch was found; the module and node record are unchanged.

Source check: the repository has no local Stacks cohomology.tex. I fetched the
Stacks project's authoritative raw cohomology.tex into scratchpad/cohomology.tex
and read section-unbounded through lemma-adjoint, as well as
[079V](https://stacks.math.columbia.edu/tag/079V) and
[079W](https://stacks.math.columbia.edu/tag/079W). The standing assumptions are a
ringed space and arbitrary complexes of modules. The construction is immediately
before lemma-adjoint; 079W refers back to it, rather than itself defining direct
image. There is no Noetherian, scheme, boundedness, or finite-dimensional assumption.
The node deliberately uses commutative rings through its ringed-space dependency.

The node's objects, hypotheses and conclusion clauses, matched individually:

1. Two commutative ringed spaces and a ringed-space morphism:
   `X Y : RingedSpace.{u}` and `g : X ⟶ Y`. Verdict: exact. I read
   RingedSpace in Mathlib/Geometry/RingedSpace/Basic.lean, SheafedSpace's inherited
   category, and PresheafedSpace.Hom's `base` and contravariant `c` fields. The
   dependency's recorded LocallyRingedSpace.Hom is narrower than its general
   ringed-space clause; this file correctly uses the latter's existing
   SheafedSpace structure, with no local-stalk condition.
2. Abelian module categories on the small open sites:
   `SheafOfModules.{u} (moduleRings X)` and the analogous Y category. Verdict:
   exact. I read SheafOfModules and Hom in Mathlib's Sheaf.lean and its Abelian
   instance in Sheaf/Abelian.lean. The dependency's Scheme.Modules record is the
   scheme specialization; its mathlib_match explicitly supplies this general
   category. `moduleRings` in DerivedHomMayerVietoris is sheafCompose with the
   forgetful functor on X.sheaf, so retains the same ring operations.
3. Sections over inverse-image opens, their restrictions, scalars through
   g-sharp, and the componentwise action on maps:
   `moduleDirectImage g`, using `Opens.map g.hom.base` and
   `Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)`. Verdict: exact.
   I traced SheafOfModules.pushforward to PresheafOfModules.pushforward,
   pushforward₀Obj, pushforward₀, and restrictScalars. The first precomposes
   objects, restrictions and map components with the inverse-image functor;
   the last changes scalars along precisely the given structure-ring map.
4. Additivity, termwise application, and preservation of homotopies:
   `moduleDirectImage_additive_proof`, the corresponding global instance,
   and `.mapHomologicalComplex (ComplexShape.up ℤ)`. Verdict: exact.
   The standard additive-functor action on complexes supplies homotopy
   preservation; no exactness hypothesis is assumed on direct image.
5. The unbounded localization functors Q:
   `DerivedCategory.Q` on both module categories. Verdict: exact. I read
   DerivedCategory.Basic's HasDerivedCategory, standard choice, DerivedCategory,
   and Q.IsLocalization at HomologicalComplex.quasiIso. The explicit wX/wY
   instances represent chosen localization morphism sizes, not geometric
   restrictions, as allowed by def-weil-abstract-derived-category.
6. Functorial K-injective replacement K to I(K):
   `CochainComplex.kInjectiveResolutionFunctor.{u}` and its existing
   `toKInjectiveResolution`. Verdict: exact. I read the upstream definitions,
   monoQuasiIso_toKInjectiveResolution_app, and the K-injective object instance.
   `moduleGrothendieckAbelian` takes the first conjunct of the recorded
   grothendieckAbelian_and_functorial_kInjective_resolutions theorem; I read that
   theorem's complete signature and docstring. It applies to the small opens
   category with X.sheaf. This file reuses the upstream replacement rather
   than making a private existential choice. The node only needs K-injectivity,
   not degreewise injectivity of this chosen replacement.
7. Rg-star on objects and on Q(f):
   `resolvedModuleDirectImage` is I followed by termwise g-star followed by Q;
   `derivedModuleDirectImage` is its Localization.lift; and
   `derivedModuleDirectImageFactorization` is Localization.fac. Verdict: exact.
   I read lift and fac in Localization/Predicate.lean. Their natural isomorphism
   gives both the object formula and, by naturality, the morphism formula.
   The usual unique-up-to-isomorphism factorization is the localization
   universal property, rather than a literal equality of chosen objects.
8. Inversion of quasi-isomorphisms and well-definedness:
   `resolvedModuleDirectImage_inverts`. Verdict: exact. Its docstring follows
   the node: naturality and two-out-of-three, quasi-isomorphisms between
   K-injectives are homotopy equivalences, additive direct image preserves
   them, then Q inverts them. I read IsKInjective.quasiIso_iff and
   Qh_map_bijective in the recorded Mathlib KInjective module.
9. Every K-injective resolution computes Rg-star:
   `derivedModuleDirectImage_computed_by_resolution`, for every K, J and
   `s : K ⟶ J` with `[QuasiIso s] [J.IsKInjective]`. Verdict: exact. It asserts
   precisely Nonempty of the required isomorphism, with no restriction to
   the chosen replacement and no stronger claim about a selected comparison.
   The docstring follows the node's lift of QI(K) ≅ QJ to a homotopy class,
   homotopy equivalence, additive direct image, and defining factorization.

Edge cases: empty spaces are included; there is no Nonempty assumption on opens
or points. Zero sheaves, zero rings and zero complexes remain valid inputs.
Identity morphisms are allowed. All degrees are ℤ, including zero and negative
ones, with no boundedness condition. No characteristic or finiteness condition
occurs. The common arbitrary ambient universe u can contain both spaces and
rings after enlargement, as in the shared moduleRings convention; wX and wY
are independent localization sizes. No binder, variable, or universe is unbound.

Independent H4 searches, using different phrases:

- LeanFinder via msearch.py: "right derived functor of sheaf pushforward on
  unbounded complexes" returned eight hits: ordinary sheaf and module
  pushforwards and their coherence maps, no ringed-space derived specialization.
- Loogle via msearch.py: `SheafOfModules.pushforward` returned twelve hits,
  all ordinary pushforward, restriction, adjunction, or coherence declarations.
- LeanSearch via msearch.py: "unbounded derived direct image of modules on a
  ringed space" was unavailable (Internal Server Error), with no verdict claimed.
- Independent rg on project lean/Sheaf, upstream WeilConjectures and Mathlib
  derived-category modules, for derivedModuleDirectImage, moduleDirectImage,
  derivedPushforward, totalRightDerived and combinations of rightDerived and
  pushforward. The upstream generic Functor.rightDerivedFunctor in
  CategoryTheory/DerivedCategory/RightDerivedFunctor/Defs.lean was opened:
  it is an unbounded generic right-derived construction for additive functors,
  not the ringed-space module-direct-image specialization or its explicit
  functorial-resolution factorization. Other hits are scheme higher-direct-image
  functors (rightDerived q), bounded-below functors, or coefficient sheaves.
  No existing declaration realizes this whole definition node. The ordinary
  pushforward, replacement and localization constructions are all reused.

H5/H6/H8/H9: every definition's data comes from existing constructions, never
sorry. The three postponed obligations are named theorems, with source and
blueprint tags and full stepwise arguments. No theorem is proved in this delivery.
No private definition, file-local notation, local instance, or statement let/show
binder is introduced. All imports serve the ring-sheaf carrier, Grothendieck
structure, replacement, or K-injective comparison. No new node, dependency
module, or statement correction is present, so H12/H13 and citer rechecks
require no extra packet.

Validation: scompile.py with the absolute sandbox module path compiled the
115-line file on the server in 8.0 seconds, exit code 0, without any warnings.
The initial relative-path invocation could not open the file from the read-only
repository cwd; using the correct absolute sandbox path resolved it.
Second reading changed only this report; no Lean or node repair was needed.
