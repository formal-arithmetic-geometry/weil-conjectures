## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralEtaleDirectImageExact` states
`AlgebraicGeometry.Etale.integral_etale_direct_image_exact`, with `sorry` as its only
proof. No definitions, auxiliary nodes, or statement corrections were needed.

Hypothesis and clause correspondence:

- Schemes T', T and their morphism π: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Integrality, without finiteness or surjectivity: `[IsIntegralHom f]`, Mathlib's
  affine-local integral-ring-map predicate.
- Abelian sheaves on the small étale sites: `Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}`, and the corresponding category for Y. This is exactly the
  recorded abelian-sheaf dependency's size convention.
- Direct image π_*: the existing `AlgebraicGeometry.Etale.lowerStar
  AddCommGrpCat.{u + 1} f`, evaluating F at the base change of an étale object.
- Exactness: preservation of finite limits and finite colimits (the first conjunction).
  For this additive functor between abelian categories this is equivalent to preserving
  short exact sequences.
- R^qπ_*=0 for positive q: the second conjunction quantifies over every sheaf F and
  every `q : ℕ` and asserts `IsZero` of `(lowerStar ... f).rightDerived (q + 1)` on F.
  Every positive integer is represented uniquely by such a successor; this is
  objectwise vanishing of the positive right derived functors, not a bound on F.
- Rπ_*=π_* on D⁺: the last conjunction asserts invertibility of the actual existing
  `rightDerivedFunctorPlusUnit.app K` for every bounded-below homotopy object K.
  Its source is Qh of termwise π_*K and its target is Rπ_*QhK, by the full signature in
  Mathlib's `Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`. Thus this
  says that the canonical comparison is an isomorphism, as the node's final proof step
  specifies. Every bounded-below derived object has such a representative, and the
  localization universal property identifies the functors canonically. It does not
  assert an arbitrary unnormalized natural isomorphism or literal equality of choices.
- The finite-case sentence is an identification with a previously stated special case,
  not an additional assumption or independent mathematical conclusion. Its recorded
  module is imported and its relationship is documented in the theorem docstring.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Integral`, `AlgebraicGeometry.IsIntegralHom`;
  also read `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, its objectwise section formula and its additive
  and finite-limit-preservation instances.
- `Mathlib.CategoryTheory.Sites.Sheaf`, `CategoryTheory.Sheaf`, specialized exactly as
  the dependency record specifies; `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: its recorded docstring identifies
  D(T_et) with the derived category of the same abelian sheaves, and D⁺ with
  `DerivedCategory.Plus`. The module is publicly imported. The torsion predicate and
  coefficient-module version are irrelevant to the present statement.
- `WeilConjectures.SixFunctors.Finite.Exact`,
  `AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite` and
  `AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`.
  These require finiteness; they are not used to restrict the integral statement.

All recorded, stated proof-dependency modules are imported without `public`;
Mathlib proof dependencies are imported likewise. The docstring follows all six proof
steps: local surjective lifts; integral disjoint refinement; gluing and local epi
criterion; left exactness plus epi preservation; higher-derived vanishing using enough
injectives; canonical exact-functor bounded-below derived factorization. Étale
composition/cancellation is available through the site imports.

Edge cases checked: empty source or target schemes require no nonemptiness assumption;
an empty disjoint partition glues the unique zero section. Integral morphisms need not
be finite or surjective, and neither property occurs as a binder. Positive degrees start
at 1, leaving degree zero unrestricted. Zero sheaves and zero complexes are included.
Bounded-below complexes have arbitrary integer lower bound, not just nonnegative degrees.
No independent too-small universe for test objects, no file-local notation, no implicit
universe, and no extra hypothesis on coefficients or injective/derived-category instances
is introduced.

Searches (2026-10-15):

- `msearch.py ... leanfinder "The direct image functor on abelian etale sheaves along an
  integral morphism is exact and higher direct images vanish"`: eight unrelated
  Grothendieck-abelian/category/site results; no exact statement.
- `msearch.py ... loogle '"IsIntegralHom", "PreservesFiniteColimits"'`: zero hits.
- `msearch.py ... grep 'IsIntegralHom.*[Ee]xact|preservesFiniteColimits_lowerStar|integral.*direct image'`:
  zero Mathlib hits.
- `rg` with the same pattern in upstream WeilConjectures and side `lean/Sheaf`:
  upstream `SixFunctors/Integral/Exact.lean` has
  `Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`, but its full signature is
  for `Sheaf ... (ModuleCat Λ)`, for an arbitrary commutative coefficient ring Λ.
  It neither states the abelian-group-valued result verbatim nor includes the two
  derived conclusions. Read the whole file; no duplicate of the delivered declaration.
  Other hits concern the finite case, pro-étale closed immersions, and module-valued
  base change. Side hits concern constant module sheaves, not this statement.
- `grep -rn 'sbc-lem-integral-etale-direct-image-exact'` in upstream points to that same
  module-valued theorem; its blueprint tag alone does not make its signature identical.
- `msearch.py ... leansearch "Exactness of direct image of abelian etale sheaves along
  an integral morphism"`: unavailable, Internal Server Error (recorded without a verdict).

Source read: local `literature/stacks-project/etale-cohomology.tex`,
`lemma-what-integral` (Tag 04C2), especially clauses (1) and (4); and the node's blueprint
statement and full proof. The source assumes only integrality. Generic exact-functor
comparison signatures were read in the existing upstream `RightDerivedFunctor/PlusExact`
and Mathlib `RightDerivedFunctorPlus` modules.

Validation: server-only `scompile.py NN sbc-lem-integral-etale-direct-image-exact` compiled
the delivered file cleanly, including the private overlay of the disjoint-refinement
proof dependency. No local compiler was run. No disputed statement or node fault found.

## Second reading by NN

Read the node's statement and six proof steps against the delivered module and the
local Stacks sources: `etale-cohomology.tex`, `lemma-what-integral` (04C2), and
`derived.tex`, `lemma-right-derived-exact-functor` (015F). The former begins with an
arbitrary scheme morphism assumed integral, with no standing Noetherian, finite,
surjective, characteristic, or coefficient hypothesis. Its parts (1) and (4) give the
exactness used here; 015F supplies the two derived consequences.

Object, hypothesis, and conclusion checklist:

1. Schemes T' and T: `{X Y : Scheme.{u}}`; the source and target of the displayed
   functor agree with their roles in the node. Verdict: exact match.
2. Their morphism π: `(f : X ⟶ Y)`. Integrality: `[IsIntegralHom f]`. Opened the
   dependency's Mathlib `IsIntegralHom`: it extends `IsAffineHom f` and requires
   `(f.app U).hom.IsIntegral` for every affine open U. This is the node's integral
   morphism, without finiteness or surjectivity. Verdict: exact match.
3. Abelian sheaves on the small étale sites: `Sheaf X.smallEtaleTopology
   AddCommGrpCat.{u + 1}` and the corresponding Y category. Read the recorded
   `Sheaf`/`smallEtaleTopology` interfaces and the derived-category dependency
   `Sheaf.AlgebraicGeometry.DerivedCategories`, including its abelian-sheaf convention.
   No module coefficients, torsion, or structure-sheaf modules are substituted.
   Verdict: exact match under the recorded universe convention.
4. π_*: `lowerStar AddCommGrpCat.{u + 1} f`. Opened its definition and the formulas
   `lowerStar_obj_val_obj`, `lowerStar_obj_val_map`, and `lowerStar_map_hom_app`:
   it evaluates on the base change of each target étale object and acts on maps by
   restriction/whiskering. Also read its additive and finite-limit instances.
   Verdict: the recorded canonical direct image, not an arbitrary functor.
5. Exactness: `PreservesFiniteLimits ... ∧ PreservesFiniteColimits ...`. Both sheaf
   categories are abelian and this direct image is additive, so this is precisely
   exactness. No additional hypothesis is introduced. Verdict: exact match.
6. Positive higher direct images vanish: `∀ (F : Sheaf ...) (q : ℕ), IsZero
   (((lowerStar ... f).rightDerived (q + 1)).obj F)`. Every positive integer degree
   occurs, every sheaf is quantified, and categorical zero is asserted in the sheaf
   category. Read the named exact-functor higher-derived-vanishing dependency and
   enough-injectives dependency with these same categories. Verdict: exact match.
7. Rπ_*=π_* on D⁺: `∀ K : HomotopyCategory.Plus (Sheaf ...), IsIso
   ((lowerStar ... f).rightDerivedFunctorPlusUnit.app K)`. Opened Mathlib's full
   `rightDerivedFunctorPlusUnit` signature: its source is termwise direct image
   followed by `DerivedCategory.Plus.Qh`, its target is `Qh` followed by the right
   derived functor. Opened `rightDerivedLowerStarPlus` in upstream
   `Etale.Derived.UpperLowerStarCoherence`: it is exactly this
   `rightDerivedFunctorPlus`. Opened `HomotopyCategory.plus` and `Plus`: these
   represent bounded-below complexes with arbitrary integer lower bound. Their
   localization is D⁺, so invertibility of every canonical comparison expresses
   precisely the node's last proof step and its derived equality. Naturality is
   built into the named transformation. Verdict: exact match.
8. The finite-case sentence identifies an already recorded special case. Opened
   `SixFunctors.Finite.Exact`: its finite-colimit instance and canonical derived
   comparison specialize the same direct image. The theorem does not add a finite
   hypothesis; the finite-case dependency is imported and explained in the
   docstring. Verdict: no independent conclusion omitted.

Edge cases: empty schemes are allowed; neither scheme has a nonempty binder. Empty
coverings and partitions occur in the proof, not as restrictions on the statement.
Zero sheaves and zero complexes are included. Degree zero is deliberately not forced
to vanish; q+1 starts at 1. There is no characteristic restriction, coefficient ring,
Noetherian condition, finite hypothesis, or surjectivity condition. The single explicit
universe u is bound; the u+1 abelian-group values follow the dependency's convention
for the full small étale site, without a new equality of site universes. No free
variables or added derived-category/injective-resolution binders remain.

Independent H4 searches: `msearch.py ... leanfinder "An integral morphism induces an
exact pushforward functor on sheaves of abelian groups"` returned eight general
module-pushforward results, not this statement; `msearch.py ... loogle
'"lowerStar", "IsIntegralHom"'` returned zero hits. Searched with `rg` for
`integral.{0,50}(direct.image|lowerStar|pushforward)`,
`preservesFiniteColimits_lowerStar_of_isIntegral`, and the full delivered name across
Mathlib, upstream WeilConjectures, and project Sheaf sources. Opened upstream
`SixFunctors.Integral.Exact` in full: the candidate takes a commutative ring Λ and
states finite-colimit preservation for `ModuleCat Λ`-valued sheaves, with no two
derived conclusions. It is useful proof material but is not the node's entire
abelian-sheaf statement. No exact existing declaration or duplicate name was found.

No new definition nodes, dependency modules, hollow definitions, or statement
correction occur in this delivery. The only declaration introduced is the named
theorem with proof `sorry`; its source/blueprint docstrings and six-step proof plan
are present, and its recorded `lean.statement` agrees verbatim with the signature.
No mathematical mismatch was found, so the Lean and node record are unchanged.
The second reading adds this review only. Server-only scompile passed with no
errors or warnings. The initial invocation used a relative filename from the
read-only repository; rerunning from the sandbox resolved that invocation error.
