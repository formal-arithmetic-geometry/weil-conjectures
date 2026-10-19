## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedDerivedSmoothBaseChange` states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_boundedConstructible_of_smooth`.
Its sole proof is `sorry`; no definition or auxiliary theorem is added. The node changes
only in `lean`. There is no statement correction or disputed statement.

Hypotheses and clauses, in the node's order:

- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  The explicit `(N : ℕ)` and `hcoeff : IsSmoothBaseChangeCoefficients N Λ S`
  render positive N, finiteness, `(N : Λ) = 0`, and `IsUnit (N : Γ(S, ⊤))`.
  The predicate is exactly `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`.
  The explicit `Finite` instance supplies the instance required to type the recorded
  bounded-constructibility predicate. It repeats the same finiteness already in hcoeff
  and adds no mathematical restriction. Invertibility on the other three corners follows
  by pulling back along their maps to S; no independent hypothesis there is needed.
- The four arbitrary schemes and named arrows are
  `{X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}`.
  `sq : ChosenCartesianSquare h e f g` provides commutativity, the chosen isomorphism
  `Y ≅ pullback f g`, and both projection equations, exactly the specified square.
- Smoothness is `[Smooth f]`, using the recorded Mathlib definition, with no relative
  dimension, quasi-compactness, separatedness, or Noetherian assumption on f.
- The hypotheses on g are separately `[QuasiCompact g]` and `[QuasiSeparated g]`.
- Every K in Dᵇc is represented by `(K : DerivedCategoryModule Λ T)` together with
  `(hK : DerivedCategory.isBoundedConstructible Λ T K)`. This is precisely the object
  condition of the recorded full subcategory: all cohomology sheaves are constructible
  using `Scheme.IsConstructibleEtaleModuleSheaf`, and they vanish outside some [a,b],
  where a and b are integers and a ≤ b. No particular interval is fixed in the theorem.
- The conclusion is
  `IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app K)`.
  The generic exchange takes a square `CommSq g' f' f g` and has source Lg* Rf* and
  target Rf'* Lg'*. Flipping the node's square substitutes `(g',f',f,g)=(e,h,g,f)`.
  Thus this component has exactly source Lf* Rg* K and target Rh* Le* K in D(X_et,Λ).
  It is the canonical derived-square adjunction mate, not an arbitrary arrow or merely
  an existence of some isomorphism. The full square and its choice are passed through
  the dependency's `toCommSq`.
- This is the unbounded `derivedBaseChangeMap`, not `baseChange` on D⁺. Neither
  endpoint is required or asserted to be bounded or constructible, as the node requires.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients` (full defining conjunction).
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso` and its imported
  `ChosenCartesianSquare`, from `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`.
  Read the latter's full structure, including `hom_fst` and `hom_snd`. The inverse-image
  comparison is used internally by the canonical exchange, so no second comparison is defined.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `def-weil-pbc-scheme-conventions` is a convention-only node with no declaration/module.
  Its named notions here are Mathlib's `AlgebraicGeometry.QuasiCompact` and
  `AlgebraicGeometry.QuasiSeparated`; their full class signatures and docstrings were read
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and
  `AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`: its recorded
  `abelianDerivedBaseChangeArrow` is the abelian specialization. The node record explicitly
  retains and lists `AlgebraicGeometry.Etale.derivedBaseChangeMap`, imported from
  `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`, for the module coefficients
  used here. Read that declaration's full ambient coefficient assumptions, derived square,
  adjunction-mate definition, and functor signature. Its module has real canonical data.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: its existing
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, defined in upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, is the full unbounded
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.

All already recorded proof-dependency modules are imported as non-public imports:
`UnboundedAbelianExchangeComparison`, upstream `SmoothBaseChange.Theorem`,
`TruncationExchangeCouple`, `HypercohomologyConvergence`, `FiniteRangeComparison`, and
`AbelianDerivedExchangePlusCompatibility`. The last source was absent locally and read
with `scompile.py --source`; its public theorem identifies the unbounded abelian arrow
with the bounded-below component conjugated by canonical direct-image comparisons.
The docstring follows every one of the node's five proof steps, including the coefficient
annihilator calculation, exact-couple comparison, ambient compatibility, and conservativity.
The coefficient comparison currently uses exact termwise inverse-image exchange, which is
canonically identified with the derived pullback exchange used here by exactness of
constant-coefficient inverse image; no change of map or extra hypothesis is intended.

Edge cases checked: the empty scheme and arbitrary disconnected schemes are allowed;
zero complexes and the zero coefficient ring are allowed; N = 1 forces the zero ring but
is not excluded; N = 0 is excluded precisely by the node's positivity condition; arbitrary
positive composite N is allowed, with no primality hypothesis. The degree interval can be
negative or degenerate, and no sign condition is placed on its endpoints. Identity arrows
and arbitrary chosen pullback identifications are retained. Schemes live in arbitrary u,
with module coefficients in u+1 as required by the recorded small-site encoding; the
statement introduces no independent smaller test-object universe and no universe equality.
Smoothness and qcqs on g are meaningful hypotheses, not automatic properties of every map.

Searches for an existing exact statement:

- `msearch.py leanfinder`: “Smooth base change for bounded constructible complexes of
  etale sheaves with finite coefficients killed by an integer invertible on the base”.
  Eight hits concern stability of smooth/etale ring or scheme morphisms and differentials;
  none concerns the derived exchange.
- `msearch.py loogle`: `AlgebraicGeometry.Smooth, CategoryTheory.IsIso`.
  One hit is `Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`, a normalization result.
- `msearch.py grep`: `smooth.*base.?change|base.?change.*smooth|boundedConstructible`.
  Twenty-five Mathlib hits concern ring smoothness/base change and normalization;
  none states this derived etale result.
- `msearch.py leansearch`: “Smooth base change for bounded constructible derived etale
  sheaves with finite coefficient ring”. The service returned Internal Server Error;
  this is recorded as unavailable, not as evidence of absence.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`,
  plus `grep -rn` for the exact node id, located
  `Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth` in upstream
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived`, lines 285–298.
  Its full docstring and signature were read: it uses the upstream constructibility
  predicate `Etale.DerivedCategory.boundedConstructible` and concludes invertibility
  of `Etale.baseChange` on D⁺. The node explicitly uses the project's different recorded
  constructibility predicate and the actual unbounded module exchange. Consequently the
  upstream declaration is not an exact existing statement of this node.
- The project's `BoundedAllowableTorsionSmoothBaseChange` concerns abelian coefficients
  and adds a bounded-output conditional clause, so it is not this module statement either.
- Exact proposed declaration-name searches in Mathlib, upstream, the upstream name index,
  and project sources returned no existing declaration with that name.

The referenced blueprint markdown is not present in this machine's literature checkout.
Read the complete node statement and proof, and checked the source online:
[Stacks 0EYU](https://stacks.math.columbia.edu/tag/0EYU) has exactly the smooth and qcqs
square orientation; [Stacks 0F09](https://stacks.math.columbia.edu/tag/0F09) gives the
bounded-below spectral-sequence argument (a single smooth stage is its special case).
No extra geometric hypothesis is inferred from absent blueprint material.

Validation: `scompile.py N9 sbc-thm-bounded-derived-smooth-base-change` compiled the
sandbox probe and delivered module separately without any error or warning. All variables
and the single universe u are explicitly bound. No local notation, private definition,
local instance, or hidden let binder occurs in the statement. Only the expected theorem
proof `sorry` is left. The independent second reader will add their own review section.

## Second reading by N9

I independently opened the node, the delivered module, every statement dependency's
node and recorded declaration, and the relevant upstream declarations. The Lean says
exactly what the node says. No mathematical mismatch was found, so the Lean module and
node record are unchanged; this section records the independent review.

The source checkout has no Stacks `.tex` or blueprint markdown. I fetched the official
Stacks `etale-cohomology.tex` into this sandbox's `scratchpad/` and read the section
introduction, `theorem-smooth-base-change` (Tag 0EYU), and
`lemma-smooth-base-change-general` (Tag 0F09), including the latter's full proof.
The section introduces no additional standing hypotheses. Tag 0EYU has exactly smooth
f and qcqs g with the node's square orientation and allowable torsion. Tag 0F09 uses
bounded-below complexes and the hypercohomology spectral sequences; a one-stage inverse
system specializes its smooth-limit map to a smooth map. Neither source imposes
Noetherianity, separatedness of f, a field base, or a relative-dimension bound.
Sources: [0EYU](https://stacks.math.columbia.edu/tag/0EYU),
[0F09](https://stacks.math.columbia.edu/tag/0F09), and
[official TeX](https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex).

Here is my object/hypothesis/conclusion list and its Lean matching, in node order:

1. **Finite commutative coefficient ring.** `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]` gives exactly this. I opened `SmoothBaseChangeCoefficients.lean`:
   `IsSmoothBaseChangeCoefficients N Λ S` is the real conjunction
   `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`.
   The repeated `Finite Λ` instance is needed to type the recorded constructibility
   predicate and adds no restriction beyond the convention. Verdict: exact.
2. **Positive annihilator invertible on S.** `(N : ℕ)` and
   `(hcoeff : IsSmoothBaseChangeCoefficients N Λ S)` supply positivity, annihilation,
   and the global-section unit. Invertibility on X, T and Y follows by the indicated
   scheme maps; no extra unit hypotheses are imposed. Verdict: exact.
3. **Four schemes and four arrows with a chosen Cartesian identification.**
   `{X Y S T : Scheme.{u}}`, `{h : Y ⟶ X}`, `{e : Y ⟶ T}`, `{f : X ⟶ S}`,
   `{g : T ⟶ S}`, and `(sq : ChosenCartesianSquare h e f g)` introduce exactly them.
   I read the structure itself: it extends `CommSq`, contains
   `isoPullback : Y ≅ pullback f g`, and requires both projection equations
   `hom_fst` and `hom_snd`. It is an identification of squares, not a bare scheme
   isomorphism. Its imported `baseChangeInverseImageIso` is the inverse of the usual
   square comparison, in the orientation specified by the dependency node.
   Verdict: exact, including arbitrary chosen pullback identifications.
4. **f smooth.** `[Smooth f]` is the recorded Mathlib class, whose signature and
   affine-local smooth-ring-map definition I read. No dimension or global finiteness
   assumption is added. Verdict: exact.
5. **g quasi-compact and quasi-separated.** `[QuasiCompact g] [QuasiSeparated g]`
   are the notions collected by the convention-only dependency. I read both Mathlib
   classes: quasi-compact preimages of compact opens, and quasi-compact diagonal.
   These are actual restrictions on g, not automatic instances. Verdict: exact.
6. **Every bounded constructible K on T.** `(K : DerivedCategoryModule Λ T)` and
   `(hK : DerivedCategory.isBoundedConstructible Λ T K)` quantify over precisely
   the objects of the recorded full subcategory. I opened `DerivedCategories.lean`,
   upstream `Etale/Derived/Coefficients.lean`, `BoundedConstructibleComplexes.lean`,
   and `IsConstructibleEtaleModuleSheaf.lean`. The ambient category is the full
   unbounded derived category of `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`;
   the predicate requires the recorded finite-stratification constructibility of
   every cohomology sheaf and an existential integer interval a ≤ b outside which
   cohomology is zero. It does not require Tor amplitude or fix a common interval
   for different K. Verdict: exact.
7. **The specified canonical exchange is an isomorphism in D(X_et,Λ).**
   The conclusion is `IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
   sq.toCommSq.flip).app K)`. I read the generic map's definition and ambient
   coefficient assumptions in upstream `BaseChange/DerivedUnbounded.lean` and the
   dependency's mixed module/abelian record. `derivedBaseChangeMap` is explicitly
   retained by that record, and its monoidal/Grothendieck/sheafification requirements
   are available for modules over every commutative Λ, including the zero ring.
   For the flipped square its generic `(g',f',f,g)` become `(e,h,g,f)`, so its
   source is Lf* Rg* K and target Rh* Le* K, both on X. It is the mate of the
   canonical derived inverse-image square isomorphism, with the counit transpose
   required by the node. It is neither an unspecified map nor a bare existence of
   an isomorphism. Verdict: exact.
8. **No bounded/constructible-output clause.** The single `IsIso` conclusion is
   in the ambient unbounded category, with no further predicates on either
   endpoint. This includes the node's final qualification. Verdict: exact.

Edge cases: empty schemes, disconnected schemes, zero complexes, and the zero ring
are all allowed. N = 0 is excluded exactly by positivity; N = 1 and arbitrary
positive composite N are allowed, with no prime or nontrivial-ring assumption.
The cohomological bounds can be negative, zero, or equal. Identity morphisms and
relative dimension zero are retained. No index set is introduced by this statement;
the recorded constructibility definition permits the empty stratification for the
empty scheme. Universe u is arbitrary; the coefficient and module universe u+1 is
the recorded small-etale-site size convention. There is no smaller test universe or
extra universe equality. All variables and universes are explicitly bound.

Independent searches, using words different from the worker's initial query:

- `msearch.py leanfinder`: “The inverse image of a smooth scheme morphism commutes
  with total right derived pushforward on etale finite torsion module sheaves”.
  Eight hits are underived module pushforward/composition/restriction facts; none
  states this exchange theorem.
- `msearch.py loogle`: `CategoryTheory.IsIso, DerivedCategory`. Twelve hits concern
  localization, quasi-isomorphisms, homology detection, fractions, and bounded-below
  derivability; none is smooth base change.
- `msearch.py grep`: `exchange|smooth` in `AlgebraicGeometry`. Twenty-five returned
  Mathlib hits concern group schemes, normalization, smooth morphisms and fibres;
  no exact statement. I also ran direct `rg` searches on Mathlib, upstream
  `WeilConjectures`, project `lean/Sheaf`, and the upstream-name index by the exact
  proposed declaration name, node id, `derivedBaseChange`, and smooth-exchange terms.
- `msearch.py leansearch`: “Smooth inverse image commutes with unbounded derived
  direct image on bounded complexes of finite etale module sheaves”. The service
  returned Internal Server Error; this is unavailable, not evidence of absence.
- The node-id search finds upstream
  `Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth`. I read its complete
  signature and docstring in `SmoothBaseChange/Derived.lean`: it concludes about
  `Etale.baseChange` on the bounded-below category and uses upstream
  `DerivedCategory.boundedConstructible`, rather than the project's recorded
  constructibility predicate. It is therefore not an existing exact statement of
  this node. The project's bounded allowable-torsion theorem has abelian
  coefficients and an additional conditional bounded-output clause, so it is not
  an exact replacement either. No second definition is introduced in this delivery.

There are no new nodes, dependency modules, private copies, or statement corrections
to review under H12/H13/§1(C). I verified that the sandbox node differs from the
shared node only in `lean`, and its `lean.statement` equals the file signature
verbatim. The module contains one public named theorem, with whole proof `sorry`,
and no definitions or other theorems. Its docstring cites the node and source and
contains all five proof steps: coefficient forgetting and annihilation; degreewise
smooth base change; exact-couple/E2 comparison and convergence; bounded-below to
unbounded compatibility; conservative descent of the canonical exchange. I read
the current compatibility theorem with `scompile.py --source
Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility`; it uses precisely
the inverse source comparison and forward target comparison described in step 4.
The exact-termwise and left-derived module pullbacks are canonically identified by
exactness; the report already identifies that stage-3 comparison, without changing
the theorem's actual arrow. No hidden `let`, local notation, local instance, private
declaration, or overlength line occurs in this statement module.

Validation: independently ran `scompile.py N9
sbc-thm-bounded-derived-smooth-base-change
lean/Sheaf/AlgebraicGeometry/BoundedDerivedSmoothBaseChange.lean`. Both the wrapper's
sandbox check (7.7 seconds) and separate library-path check (10.1 seconds) completed
with no errors or warnings under the 60-second limits. No repair was required;
only this independent reading and its search evidence were added.
