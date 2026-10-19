## Worker report

This delivery states the definition `def-sf-categories` as direct category aliases and full
subcategories in `Sheaf.SixFunctors.SfCategories`. The primary declaration is
`WeilConjectures.sfAmbientDerivedCategory`; `lean.declarations` lists every additional declaration
owned by this node. No product of categories or new categorical datum is introduced. There are
no proofs or `sorry`s in either delivered module. Definitions have their actual data.

I read the item, the statements and records of its 26 statement dependencies, and the blueprint
source `main-20261015/blueprint/sec-six-functors/sk-def-sf-categories/def-sf-categories.md`.
The node's expanded coefficient-stage conventions are retained. The integral, rational and
common-stage constructions are reused under their existing names, not redefined. One dependency
interface needs a presentation repair under §1(B), described below. The other repair in the
returned packet has already landed independently as Q70’s exact existing-declaration binding;
this delivery uses it without changing that node. There is no statement
correction, new node, or `STATEMENT-DISPUTED` finding.

### Every hypothesis and clause

| Node clause | Lean rendering |
| --- | --- |
| A scheme T and either small site | `T : Scheme.{u}` for the specialized definitions. The ordinary ambient aliases take an arbitrary `J : GrothendieckTopology C`, specializing to `T.smallEtaleTopology` or `Scheme.ProEt.topology T`. They introduce neither a third site nor a different topology. |
| Universes and small skeleton convention | The generic ambient section has explicit site-object `c`, site-morphism `h`, ring `r`, module-value `m`, and localization `w` universes. The needed sheafification and locally-bijective equivalence instances supply Mathlib's canonical abelian structure; `HasDerivedCategory.{w}` fixes the localization universe. In particular the pro-etale site keeps object universe `u+1` and arrow universe `u`. |
| A sheaf of commutative rings R_T and its module category | The ambient aliases use the exact recorded `ringedSiteModules.{m} R`. Here `R : Sheaf J RingCat` is the underlying ring sheaf of the commutative sheaf. The pro-etale torsion definition accepts the commutative ring sheaf itself and explicitly applies `sheafCompose` with `forget₂ CommRingCat RingCat`. Allowing the ambient construction for any ring sheaf adds no condition in the commutative specialization. |
| D(T_tau,R_T) | `sfAmbientDerivedCategory R := DerivedCategory (ringedSiteModules.{m} R)`. |
| D+, D-, Db and their cohomological boundedness meanings | `sfAmbientDerivedCategoryPlus`, `sfAmbientDerivedCategoryMinus`, `sfAmbientDerivedCategoryBounded` are exactly `DerivedCategory.Plus`, `.Minus`, `.Bounded` of the same category. Mathlib's standard t-structure defines these by the corresponding eventual cohomology vanishings. |
| Constant commutative coefficients R | `sfConstantDerivedCategory J A` uses `(constantSheaf J RingCat).obj (RingCat.of A)` for `[CommRing A]`, then exactly the ordinary module derived category. This is sheafification of the constant presheaf as a ring sheaf, as required. |
| P-torsion on the etale site | `sfEtaleAllowableTorsionCategory T R P` is a full subcategory of `DerivedCategory.Plus (SheafOfModules R)`. For every integer `i`, it applies the recorded `Etale.allowableTorsionSheafProperty T P` to `SheafOfModules.toSheaf R` of `homologyFunctor _ i` of `K.obj`. The recorded predicate quantifies over every separably closed geometric point, every stalk element, and a positive natural annihilator with each prime divisor in P. |
| P-torsion on the pro-etale site | `sfProEtaleAllowableTorsionCategory` is the full subcategory of the bounded-below ringed-module derived category. Its body explicitly quantifies `i`, every algebraically closed field `Ω`, geometric map `s`, and every `x` in the recorded `geometricRingModuleStalkFunctor s R` of `H^i(K)`. It requires `∃ n : ℕ, 0 < n ∧ (∀ p, p.Prime → p ∣ n → p ∈ P) ∧ n • x = 0`. Positive naturals express exactly positive integer annihilators. |
| P consists of primes invertible on T | This is the stated convention for using either torsion category, documented in their docstrings. The formula is meaningful for any P and imposes no additional hypothesis on its elements. As in the recorded abelian-etale dependency, nonprime members are immaterial. |
| Global finite-field datum, ell ≠ p, algebraic closure, finite extension E and uniformizer | These are the node's coefficient conventions. The actual definitions use `l : ℕ`, `[Fact l.Prime]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, and for the closure `[IsAlgClosure (Padic l) Ω]`. The existing Padic coefficient constructions provide the valuation ring and chosen uniformizer. The intrinsic dependency definitions do not use the global datum or the characteristic inequality; fixing those in the source simply specializes these same definitions. No alternative finite-field, valuation, uniformizer or embedding choice is made here. |
| n ≥ 1 and A_{E,n} | `n : ℕ`, `hn : 1 ≤ n`, and `Padic.coefficientExtensionRing l E n` inside the recorded intrinsic and finite-Tor predicates. For the etale aliases specialize `Λ` to `ULift.{u+1,u} (Padic.coefficientExtensionRing l E n)`; positive-level finiteness is the recorded theorem `Padic.finite_coefficientExtensionRing l E n hn`. |
| ell invertible for finite-Tor conventions | These aliases are used under the node's invertibility convention, exactly as the existing intrinsic finite-Tor category. Their formulas do not change with a proof of invertibility. There is no extraneous geometric premise or restriction on T. |
| Finite-etale Db_c | `sfEtaleConstructibleCategory Λ T` is the full subcategory of the repaired recorded `Etale.DerivedCategory.isBoundedConstructible Λ T`. It requires the recorded finite-value constructibility of every cohomology sheaf and a single ordered finite bound, not merely the upstream finitely-generated-stalk variant. |
| Finite-etale Db_ctf | `sfEtaleConstructibleFiniteTorCategory` is a full subcategory of the preceding category with `∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn Λ T a b K.obj`. The recorded predicate tests every degree-zero module sheaf and all cohomological degrees. |
| Finite-etale interval category | `sfEtaleConstructibleIntervalCategory Λ T a b` is a full subcategory of `sfEtaleConstructibleCategory`, requiring `∀ i, i < a ∨ b < i → IsZero ((homologyFunctor _ i).obj K.obj)`. |
| Finite pro-etale Db_c | `sfFiniteConstructibleCategory l E n hn T` is exactly `(Scheme.intrinsicFiniteTorsionConstructible l E n hn T).FullSubcategory`. Finitely many nonzero cohomologies and constructibility are both retained. No etale-origin hypothesis is imposed. |
| Finite pro-etale Db_ctf | `sfFiniteConstructibleFiniteTorCategory` is exactly the recorded `finiteTorConstructibleCategory`. Its predicate is intrinsic constructibility intersected with `HasFiniteProEtaleTorAmplitude`, whose ordered interval tests every degree-zero module sheaf. This full subcategory in the unbounded ambient has exactly the inherited Hom sets of the corresponding subcategory of Db_c. |
| Finite pro-etale interval category | `sfFiniteConstructibleIntervalCategory l E n hn T a b` is the transparent alias of the dependency declaration `intrinsicConstructibleIntervalCategory l E n hn T a b`. Its objects are intrinsic finite Db_c objects satisfying `∀ i : ℤ, (i < a ∨ b < i) → IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj)`. It inherits the containing constructible category’s morphisms and includes no Tor condition. |
| Fullness, identities and composition | Every new category is a transparent alias to Mathlib `ObjectProperty.FullSubcategory`; its category is the `InducedCategory` on the underlying-object function. Nested full subcategories inherit the same derived Hom sets, identities and composition. Existing scalar-localization/common-stage categories retain their own recorded morphisms. |
| Integral ambient over the completion | `sfIntegralAmbientDerivedCategory l E T := DerivedCategory (scalarReductionSource.{u,u} l E T)`. That is the recorded module category over the completed coefficient sheaf, not the constant ring sheaf of O_E. |
| Integral Db_c and its common reduction bound | Reexported `sfIntegralConstructibleCategory l E T` uses exactly `sfIntegralConstructible`: derived completeness, constructibility of every positive reduction, and one cohomological interval bounding all reductions. No additional boundedness hypothesis on the unreduced complex is inserted. |
| Integral Db_ctf and uniform Tor bound | Reexported `finiteTorConstructibleIntegralCategory` uses the same completed module category and the same integral constructibility predicate, plus one ordered Tor interval for every positive reduction. |
| Rational Db_c | Reexported `sfRationalConstructibleCategory` is exactly the scalar localization of that integral category, with unchanged objects and the recorded Hom tensor E coordinates; no Karoubi completion is introduced. |
| Algebraically closed Db_c | Reexported `generalAlgebraicallyClosedConstructibleCategory` has exactly the recorded finite-field pairs and common-stage Hom colimits, compositions and triangles. No comparison with an ordinary constant-coefficient category is asserted. |
| Field Db_ctf = Db_c | `sfRationalConstructibleFiniteTorCategory` and `sfCommonStageConstructibleFiniteTorCategory` apply the existing `finiteTorFieldCoefficientCategory` identity alias to those exact rational/common-stage categories. |
| Integral, rational and common-stage D_c^[a,b] | `sfIntegralConstructibleIntervalCategory`, `sfRationalConstructibleIntervalCategory`, `sfCommonStageConstructibleIntervalCategory` take the full subcategory on `sf*StandardClass false a ⊓ sf*StandardClass true b`. These are precisely the recorded shifted lower and upper classes. Rational and common-stage membership retain their isomorphism-closure/finite-stage meanings. |
| Ordered bounds a ≤ b | All interval formulas apply, in particular, to every ordered pair. They are also well-defined for reversed bounds (cohomological vanishing in all degrees); no ordered pair is omitted and no stronger condition is imposed. |

### Dependency declarations read and used

| Dependency | Module and declaration/interface |
| --- | --- |
| def-weil-pbc-etale-site | `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`. |
| def-weil-pbc-proetale-site | `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`. |
| def-weil-size-convention | Recorded metatheoretic convention; explicit universes and the canonical sheafification/localization instances above. There is no object to duplicate. |
| def-weil-sheaf-of-modules-category | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`. `SheafOfModules.toSheaf` supplies its underlying abelian sheaf. |
| def-weil-abstract-derived-category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`. |
| def-weil-pbc-bounded-derived-subcategories | `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.Plus`, `.Minus`, `.Bounded`. |
| def-weil-pbc-constant-sheaf | `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`. |
| def-weil-pbc-derived-categories | `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `Etale.DerivedCategoryModule`, reexported by the recorded derived-category module. `BoundedConstructibleComplexes` imports the corresponding published side module. |
| def-sf-induced-category | `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: its category instance is Mathlib `InducedCategory`. |
| def-weil-derived-cohomology-sheaves | `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `DerivedCategory.homologyFunctor`. |
| def-weil-pbc-geometric-stalks | `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`; `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber`. The etale allowable-torsion predicate uses these exact stalks. |
| def-weil-proetale-geometric-stalk | `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`: `Scheme.geometricRingModuleStalkFunctor`, the actual module colimit, with no arbitrary stalk functor parameter. |
| sbc-def-derived-categories-with-allowable-torsion | `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`: `Etale.allowableTorsionSheafProperty`. |
| def-weil-finite-field-fiber | `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`. Its fixed global conventions specialize the intrinsic coefficient constructions; no new datum is defined. |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, and the publicly imported `Padic.coefficientExtensionRing`. |
| def-weil-pbc-constructible-complexes | Current Q70 existing-declaration binding, used unchanged: `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, `Etale.DerivedCategory.isBoundedConstructible`. |
| def-weil-finite-torsion-constructibility | `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: `Scheme.intrinsicFiniteTorsionConstructible`. |
| def-kun-tor-amplitude | `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: publicly imported `Etale.DerivedCategory.hasTorAmplitudeIn`. |
| def-weil-finite-tor-amplitude | `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructibleCategory`, `finiteTorConstructibleIntegralCategory`, `finiteTorFieldCoefficientCategory` and their defining predicates. |
| def-weil-constructible-intervals | §1(B) dependency module: `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`, `WeilConjectures.intrinsicConstructibleIntervalCategory`. |
| def-weil-derived-category-cohomological-support | Mathlib `DerivedCategory.homologyFunctor` and `Limits.IsZero`, the recorded support-vanishing expression. |
| def-weil-completed-integral-coefficients | `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its completion imports; the ambient is the identical `scalarReductionSource`. |
| def-weil-derived-complete-integral-detailed | `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, `sfIntegralConstructibleCategory`. |
| def-weil-rationalization-karoubi | `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`. |
| def-weil-algebraically-closed-coefficients | `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `generalAlgebraicallyClosedConstructibleCategory`. |
| def-weil-constructible-standard-tstructure | `Sheaf.Paper.SfConstructibleHeart`: `sfIntegralStandardClass`, `sfRationalStandardClass`, `sfCommonStageStandardClass`. |

Current sources for missing/stale local modules were read using `scompile.py --source`, including
the finite, integral, rational, general algebraically closed, derived-category and fixed-scalar
constructible modules. The exact ordinary etale constructibility predicate and its finite-value
constructibility dependency were also read locally in full.

### Edge cases

For the zero complex, all stalks are zero and annihilator `n = 1` works for every P; there is no
nonzero-coefficient hypothesis. For `P = ∅`, only annihilator 1 is allowable, so the tested stalk
groups are zero; for all primes, the condition is exactly torsion, not one uniform exponent.
The quantifier order gives a separate annihilator for each element, point and cohomological
degree. Bounded-below is retained even when cohomology is not bounded above.

The empty scheme and all geometric-point quantifiers are allowed. `n = 1` is included and
`n = 0` is excluded precisely by `hn`. Intervals are inclusive at both endpoints, include the
single-degree case `a = b`, and have no finite-Tor condition unless the ctf subcategory is chosen.
Over `Z/l^2`, a residue-field module in degree zero shows why bounded constructibility alone
must not replace the finite-Tor predicate. Integral definitions retain one interval across all
reductions rather than one different interval at each reduction. Field stages use exact
identity aliases, and the integral/rational/common-stage interval objects stay in their
respective categories. The small pro-etale site is never made a same-object-and-arrow-universe
site. `autoImplicit false` is set in both modules; every level and variable is bound.

### Searches and validation

Actual searches made with `msearch.py Q94 def-sf-categories`:

- LeanFinder: `Bounded constructible derived categories of etale and proetale module sheaves with allowable torsion and finite Tor amplitude`: 8 hits, mainly condensed module categories and `DerivedCategory.IsGE`, no entire match.
- Loogle: `DerivedCategory, "constructible"`: 0 hits.
- Mathlib grep: `allowableTorsion|sfCategories|boundedConstructibleFiniteTor`: 0 hits.
- LeanSearch: `Bounded constructible derived sheaves with allowable prime torsion`: 8 hits, generic derived t-structures and unrelated constructible subsets/modules, no entire match.
- Direct `rg` over upstream `WeilConjectures` and side `lean/Sheaf` for `sfCategories`, the node id, allowable torsion and finite-Tor names found existing component definitions, not one declaration covering the item. Upstream constructibility uses the finitely-generated-stalk predicate; the recorded project definition with finite constant values is used instead. The existing ordinary-small-etale predicate was found and reused after reading its full definition.

Both final delivery modules compiled individually through `scompile.py`, in dependency order,
with no errors or warnings. A separate scratch import check confirmed that the existing
`BoundedConstructibleComplexes` module and `Etale.DerivedCategory.isBoundedConstructible` import
compatibly with `FiniteTorAmplitude` and `SfConstructibleHeart`. Scratch files are outside
`lean/` and are not delivered. The required dry run and delivery are performed after recording
these final interfaces.

## Dependency modules

`def-weil-constructible-intervals`: new module
`Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`, with the exact intrinsic finite
coefficient category as ambient. The prior recorded `constructibleIn` is in the fixed-scalar
`Sheaf _ (ModuleCat A)` etale-origin presentation; the intrinsic constructibility and finite-Tor
records use the ringed-module `proEtaleDerivedCategory`. The new dependency module directly
states the same interval full subcategory on the recorded intrinsic constructible objects,
using `homologyFunctor` and `IsZero`, with no Tor condition, equivalence choice, etale-origin
assumption or comparison theorem. Only its node's `lean` field changes.

## Second reading by Q94

Fresh repair worker, independent of the author of the retained packet, 2026-10-17 UTC.
I opened the complete node, its current blueprint source at
`main-20261015/blueprint/sec-six-functors/sk-def-sf-categories/def-sf-categories.md`,
the two delivered Lean files, both dependency-node statements, the current dependency records,
and the component definitions named below. I did not author the retained delivery. This reading
replaces its explicitly identified author self-reading; no other agent was started.

### Returned points and changes

1. **H3, missing finite pro-etale interval declaration.** The retained file ended its finite
   coefficient section after `sfFiniteConstructibleFiniteTorCategory`. Its interval dependency
   existed, but the item had no corresponding declaration in that section or in
   `lean.declarations`. I added `sfFiniteConstructibleIntervalCategory (a b : ℤ)` with body
   `intrinsicConstructibleIntervalCategory l E n hn T a b` and listed its full name in the item’s
   record. This directly renders the third displayed finite category on the pro-etale site.
   The alias uses the existing dependency rather than copying its predicate. Opening that
   dependency shows that its ambient is the full category of
   `intrinsicFiniteTorsionConstructible l E n hn T`, its sole extra condition is vanishing of
   `homologyFunctor` outside the inclusive interval, and its Hom sets, identities and composition
   come from that category. In particular there is no finite-Tor or etale-origin requirement.
2. **H11, self-reading.** I replaced the author’s paragraph with this independent reading of the
   retained packet and the repaired definitions. The clause checks below record the actual
   declarations and bodies checked, including the missing clause found and repaired in point 1.

The initial required dry run of the retained packet passed (commit `7ff2ea6a58`). That verifies
compilation and mechanical shape; it does not resolve H3 or H11. The two changes above are
substantive repairs on top of the returned packet, not an unchanged re-push.

### Clause checks against the final files

- **Schemes, sites, modules and universes.** `T : Scheme.{u}` occurs in every specialized
  definition. `smallEtaleTopology` and `Scheme.ProEt.topology` are the exact recorded small
  sites; I read their Mathlib definitions. The generic `RingedSite` section binds site-object,
  site-arrow, ring, value and localization universes separately. `ringedSiteModules` unfolds
  to Mathlib `SheafOfModules`; the ringed-site abelian and derived-category typeclasses record
  existence of the structures required by the source. The small pro-etale site still has
  object universe `u+1` and arrow universe `u`. `autoImplicit false` is present in both files.
- **Ordinary D, D+, D-, Db and constant coefficients.** The four ambient bodies are literally
  `DerivedCategory`, `.Plus`, `.Minus`, `.Bounded` of the same recorded module category.
  Mathlib `TStructure.lean` defines Plus by the existence of a lower bound, Minus by an upper
  bound and Bounded by their intersection. The constant-coefficient body is the derived
  category over `(constantSheaf J RingCat).obj (RingCat.of A)` for `[CommRing A]`;
  `constantSheaf` sheafifies the constant presheaf. Passing to RingCat only forgets
  commutativity for forming modules. No derived-completeness condition enters ordinary D.
- **Allowable torsion on both sites.** Both category bodies start with `DerivedCategory.Plus`,
  so they retain bounded-below objects and do not silently require boundedness above. The
  etale body applies the recorded `allowableTorsionSheafProperty` after `SheafOfModules.toSheaf`
  to each integer cohomology sheaf. I opened that predicate: it quantifies over separably
  closed geometric fields, points and individual elements, then requires a positive natural
  annihilator with all prime divisors in P. The pro-etale body has exactly that quantifier
  order with algebraically closed fields and `geometricRingModuleStalkFunctor`. I opened this
  functor: it is restriction to pointed neighbourhoods followed by the module colimit, with
  the actual stalk-ring action. There is no arbitrary stalk parameter or uniform exponent.
  The invertibility of the primes in P is the source convention for using the notation;
  these formulas also make sense for other P and do not assert an additional theorem there.
- **Finite coefficients and the three etale categories.** The coefficient ring is exactly
  `Padic.coefficientExtensionRing l E n`, with prime l, finite-dimensional E/Padic l and
  `hn : 1 ≤ n`. The etale aliases accept any finite commutative ring, hence in particular
  its recorded ULift. The current Q70 `isBoundedConstructible` body uses the project’s finite
  locally constant values on a finite constructible stratification and one ordered interval
  bounding cohomology. `sfEtaleConstructibleFiniteTorCategory` adds one existential ordered
  interval to `hasTorAmplitudeIn`; I read its upstream body, which tests all degree-zero
  module sheaves and all outside degrees of the derived tensor. The interval category instead
  adds only `∀ i, i < a ∨ b < i → IsZero (H^i K)` to Db_c.
- **The three finite pro-etale categories.** `sfFiniteConstructibleCategory` unfolds to the
  exact intrinsic predicate’s full subcategory. I read that predicate: finite support of
  cohomology and intrinsic finite-stratification constructibility in every degree.
  `sfFiniteConstructibleFiniteTorCategory` is an alias of `finiteTorConstructibleCategory`,
  whose body intersects this predicate with `HasFiniteProEtaleTorAmplitude`. Its definition
  quantifies one ordered interval before all test sheaves; it does not replace Tor amplitude
  by cohomological boundedness. The repaired `sfFiniteConstructibleIntervalCategory` is the
  inclusive cohomological interval described in return point 1. All three have the same
  underlying derived Hom sets, including in the nested interval full subcategory.
- **Integral coefficients.** The integral ambient is `DerivedCategory (scalarReductionSource
  l E T)` of the completed ring sheaf, not of the constant O_E sheaf. The imported
  `sfIntegralConstructible` body requires `IsSfDerivedComplete` and an existential single
  ordered interval followed by `∀ n : ℕ`, intrinsic constructibility and support in that
  interval for the `(n+1)`st derived reduction. I also read `finiteTorConstructibleIntegral`:
  it uses the same ambient and constructibility predicate and one ordered Tor interval for
  all positive reductions. Nothing in the new aliases changes these quantifiers.
- **Rational and algebraically closed coefficients.** `sfRationalConstructibleCategory` is
  the recorded `ScalarLocalization` of the integral category at the chosen uniformizer;
  `generalAlgebraicallyClosedConstructibleCategory` is the recorded finite-field pair
  category with common-stage Hom colimits. These imported definitions, rather than ordinary
  constant-coefficient derived categories, supply the categories. The two field ctf aliases
  apply `finiteTorFieldCoefficientCategory`, whose body is the identity on its input type.
  Thus their objects, morphisms and category structures are unchanged; no completion or
  idempotent envelope is introduced.
- **All three higher intervals.** In `SfConstructibleHeart` I checked that Bool false at a
  gives the lower class and true at b the upper class. The integral class tests actual
  cohomology, the rational class is its isomorphism closure after localization, and the
  common-stage class is represented up to isomorphism at a finite stage. Each interval body
  takes exactly the intersection of these two recorded classes. No finite-field structure
  morphism or finite-type hypothesis is needed to define these classes; the separate
  t-structure theorem has those hypotheses. The aliases do not use that theorem.

### Dependency repairs and comparison with current base

The current `def-weil-pbc-constructible-complexes` record already binds the exact
`AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` in the imported
`Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, by Q70. I removed the redundant
Q94 dependency copy from the delivery instead of overwriting that landed attribution.
The dependency table above now identifies the current declaration actually used.

The interval dependency still records upstream `ProEtale.DerivedCategory.constructibleIn`
on `DerivedCategory (Sheaf _ (ModuleCat A))`, with bounded constructibility defined by etale
origin. I read its current source through `scompile.py --source`. It does not accept the
item’s recorded intrinsic `proEtaleDerivedCategory` objects. The retained §1(B) module
`IntrinsicConstructibleIntervals` states the dependency directly on its recorded intrinsic
bounded-constructible ambient and uses Mathlib’s exact cohomology and full-subcategory
constructions. This changes only its Lean record and preserves the node’s statement.
No comparison equivalence, arbitrary map, choice from Nonempty, or new notion is inserted.
Both delivered node copies were refreshed from the current base with only their Lean records
retained; there is no item statement correction or new definition node.

### Edge cases and final check

I checked the empty scheme, zero objects, P empty and P all primes, n=1, the inclusive
endpoints and a=b. For zero stalk elements, n=1 witnesses allowable torsion; P empty forces
elementwise zero rather than an unrelated uniform-exponent condition. The interval predicate
excludes precisely i<a or b<i, so degree a and degree b are included. For a=b it tests a single
cohomological degree. A module concentrated in degree zero over Z/l^2 can be bounded
constructible without finite Tor amplitude, so the interval alias must not use the finite-Tor
category; it does not. The aliases also allow reversed bounds, which impose total cohomology
vanishing; every source-allowed ordered pair is included. No definition contains sorry, no
proof was introduced, and no universe or variable was left auto-bound. The independent
reading found the missing alias and redundant stale rebind above and no further mismatch.

Validation: `scompile.py Q94 def-sf-categories` compiled both delivered files separately in
dependency order, exit 0 with no warnings or errors. The library checks took 10.3 s for
`IntrinsicConstructibleIntervals` and 51.9 s for `SfCategories`, each below the unchanged 60 s
limit. The repaired packet is then checked by `deliver2.py --no-push` before the final push.

## Maintainer review correction (2026-10-18)

The independent maintainer review found the existing intrinsic interval construction in
`Sheaf.Paper.ConstructibleIntervalsUnordered`: `constructibleInterval` intersects
`intrinsicFiniteTorsionConstructible` with `proEtaleCohomologicalSupport K ⊆ Set.Icc a b`,
and `constructibleIntervalCategory` is its full subcategory. This file was already present
at delivery commit 255d7c8d02075fb8f642076b387715d6a1408ef2. Thus the assertion above
that only the fixed-scalar interval presentation existed was incomplete.

The replacement `IntrinsicConstructibleIntervals` imports that existing module and makes
`intrinsicConstructibleIntervalCategory` a transparent alias of its category. It constructs
neither a new predicate nor a second category. The public declaration and its complete
explicit signature are preserved. All interval objects, morphisms, identities and composition
are those of the existing construction. The item still uses this recorded dependency
interface. The difference between the former nested subtype and the existing conjunction
subtype is only a presentation of the same full subcategory; no mathematical statement
changes. Every source-allowed ordered interval remains covered.

Maintainer validation: the replacement dependency and unchanged SfCategories module
compiled separately, in dependency order, through `scompile.py Q94 def-sf-categories`,
with exit 0 and no Lean errors or warnings. The wrapper confirmed both library module
paths in its private side overlay and kept the 60 s per-Lean limit after slot acquisition.
The original snapshot pair was also reproduced successfully. No global build, direct Lean
invocation, project-clone edit or direct SSH command was used for this review.
