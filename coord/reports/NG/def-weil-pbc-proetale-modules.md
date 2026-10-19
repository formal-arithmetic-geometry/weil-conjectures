## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` states the complete definition
of `def-weil-pbc-proetale-modules`. The item node changes only in `lean`. No new node,
dependency replacement, statement correction, or disputed statement is needed. All files
written by this worker are in the assigned sandbox. The prescribed compilation and delivery
wrappers handle their own authorized bookkeeping. This is the worker's report; the independent
second reading remains for the second reader.

Hypotheses and clauses, in the order of the node:

1. An arbitrary scheme is `T : Scheme.{u}`. The coefficient ring is
   `Λ : Type (u + 1)` with `[Ring Λ] [Finite Λ]`, not `[CommRing Λ]`.
   Its given discrete topology is `[TopologicalSpace Λ] [DiscreteTopology Λ]`.
   These hypotheses are explicit on `finiteCoefficientPresheaf` and the primary
   `isBoundedConstructibleFiniteCoefficient` signature; the intermediate declarations use
   the explicitly declared section variables. The site is the existing `T.ProEt` and
   `Scheme.ProEt.topology T`. Its object universe is `u + 1` and morphism universe `u`;
   no equality between these universes, auxiliary smallness assumption, or new site is imposed.
   Ring sections and module values live in the common larger universe `u + 1`.
2. The connected-component space is Mathlib's `ConnectedComponents U.unop.left`.
   Its topology is the quotient topology, with quotient map `ConnectedComponents.mk`, as
   witnessed by `ConnectedComponents.isQuotientMap_coe`. No discreteness or local
   connectedness of this space is assumed.
3. `finiteCoefficientPresheaf` has object
   `RingCat.of C(ConnectedComponents U.unop.left, Λ)`, whose operations are pointwise.
   Its restriction along `f` is composition with
   `f.unop.left.continuous.connectedComponentsMap`, bundled with its existing continuity
   proof. The identity and composition laws reduce to the induced maps on quotient classes.
4. `finiteCoefficientRingSheaf` is exactly
   `(presheafToSheaf (Scheme.ProEt.topology T) RingCat).obj
   (finiteCoefficientPresheaf T Λ)`, rather than an abstract ring chosen from existence.
5. `FiniteCoefficientModules` is `ringedSiteModules.{u + 1}` of that ring sheaf, hence
   exactly `SheafOfModules` from the recorded dependency. These are left modules, the
   restriction maps are semilinear, and morphisms are the sectionwise linear maps of the
   existing category. Its abelian structure is the existing Mathlib instance.
6. `FiniteCoefficientDerivedCategory` is the existing `DerivedCategory` of that abelian
   category, with `HasDerivedCategory.standard`, as in the recorded pro-etale site module.
   Thus it localizes `CochainComplex _ ℤ` at quasi-isomorphisms. The associated cohomology
   objects are `DerivedCategory.homologyFunctor`, the kernel/image cohomology of that
   same abelian category. This construction is ordinary, uncompleted and unbounded.
   `finiteCoefficientModules_hasDerivedCategory` names the same standard localization
   instance for the derived functor API; it does not choose a second abelian structure.
7. `FiniteCoefficientDerivedCategoryPlus` is `DerivedCategory.Plus` of exactly that
   category and localization. The recorded standard t-structure characterizes it by
   existence of an integer lower bound and vanishing of all smaller cohomology objects.
8. `finiteCoefficientEtaleRingSheaf` is
   `(constantSheaf T.smallEtaleTopology RingCat).obj (RingCat.of Λ)`, the required
   sheafification of the constant ring presheaf. `FiniteCoefficientEtaleDerivedCategory`
   uses `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, the standard
   fixed-coefficient presentation used by the recorded derived-categories dependency.
   `finiteCoefficientEtaleRealization` constructs its canonical identification with
   `ringedSiteModules` of this ring sheaf: reinterpret a module-valued diagram as modules
   over the constant ring presheaf, then use `PresheafOfModules.sheafification` along
   `toSheafify`. The named theorem `finiteCoefficientEtaleRealization_isEquivalence`
   states the identification for arbitrary left coefficient rings, with its proof postponed.
   For commutative rings the derived-category type is definitionally the recorded
   `AlgebraicGeometry.Etale.DerivedCategoryModule Λ T`.
9. `finiteCoefficientConstants` sends a scalar to its actual constant continuous function;
   `finiteCoefficientScalarMap` composes it with the coefficient sheafification unit.
   `finiteCoefficientModulePresheaf` is the actual diagram-to-constant-ring-module-presheaf
   functor. `finiteCoefficientRealization` is its composite with associated-module
   sheafification along that scalar map. Its objects and morphisms have real constructions;
   neither a selected arbitrary functor nor a bare `Nonempty` equivalence is used.
10. `finiteCoefficientComparison` is the existing
    `ProEtale.comparisonUpperStar (ModuleCat Λ) T`, the left functor of the recorded
    `Scheme.proEtaleSiteComparisonModules`, followed by this canonical ringed realization.
    Exactness and additivity of realization are named obligations. The comparison inherits
    its additive and finite-limit/finite-colimit preservation instances from its two factors.
    `finiteCoefficientDerivedComparison` is exactly
    `(finiteCoefficientComparison T Λ).mapDerivedCategory`: termwise application followed
    by localization, using the recorded exact-functor derived construction.
11. `isBoundedConstructibleFiniteCoefficient` uses `ObjectProperty.map` under that derived
    comparison. Unfolding `ObjectProperty.map` says precisely that there exist an etale
    complex `L` satisfying the displayed criterion and a `Nonempty` isomorphism from its
    derived inverse image to the object `K`. This is existential isomorphism membership,
    not a choice of a map or a condition identifying different objects by equality.
12. The etale criterion is inline in that one property because the item explicitly gives
    the criterion for noncommutative rings, whereas the cited constructible-complexes
    declaration has `[CommRing Λ]`. It requires, for every `j : ℤ`, a
    `Scheme.LocallyClosedStratification T`; `Fin S.n` supplies finiteness and the structure
    supplies disjoint locally closed parts, their union, realizing schemes and immersions.
    `Topology.IsConstructible (S.stratum k)` is required for every stratum. Pull back the
    `j`-th cohomology sheaf along `S.immersion k` with `Etale.upperStar`; a
    `Scheme.LocallyConstantDatum` gives the etale cover; on each covering member an
    `M : ModuleCat Λ`, `Finite M`, and a sheaf isomorphism to `(constantSheaf ...).obj M`
    supply exactly the finite left-module values. Finally `∃ a b : ℤ, a ≤ b ∧ ...` and
    `IsZero` give cohomology vanishing for `i < a ∨ b < i`. A scratch compilation checks
    by `rfl` that, for `[CommRing Λ]`, the entire resulting pro-etale property equals
    `(Etale.DerivedCategory.isBoundedConstructible Λ T).map
    (finiteCoefficientDerivedComparison T Λ)`. Thus the commutative criterion is exactly
    the recorded criterion, including finite values rather than a stalkwise substitute.
    No second independent constructibility declaration is introduced.
13. `FiniteCoefficientBoundedConstructibleDerivedCategory` is the property's
    `FullSubcategory`. Like `DerivedCategory.Plus`, it has all the ambient morphisms
    between its objects. Essential-image membership is invariant under isomorphism by
    construction, so the subcategory is strictly full.

Recorded dependency declarations read and used (including through their defining formulas):

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its existing
  `Scheme.ProEt`/`Scheme.ProEt.topology` site and standard localization convention.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent specialization of `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard` and the quasi-isomorphism localization.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.Plus`
  and its standard cohomological lower-bound characterization.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and its upstream coefficient import:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the existing fixed-ring etale encoding.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`, whose left
  module functor is the existing `ProEtale.comparisonUpperStar` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, its termwise localization characterization.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification` and `Topology.Stratification`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, with its recorded
  `Scheme.IsConstructibleEtaleModuleSheaf`; the commutative specialization is checked
  definitionally as described above.

The existing site-comparison and bounded-constructible modules publicly import the needed
recorded dependency modules, so additional redundant imports are unnecessary. The item's
`proof_deps` is empty. The pro-etale framework note `coord/pefw-upstream-framework.md` and
its finite-coefficient/module-object distinction were read; no condensed-module or adic
coefficient category is substituted for the finite ringed module category here.

Three named construction obligations remain `sorry`, all owned by this definition node,
listed in `lean.declarations`, and supplied with source and complete proof docstrings:

- `finiteCoefficientScalarMap_locallyBijective`: open level sets of continuous functions
  to a discrete ring give local surjectivity; evaluation gives local injectivity, with
  the empty covering for empty objects; compose with the sheafification unit.
- `finiteCoefficientEtaleRealization_isEquivalence`: locally constant scalars extend
  and glue uniquely to the constant ring sheaf, giving inverse equivalences on modules
  and linear morphisms.
- `finiteCoefficientRealization_exact`: associated-module sheafification along the
  locally bijective scalar map identifies the two module-sheaf presentations; the
  sectionwise additive equivalence preserves finite limits and colimits.

All definitions have actual data; the proof obligations are named separately rather than
placed as `sorry` data or anonymous missing proofs inside a definition.

Edge cases checked against the formulas and proof plans: the empty scheme and empty site
objects (empty covers handle constant-scalar injectivity); disconnected schemes and
non-discrete component spaces (the quotient topology is retained); the zero coefficient
ring and zero module; noncommutative finite rings (all scalar actions are left actions);
zero complexes (any interval such as `[0,0]` suffices); equal endpoints `a = b`;
negative cohomological bounds and arbitrary integer degrees; the empty stratification
`n = 0` when the underlying scheme is empty; independent trivializing covers on different
strata and different cohomology sheaves. No Noetherian, quasi-compact, quasi-separated,
connectedness, nonempty, or characteristic hypothesis is introduced.

Searches performed before choosing constructions:

- `msearch.py` LeanFinder, query `finite coefficient ring sheaf continuous maps connected
  components pro etale derived bounded constructible modules`: 8 hits, including
  `CompHausLike.LocallyConstantModule.functor`, `SheafOfModules.IsFiniteType`, condensed
  module constructions, and unrelated scheme limits. None states this definition.
- `msearch.py` Loogle, query `ConnectedComponents, ContinuousMap, SheafOfModules`: 0 hits.
- `msearch.py` grep in `Algebra/Category/ModuleCat`, query
  `constant.*(equiv|Equiv)|equiv.*(Module|module)|ConnectedComponents`: general linear
  equivalences and the associated-module-sheaf adjunction, no complete coefficient
  definition or finite constructible essential-image predicate.
- `rg` in the source project's `WeilConjectures` finds blueprint-id mentions in
  `SixFunctors/ProEtale/Derived/Constructible.lean` and `TraceFormula/Defs.lean`.
  The former was read in full: its etale-origin predicate uses the source's
  finitely-generated-stalk constructibility, so it is not the recorded finite-constant-value
  criterion; its ambient category is fixed coefficient sheaves, not the explicit ringed
  presentation being defined here. The adic module category was also inspected and is
  a different coefficient construction.
- `rg` over `lean/Sheaf`, Mathlib and the source tree for the new declaration names
  `finiteCoefficientModulePresheaf`, `finiteCoefficientScalarMap`, and
  `finiteCoefficientRealization`: no existing declaration. The project's recorded
  pro-etale derived category, ringed modules, comparison, strata and commutative
  constructibility definitions were read and reused, not recopied.
- `msearch.py` LeanFinder, query `bounded constructible etale complexes finite
  noncommutative ring left modules finite constant values stratification`: 8 unrelated
  etale-algebra hits, no more general matching finite-value predicate.
- `msearch.py` LeanSearch, query `sheaves of modules over constant ring sheaf equivalence
  sheaves valued in modules`: service unavailable, Internal Server Error. This is recorded
  as unavailable; the other searches and source inspection provide the search evidence.
- `msearch.py` grep in `AlgebraicGeometry/Sites`, query
  `finiteCoefficient|boundedConstructible|ConnectedComponents`: found
  `AlgebraicGeometry.continuousMapPresheafEquivOfTotallyDisconnectedSpace`, whose complete
  source was read. It is a set-valued equivalence for continuous functions on underlying
  schemes, not this RingCat coefficient sheaf or module/derived construction. The existing
  `Continuous.connectedComponentsMap` and quotient-topology API are used for the new
  ring-valued functor's specified objects and restrictions.
- `tools/blueprint_refs.py search 'finite ring'` and DAG grep for noncommutative
  coefficients: the item's explicit noncommutative clause is the needed definition;
  no additional independent notion needs a new node. The existing commutative predicate
  is exactly its commutative specialization, as checked by reduction.

Validation uses only `scompile.py`. The final module compiles file by file under the
normal 60-second limit, two threads, nice 19, with no non-sorry warning. A scratch file,
excluded from delivery, verifies the commutative criterion by `rfl` and checks the explicit
finite-ring and universe binders. The worker's final step is the prescribed
`deliver2.py NG def-weil-pbc-proetale-modules --no-push`; its result is recorded below.

Dry-run result: `OK (dry run)` — the module compiles and passes preflight except for the
independent second-reading section, which the delivery tool explicitly leaves to the
second reader. Nothing was pushed. The first checked dry-run commit was `7a955c3fda`;
the final dry run repeats the checks after recording this result.

## Second reading by NG

I am the independent second reader, not the author of the module. I read the sandbox
node and the complete Lean module together, the recorded dependency nodes and their
declarations, and the original blueprint definition. The blueprint file is absent from
the local literature mirror, so I read its exact source on the project server. It defines
the continuous-function coefficient sheaf, its module and derived categories, lower
boundedness, and the essential image of bounded constructible etale objects, without
any Noetherian, characteristic or nonemptiness assumption. I also read the surrounding
Stacks source for the auxiliary constructions: sites-modules.tex, definition-sheaf-modules
and lemma-abelian (03CV/03DA), and derived.tex, definition-unbounded-derived-category
(05RU) and lemma-right-derived-exact-functor (015F). These require an arbitrary ringed
site or abelian category, and an exact functor, respectively. Their assumptions introduce
no additional scheme hypotheses here. The expanded node agrees with this source.

My object/hypothesis/clause checklist, in node order:

1. Arbitrary scheme and finite discrete left coefficient ring: `T : Scheme.{u}` and
   `Λ : Type (u + 1)` with `[Ring Λ] [Finite Λ] [TopologicalSpace Λ]
   `[DiscreteTopology Λ]`. Verdict: exact. In particular no commutativity, nonzero-ring,
   invertible-characteristic or scheme finiteness hypothesis appears. The named section
   variables bind every variable of the intermediate definitions.
2. The recorded small pro-etale site and its size convention: `T.ProEt` and
   `Scheme.ProEt.topology T`, imported through `ProEtaleDerivedCategory` and
   `ProEtaleSiteComparison`. I opened the Mathlib site declarations: objects are the
   weakly etale schemes and the topology is the specified fpqc topology. Verdict: the
   existing site is used; object universe `u + 1` and arrow universe `u` are retained.
3. Connected components with the quotient topology: `ConnectedComponents U.unop.left`
   inside `finiteCoefficientPresheaf`. Mathlib's Connected/Clopen.lean defines this as
   the quotient by equality of connected components, equips it with the quotient
   topology, and supplies `isQuotientMap_coe`. Verdict: exact, including spaces whose
   component quotient is not discrete.
4. Continuous functions, pointwise ring structure and contravariant restrictions:
   `RingCat.of C(ConnectedComponents U.unop.left, Λ)` and the `s.comp` formula using
   `f.unop.left.continuous.connectedComponentsMap`. I read that induced map's definition
   and continuity statement. Verdict: correct objects, arrow direction, identity and
   composition; no chosen component representatives enter the data.
5. Specified coefficient sheaf: `finiteCoefficientRingSheaf` is `presheafToSheaf` applied
   to that very ring-valued presheaf. Verdict: actual sheafification as required, not a
   substituted constant sheaf with its identification left unspecified.
6. Left module sheaves, sectionwise linear morphisms and their abelian category:
   `FiniteCoefficientModules` uses the recorded `ringedSiteModules` of precisely that
   ring sheaf. I opened its transparent `SheafOfModules` definition, the underlying
   `PresheafOfModules` semilinear restrictions, and their `Hom` definitions. Verdict:
   correct general ringed-site category, rather than structure-sheaf modules on a scheme.
7. Unbounded integer cochain localization and cohomology:
   `FiniteCoefficientDerivedCategory` is `DerivedCategory` with
   `HasDerivedCategory.standard`; Mathlib's definition localizes
   `CochainComplex _ ℤ` at `HomologicalComplex.quasiIso`. The later named instance uses
   the same standard localization, so `finiteCoefficientDerivedComparison` has exactly
   this codomain. Verdict: correct localization and cohomology, without completion or
   boundedness built into the ambient category.
8. Lower bounded strictly full subcategory: `FiniteCoefficientDerivedCategoryPlus` is
   `DerivedCategory.Plus` of the same modules and localization. I read its definition as
   the full subcategory of the standard t-structure's `plus`, and the cohomology
   characterization of `IsGE`. Verdict: precisely an integer lower bound, with all
   smaller cohomology objects zero; all ambient morphisms are retained.
9. Etale coefficients and derived category: `finiteCoefficientEtaleRingSheaf` is
   `constantSheaf` of `RingCat.of Λ`. `FiniteCoefficientEtaleDerivedCategory` uses the
   recorded fixed-ring sheaf encoding. `finiteCoefficientEtaleRealization` explicitly
   constructs the passage to modules over that ring sheaf, and its named equivalence
   obligation covers noncommutative rings. Verdict: correct presentation; for commutative
   rings the derived type is the recorded `Etale.DerivedCategoryModule Λ T`.
10. Canonical comparison and termwise derivation: `finiteCoefficientConstants` and
    `finiteCoefficientScalarMap` use actual constant functions and the sheafification
    unit. `finiteCoefficientModulePresheaf` retains the given module diagram.
    `finiteCoefficientRealization` uses Mathlib's associated-module-sheaf construction
    along that scalar map. `finiteCoefficientComparison` composes the recorded
    `comparisonUpperStar (ModuleCat Λ) T` with this realization, and
    `finiteCoefficientDerivedComparison` applies `mapDerivedCategory` to that exact
    functor. I read the comparison module, its exactness instances, and
    `mapDerivedCategoryFactors`. Verdict: the specified inverse image is used, with
    real canonical maps and independently named exactness obligations.
11. Etale origin and quantifier order: `ObjectProperty.map` in
    `isBoundedConstructibleFiniteCoefficient` expands to an existential etale object
    `L`, its property, and `Nonempty ((finiteCoefficientDerivedComparison T Λ).obj L ≅ K)`.
    Verdict: exactly the required isomorphism and essential image, not equality or
    merely an unspecified comparison map.
12. Every clause of the etale property: for each integer `j`, the formula chooses a
    `Scheme.LocallyClosedStratification T`, explicitly requires
    `Topology.IsConstructible (S.stratum k)`, and pulls the `j`th cohomology sheaf back
    along `S.immersion k`. `LocallyConstantDatum` supplies an etale cover; for every
    member the formula supplies `M : ModuleCat Λ`, `Finite M`, and an isomorphism to
    its constant sheaf. The datum's constancy field is implied by these very
    isomorphisms, so imposes no extra condition. Finally `∃ a b : ℤ, a ≤ b ∧ ...`
    imposes `IsZero` in degrees `i < a ∨ b < i`. Verdict: all finiteness,
    constructibility, restriction, local trivialization and vanishing clauses are
    present, in the correct order. On commutative coefficients this reduces to the
    existing `Etale.DerivedCategory.isBoundedConstructible` criterion.
13. Fullness: `FiniteCoefficientBoundedConstructibleDerivedCategory` is the resulting
    property's `FullSubcategory`, and `ObjectProperty.map` is invariant under ambient
    isomorphism. Verdict: strictly full with exactly the ambient derived morphisms.

Edge cases: empty scheme, empty site object, zero ring, zero modules and zero complexes
are included. In the local-bijection proof plan, unequal constant sections on the empty
object are locally equal on its empty covering; no evaluation at a nonexistent point
is required. Empty stratifications (`S.n = 0`) are possible exactly when their union
condition allows them. Covers and stratum choices may differ for each cohomological
degree. Arbitrary negative degrees, coincident bounds `a = b`, and all characteristics
are permitted. There is no nonempty index or connectedness assumption. Module values
and coefficients use the larger site universe; every finite ring or finite module
admits a representative there. No equality of the distinct site universes is imposed.

Independent duplicate searches (different queries from the first reader):

- LeanFinder, `associated sheaf constant scalar ring action locally constant functions
  finite coefficients etale origin cohomology`: eight hits, principally
  `CompHausLike.LocallyConstantModule.functor` and the scheme tilde construction.
  These do not define the ringed pro-etale category or this etale-origin predicate.
- Loogle, `PresheafOfModules.sheafification`: twelve hits for the existing canonical
  construction, its adjunction and finite-limit API. I read the full source and
  confirmed the module uses that construction directly.
- Mathlib grep, `constant|equivalence` in `Algebra/Category/ModuleCat/Presheaf`: two
  ColimitFunctor hits, neither the diagram-to-constant-ring-module construction here.
- `rg` over both project source trees and `lean/Sheaf`, using `ConnectedComponents`,
  `boundedConstructible`, `constant.*[Rr]ing`, `[Rr]ing.*constant` and the new declaration
  names: no exact duplicate. I opened upstream ProEtale/Derived/Constructible.lean;
  its fixed-coefficient essential image uses the separate finitely-generated-stalk
  predicate, whereas this node requires the recorded finite-constant-value predicate
  and explicit ringed coefficient sheaf. I also read the framework note and the
  delivered ModuleObject/Basic and ProEtaleModule/Def interfaces: condensed pullback
  ring objects and intrinsic local finite presentations are different constructions.
- LeanSearch, `The category of sheaves of modules over the associated constant ring
  sheaf is equivalent to sheaves valued in modules over that ring`: unavailable,
  Internal Server Error. This is an unavailable service, not negative search evidence.

There are no new nodes, dependency modules, or statement corrections in this delivery.
The three postponed construction theorems are named, listed in `lean.declarations`, and
have complete source/blueprint proof docstrings. Their statements are the local
bijection of the specified scalar map, equivalence of the etale presentations, and
exactness of the specified pro-etale realization. All data definitions are actual
constructions. Every theorem proof remains `sorry`; functor-law fields are construction
data. The declaration docstrings, imports, 100-character lines, and explicit binders
were checked. The node's `lean.statement` matches the primary signature verbatim.

Mismatch and repair verdict: no mathematical or implementation mismatch was found.
I left the Lean and node unchanged and added only this independent review report.
The prescribed `scompile.py` invocation compiled the delivered module cleanly, with
no errors or non-sorry warnings. Final dry-run and delivery results follow below.

The scratch `CommCriterionCheck.lean` also compiled through `scompile.py`, separately
with the delivered module supplied as an overlay dependency: its `rfl` comparison with
the recorded commutative criterion passed, and its printed signatures confirmed the
explicit finite-ring and universe binders. The scratch file is excluded from delivery.
The second reader's `deliver2.py NG def-weil-pbc-proetale-modules --no-push` returned
`OK (dry run)`: commit `d569529510` passed preflight and compilation. Only this validation
paragraph was appended afterward; the final delivery wrapper rechecks the report.
