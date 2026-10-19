## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula` states
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_integral_of_isProper`.
Its sole theorem has proof `by sorry`; no definition or auxiliary theorem is introduced.
Only the item's `lean` field is changed. No statement correction is needed.

Source checked: [Stacks, Tag 0F0F, Lemma 59.92.5](https://stacks.math.columbia.edu/tag/0F0F).
This is exactly the node's integral, bounded-below proper projection formula. In the Stacks
proof the displayed inequalities `i ≥ a` and `j ≥ b` have the wrong direction for a lower
bound; the DAG proof already uses `i < a` and `j < b`. The statement is unaffected. The
module docstring carries the node's five-step proof, including the absolute qcqs fibre
argument and compatibility of the actual counit-mate map with the constant-complex map.

Hypothesis-by-hypothesis and clause-by-clause reading:

- Schemes `X,Y` and a morphism `f : X → Y` are `{X Y : Scheme.{u}} (f : X ⟶ Y)`;
  the universe `u` is explicitly declared and unrestricted.
- Properness is precisely `[IsProper f]`. This is the recorded Mathlib notion: separated,
  universally closed, and locally finite type; universal closedness supplies quasi-compactness,
  so this is the node's finite-type properness. There is no Noetherian, absolute qcqs,
  finite-dimensional, coefficient-finiteness, or characteristic assumption.
- `E ∈ D⁺(X_et)` is the binder `E : DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))`.
- `K ∈ D⁺(Y_et)` is the identical binder over `Y`. Its cohomology need not be torsion.
- The integral coefficient category is encoded by modules over `ULift.{u + 1} ℤ`.
  The ring is the universe lift of ℤ, not a variable coefficient ring or a quotient.
  Its canonical action on any abelian group is unique: transport along `ULift.ringEquiv`
  gives the unique ℤ-action. Linear maps are exactly additive maps. Thus the sheaf and
  derived categories here are the standard module encoding of abelian sheaves, with the
  same integer tensor product; no extra module data restricts the quantified objects.
  The lift is needed because the recorded coefficient and flat-pullback APIs take the
  ring and modules in universe `u+1`. It places no equality constraint on universes.
- The torsion hypothesis is exactly `hE : DerivedCategory.torsionCohomology
  (ULift.{u + 1} ℤ) X E.obj`, from the recorded derived-categories module. Its body says
  that every cohomology sheaf, after forgetting scalars, is locally torsion. It does
  not require a common annihilator, finite stalks, or invertibility of torsion orders.
- The left side `Rf_*E ⊗ᴸ_ℤ K` is
  `((derivedTensorRightDerivedLowerStar (ModuleCat ... (ULift ... ℤ)) f).obj E.obj).obj K.obj`.
  The first conclusion applies `DerivedCategory.TStructure.t.plus` to this very object.
- The right side `Rf_*(E ⊗ᴸ_ℤ f⁻¹K)` is
  `((rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  (ModuleCat ... (ULift ... ℤ)) f).obj E.obj).obj K.obj`.
  The second conclusion applies the same `t.plus` to this object. The left derived
  upper star here is the exact inverse image, as in the recorded projection-map node
  and `leftDerivedUpperStarIsoMapDerivedCategory`.
- The map itself is exactly the component
  `((rightDerivedLowerStarProjectionMap (ModuleCat ... (ULift ... ℤ)) f).app E.obj).app K.obj`.
  The third conclusion is `IsIso` of this component, not existence of an unrelated
  isomorphism between its endpoints. Reading the upstream definition shows this is
  the derived-adjunction mate of the inverse monoidal comparison followed by counit
  tensored with identity, exactly as specified by `def-kun-projection-formula-map`.
- The phrase “is an isomorphism in D⁺” is rendered by these three conclusions together:
  both endpoints belong to the bounded-below subcategory, and the canonical map is
  invertible. Since `DerivedCategory.Plus` is the full subcategory of `t.plus`, its
  inclusion is fully faithful and reflects isomorphisms. This is equivalent to
  invertibility in D⁺ itself, and does not add a separate geometric assertion.

Statement dependency declarations read and used:

- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; read its class signature and docstring, including the
  quasi-compactness explanation and the definitions of its three fields.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`; read the definition in
  full. Its imported `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` supplies
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and the coefficient-universe convention.
  `DerivedCategory.Plus` and `DerivedCategory.TStructure.t` are the existing Mathlib
  definitions in `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, also read.
- `def-kun-projection-formula-map`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`, and its two endpoint
  bifunctors `derivedTensorRightDerivedLowerStar` and
  `rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar`. Read their complete
  signatures, docstrings and defining expressions, and the transpose equation
  `homEquiv_symm_rightDerivedLowerStarProjectionMap`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` supplies the existing
  coefficient instance `AlgebraicGeometry.Etale.upperStarPreservesFlat_moduleCat`.
  Its signature and source show why specializing to the lifted integers needs no
  new hypothesis. No recorded dependency needs a repair module.

The module imports all proof-dependency modules with a recorded Lean module, except that
statement dependencies are already public imports. For the Mathlib-only proof leaves it
also imports `Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`Mathlib.CategoryTheory.Sites.Point.Basic`,
`Mathlib.CategoryTheory.Sites.Point.Skyscraper`, and
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
The two unstated proof lemmas `lem-kun-integral-derived-tensor-bounded-torsion` and
`lem-kun-0f0e` are not needed to *state* this theorem, and have no module to import.
The convention node `def-weil-pbc-scheme-conventions` also has no recorded module.
They remain named in the proof docstring. No import or declaration awaits their proofs.

Edge cases checked before writing: `E=0` or `K=0` gives zero endpoints and an isomorphism;
empty source or target schemes impose no extra side conditions; negative lower bounds
and arbitrary shifts are allowed by `Plus`; the integer tensor may start in degree
`a+b-1`, so no erroneous `a+b` bound is asserted. Torsion is required only of the first
factor and only elementwise locally; arbitrary non-torsion `K`, varying torsion orders,
and every residue characteristic remain covered. General proper maps are allowed,
without qcqs assumptions on `Y`. The proof establishes qcqs only for geometric fibres.

Searches for an existing statement (all performed in this session):

- `msearch.py leanfinder`: “Projection formula for proper pushforward of bounded below
  etale complexes of abelian groups with torsion cohomology”. Eight results concerning
  complex factorizations, derived single objects, profinite groups, affine limits,
  projective resolutions, Mayer–Vietoris and etale morphisms; none is the assertion.
- `msearch.py loogle`: `"projectionFormula", "IsProper"`. No hits.
- `msearch.py grep`: `projectionFormula|projection_formula|projection.*formula`,
  subdirectory `AlgebraicGeometry`. No hits.
- `msearch.py leansearch`: “Integral projection formula for proper morphisms and bounded
  below torsion etale complexes”. Service unavailable, Internal Server Error. The
  available semantic, name and source searches above supply the results instead.
- `rg` over upstream `WeilConjectures/` and project `lean/Sheaf/` for
  `projectionFormula|projection_formula|rightDerivedLowerStarProjection|lem-kun-0f0f`.
  Found the canonical map and existing finite-coefficient or dualizable-factor formulas.
  Read `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`, especially
  `isIso_rightDerivedLowerStarProjectionMap_of_finite`, and the project module
  `Sheaf.AlgebraicGeometry.ProperProjectionFormula`. Neither states the integral
  torsion-cohomology formula: the former requires finite coefficients, and the latter
  additionally uses reordered tensor factors and finite coefficients. The pro-etale
  comparison results and trace-framework fields likewise do not state this node.
- Checked the new declaration's full name against `dag/lean_names_upstream.json`,
  Mathlib, upstream `WeilConjectures/`, and project `lean/Sheaf/`: no occurrence.
- Checked whether abelian groups already have the tensor monoidal interface used by
  the recorded map: only the separate cartesian monoidal definition was found.
  The recorded module-coefficient specialization, with lifted integers, is therefore
  used directly rather than constructing a duplicate tensor or projection map.

Validation: the delivered file compiled cleanly through
`scompile.py Q17 lem-kun-0f0f`; the wrapper checked the sandbox and the library module
separately under the normal 60-second limit (7.0 and 8.8 seconds). No errors or warnings.
There is no STATEMENT-DISPUTED finding and no outstanding dependency-interface fault.
The independent second reading is reserved for the second worker.

## Second reading by Q17

I independently opened the sandbox node and complete module, the three statement-dependency
nodes and their recorded declarations, and Stacks Tag 0F0F. The local shared literature
checkout has no `stacks-project/` directory. I read the actual Stacks TeX at
`/home/ubuntu/weil-launcher-nt/reviews/Q27__lem-kun-0f1c-exchange__348540e5e7e4/sources/etale-cohomology.tex`,
lines 19000–19053 (`lemma-projection-formula-proper`), together with the opening of
`section-applications-proper-base-change` at line 18762. I also checked the published
[Tag 0F0F](https://stacks.math.columbia.edu/tag/0F0F). The section imposes no standing
Noetherian, qcqs, characteristic, or finite-dimension assumptions. The adjacent lemmas'
separate hypotheses do not apply to this lemma. The lower-bound inequalities in the
Stacks proof are a typographical error already resolved in the DAG proof; the node's
statement agrees exactly with the source.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

| Node item | Lean rendering checked | Verdict |
| --- | --- | --- |
| Two schemes and their morphism | `{X Y : Scheme.{u}} (f : X ⟶ Y)` | Exact; arbitrary scheme morphism before properness. |
| The morphism is proper | `[IsProper f]` | Exact; read the Mathlib class in `Morphisms/Proper.lean`: separated, universally closed, locally finite type. Universal closedness supplies quasi-compactness, so this is finite-type properness. |
| Abelian sheaves on each small etale site | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))`, and similarly for `Y` | Exact coefficient encoding. The initial ring `ULift ℤ` is ring-isomorphic to `ℤ`; each abelian group has a unique such scalar action, and additive maps are automatically linear. This preserves the integer tensor product, not a finite-coefficient or completed tensor. |
| `E ∈ D⁺(X_et)` | `E : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat ...))` | Exact; read Mathlib `Plus`, the full subcategory for `TStructure.t.plus`. No bounded-above requirement. |
| `E` has torsion cohomology | `hE : DerivedCategory.torsionCohomology (ULift.{u + 1} ℤ) X E.obj` | Exact; opened `Sheaf.AlgebraicGeometry.DerivedCategories`. Its body quantifies over every integer degree and applies `Sheaf.IsTorsion` after forgetting scalars. Opened that predicate too: sections become finite-order locally on a covering sieve; no uniform annihilator is required. |
| `K ∈ D⁺(Y_et)` | The second `DerivedCategory.Plus` binder over `Y` | Exact; neither torsion nor finite Tor amplitude nor constructibility is imposed on `K`. |
| Source `Rf_*E ⊗ᴸ_ℤ K` | `((derivedTensorRightDerivedLowerStar (ModuleCat ... (ULift ... ℤ)) f).obj E.obj).obj K.obj` | Exact; opened the bifunctor's definition: right derived direct image followed by ordinary derived tensor, in this order. |
| Target `Rf_*(E ⊗ᴸ_ℤ f⁻¹K)` | `((rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar (ModuleCat ... (ULift ... ℤ)) f).obj E.obj).obj K.obj` | Exact; read this definition and `leftDerivedUpperStarIsoMapDerivedCategory`, which identifies its derived upper star with exact termwise inverse image. |
| The specified canonical projection map | `((rightDerivedLowerStarProjectionMap (ModuleCat ... (ULift ... ℤ)) f).app E.obj).app K.obj` | Exact; read its definition and transpose equation. It is the mate of inverse-image tensor comparison followed by counit tensored with identity under `derivedUpperStarLowerStarAdjunction`. No arbitrary isomorphism replaces this arrow. |
| Isomorphism in `D⁺(Y_et)` | First and second conjuncts assert `TStructure.t.plus` of the displayed source and target; third conjunct is `IsIso` of that map | Exact; these assert both endpoints belong to the full bounded-below subcategory and its map is invertible. The fully faithful inclusion reflects isomorphisms, so the three conjuncts express precisely the node's conclusion. |

The order of quantification is schemes/morphism/properness, the two bounded-below
objects, then the torsion hypothesis for `E`. Moving a proof of this property after
`K` does not change which objects are quantified or the implication. Every binder is
explicitly bound; `universe u` is declared, and `relaxedAutoImplicit = false` is enforced
by compilation. No extra coefficient, geometric, or size hypothesis occurs.

Dependency-interface review: `def-weil-proper-morphism` uses the exact Mathlib class
above; `def-weil-pbc-derived-categories` supplies the actual torsion predicate and its
six-functor module-sheaf encoding; `def-kun-projection-formula-map` records the exact
upstream map read in `LowerStarProjection.lean`. I read the latter's endpoint
bifunctors, `rightDerivedLowerStarProjectionMap_app_app`, and
`homEquiv_symm_rightDerivedLowerStarProjectionMap`, and the derived adjunction in
`UpperLowerStar.lean`. The recorded coefficient hypotheses are discharged for
`ModuleCat (ULift ℤ)` without extra assumptions: in particular I opened
`UpperLowerStar/FlatModuleCat.lean` and checked its global
`upperStarPreservesFlat_moduleCat` instance. There is no missing notion, unusable
statement dependency, private copy, new definition node, or dependency repair module.
The proof dependencies with no module remain proof tasks, not prerequisites to typing
this statement. All recorded proof modules are imported; the geometric-stalk exactness
Mathlib leaf lists three files, each present separately among the imports.

Edge cases: both zero objects are permitted; tensoring with either gives zero and
proper direct image of zero is zero. Empty schemes are permitted and no `Nonempty`
instance or geometric point is an assumption. There is no index-set binder to restrict.
The degree-zero case and arbitrary negative shifts are covered by the standard
bounded-below subcategory; no fixed numeric lower bound is claimed. The usual integer
Tor contribution at degree `a+b-1` is retained in the proof, with no false `a+b` bound
in the statement. Coefficient characteristic is zero because this is the integer
formula, while schemes of every characteristic and torsion at every prime remain
allowed. Arbitrarily large stalks fit by increasing `u`; the ring lift supplies the
required `u+1` coefficient universe without equating site object and morphism
universes. The sizes agree with the recorded derived-category and projection-map APIs.

Independent searches, using different words from the worker (recorded by `msearch.py`
in this sandbox's `searches.jsonl`):

- LeanFinder: “Derived direct image along a proper scheme morphism commutes with derived
  tensor of bounded below integral etale sheaves when the first factor has torsion
  cohomology”. Eight hits, all ordinary module pushforward composition/adjunction
  declarations, none a derived integral projection formula.
- Loogle: `"rightDerivedLowerStar", "IsIso"`. Zero hits.
- Mathlib grep: `proper.*tensor|torsion.*projection|projection.*torsion` in
  `AlgebraicGeometry`. Two hits concerning commutativity of proper algebraic groups,
  neither about sheaf tensor or derived direct image.
- LeanSearch: “Proper direct image projection formula for bounded below complexes of
  etale abelian sheaves with torsion cohomology over Z”. Service returned Internal
  Server Error, recorded as unavailable; the other searches completed.
- Direct `rg` over Mathlib, upstream `WeilConjectures/`, project `lean/Sheaf/`, and the
  upstream-name index for the proposed full declaration name: absent.
- Direct conceptual `rg` over upstream and project modules for
  `projection.*(integral|torsion)|integral.*projection|isIso_rightDerivedLowerStarProjectionMap`.
  I opened the finite-coefficient upstream theorem in `Derived/ProjectionFormula.lean`,
  the project's `ProperProjectionFormula.lean`, and `ProperTorsionProjectionFormula.lean`.
  The first two require finite coefficient rings (and the reordered project theorem
  adds geometric assumptions); the third requires an additive-torsion coefficient
  ring and treats unbounded objects. None applies to `ℤ` with only `E` having torsion
  cohomology. The adic/integral and pro-etale results are different coefficient/site
  notions. Thus this statement is not already present.

H5/H6/H8/H9 inspection: the module introduces one theorem, whose entire proof is
`by sorry`, and no definition. Both module and theorem docstrings give Tag 0F0F and
`(blueprint: lem-kun-0f0f)`. The theorem docstring includes all five DAG proof steps:
integer tensor lower bound and torsion; qcqs geometric fibre; canonical proper
base-change/naturality square; the constant-complex formula and compatibility of its
actual arrow; and stalk conservativity. Namespace and imports follow the conventions,
there is no local notation or instance, and every Lean line is at most 100 characters.
I compared the JSON `lean.statement` directly with the theorem signature up to `:=`:
they are verbatim equal. The shared node and sandbox node differ only in `lean`.

Mismatches and changes: none in the statement, dependencies, or Lean module. I retained
all correct material and appended this independent reading only. No `statement_change`
is needed, so no citer audit is triggered. No disputed statement remains.

Validation: `scompile.py Q17 lem-kun-0f0f` with the absolute sandbox module path compiled
both sandbox and library forms cleanly, 5.4 seconds each under the required 60-second
limit. No errors or warnings. An initial invocation with a repository-relative path
could not locate the sandbox file; using its absolute path resolved that invocation
error without any compiler or source change. The required delivery dry run and push
follow this reading.
