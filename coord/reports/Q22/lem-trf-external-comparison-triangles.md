## Worker report

Item: `lem-trf-external-comparison-triangles`, Q22, 2026-10-17.
Module: `Sheaf.Paper.ExternalComparisonTriangles`.
Main declaration: `AlgebraicGeometry.Etale.externalComparison_triangles`.
The only postponed declaration is this theorem, with proof `sorry`. Four public helpers
name the two functors and the prescribed maps; their data is fully constructed. No
statement, proof, dependency list, or other mathematical field of the DAG item was changed.
No new independent notion is introduced, so no new definition node is needed. The helpers
belong to the comparison being stated, under the canonical-map permission of the brief.

Source read: the complete current blueprint file
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/lem-trf-ordinary-kunneth.proof.md`,
in particular the displayed comparison before Step 1 and Step 2's exactness in Q.
The DAG item's eight proof steps are reproduced as a proof plan in the theorem docstring.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; the three schemes are `{X Y Z : Scheme.{u}}`.
  `b : Y ⟶ Spec k` and `c : Z ⟶ Spec k` are their structure maps. The structure map
  of X is `f ≫ b`, with `f : X ⟶ Y`. This parametrizes precisely k-morphisms: a
  compatible separately named structure map of X is equal to this composite. No finite
  type, separatedness, Noetherian, properness, smoothness or coefficient torsion assumption
  is added.
- Small etale sites are `T.smallEtaleTopology` on `T.Etale`. Scheme and field universes
  are u, coefficients and sheaf module values are u+1, and derived objects lie in u+2.
  This is the existing six-functor encoding and size convention, without equating
  independent object and morphism sizes of a site or imposing a new smallness hypothesis.
- The coefficient ring is `(A : Type (u + 1)) [CommRing A]`; no nontriviality is required.
  The module derived category for L is the recorded `DerivedCategoryModule A X`.
- The hypothesis on L is `_hL : ∃ (a b : ℤ) (P : CochainComplex ... ℤ),
  IsBoundedFlatComplex A a b P ∧ Nonempty (L ≅ DerivedCategory.Q.obj P)`.
  The existing `IsBoundedFlatComplex` definition is the conjunction of zero terms outside
  [a,b] and `∀ q, ObjectProperty.flat (P.X q)`. I read its complete definition and the
  definition of `ObjectProperty.flat`: tensoring on either side preserves finite limits
  and finite colimits. On this symmetric module-sheaf category this is exactly the
  exactness of tensoring in `def-pc-flat-sheaf-modules` / `IsFlatOnSite`, expressed in the
  existing ModuleCat-valued realization used by all three derived-functor dependencies.
  The two tensor functors are naturally isomorphic by symmetry, so requiring both in
  that existing definition adds no hypothesis. No choice of flat model is made in data,
  and L is still an arbitrary derived object admitting such a model.
- The products are `pullback (f ≫ b) c` and `pullback b c`. The four projections are
  their `pullback.fst` and `pullback.snd`. The map h is the existing
  `pullback.mapOverBaseRight f b c`, literally f times the identity of Z. Its two
  projection equations are the published `mapOverBaseRight_fst` and
  `mapOverBaseRight_snd`, not additional assumptions.
- The source domain is exactly `DerivedCategory.Plus (Sheaf Z.smallEtaleTopology
  (ModuleCat.{u + 1} A))`. Both helpers begin with its existing inclusion
  `DerivedCategory.Plus.ι`. The target is the ambient unbounded category on Y times Z.
- `externalComparisonSource` is this inclusion followed by `Lp'_Z{}^*` followed by
  `(derivedTensor ...).obj (Lp_Y^* (Rf_* L))`. Hence its Q-value is precisely F(Q).
- `externalComparisonTarget` is inclusion, `Lp_Z^*`, left tensor with `Lp_X^* L`,
  and then `Rh_*`. Its Q-value is precisely G(Q).
- `externalComparisonExchange` uses the recorded `exactDerivedBaseChangeMap` for
  the square with top p_X, left h, right f and bottom p_Y. Its commutativity proof is
  the symmetry of `mapOverBaseRight_fst`. It is conjugated by the existing
  `leftDerivedUpperStarIsoMapDerivedCategory`: first Lp_Y^* to termwise p_Y inverse
  image, then the recorded exchange, then Rh_* of the inverse comparison for p_X.
  This does not substitute a freely chosen exchange map or assert base change invertible.
- `externalComparisonMap` is exactly three successive factors. First,
  `(derivedTensor ...).map (externalComparisonExchange ... L)` at `Lp'_Z{}^* Q`;
  second, the recorded `rightDerivedLowerStarProjectionMap` at `(Lp_X^* L,Lp'_Z{}^* Q)`;
  third, Rh_* applied to left tensor by Lp_X^* L of
  `(leftDerivedUpperStarComp ... h p'_Z p_Z ...).inv.app Q.obj`.
  The direction of this last inverse is `Lh^* Lp'_Z{}^* Q → Lp_Z^* Q`.
  I read the upstream definition of `leftDerivedUpperStarComp`: it derives the actual
  underived `upperStarComp` termwise and uses exact-functor composition. Thus it is the
  canonical module-linear composition c of the dependency, in the correct direction,
  rather than an arbitrary comparison isomorphism.
- The theorem first asserts `.IsTriangulated` for exactly F and G. Their `.CommShift ℤ`
  instances are the inherited composite structures from inclusion, derived pullback,
  second-variable tensor, and derived direct image. The helpers are abbreviations, so
  there is no independently chosen shift structure.
- Naturality is `∃ α : F ⟶ G, ...` together with `∀ Q, α.app Q = externalComparisonMap ... Q`.
  A natural transformation is a family satisfying every naturality square. The component
  equation fixes that family to the fully constructed three-factor map for every Q;
  the existential does not replace the canonical comparison with a free map.
- The second conjunct inside this existential is, in Lean composition order,
  `α.app (Q⟦1⟧) ≫ s_G.hom.app Q = s_F.hom.app Q ≫ (α.app Q)⟦1⟧'`.
  It is precisely the node's `s_G α_{Q[1]} = α_Q[1] s_F`, with no sign omitted.
- The last clause quantifies over every `Triangle (DerivedCategory.Plus ...)` and
  assumes `T ∈ distTriang _`. It asserts both `F.mapTriangle.obj T` and
  `G.mapTriangle.obj T` distinguished, and a morphism φ between them with
  `φ.hom₁ = α.app T.obj₁`, `φ.hom₂ = α.app T.obj₂`, `φ.hom₃ = α.app T.obj₃`.
  Mathlib's `TriangleMorphism` includes `comm₃`, the connecting square with the shifted
  first component. The component equations prevent substituting an unspecified TR3
  completion for the prescribed third component.
- There is no `IsIso α`, `IsIso (α.app Q)`, or other invertibility conclusion.

Dependency declarations and source inspection:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `def-weil-size-convention` is explicitly a metatheoretic convention without a declaration;
  its existing record was read and its universes are rendered as above.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (read using `scompile.py --source`
  because it is absent in the older source checkout): `Etale.DerivedCategoryModule`;
  Mathlib `DerivedCategory.Plus`, its inclusion and triangulated full-subcategory structure.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`;
  existing ModuleCat-valued expression `Etale.IsBoundedFlatComplex` from
  `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`, as explained above.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `Etale.exactDerivedBaseChangeMap`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap`; I read its definition, its app formula
  and the adjunction-transpose characterization.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`:
  `AlgebraicGeometry.etaleInverseImageCompositionModuleLinear`; I read the docstring and
  full signature, including its underlying abelian map and unit characterization.
  The existing exact-derived realization of this canonical composition is
  `Etale.leftDerivedUpperStarComp` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.
- `Mathlib.CategoryTheory.Triangulated.Functor` / `Basic`: `Functor.IsTriangulated`,
  `Functor.mapTriangle`, `TriangleMorphism` and its three commutativity fields.
- Canonical shift/triangulated instances are the existing ones in
  `WeilConjectures.SixFunctors.Etale.Derived.Shift` and `.Triangulated`.

The recorded statement-dependency modules are imported (the ordinary category/site and
triangulated primitives are also supplied transitively). Modules of the stated proof
inputs for exact functors, K-injectives, right derivation, derived tensor descent and the
projection mate are present as non-public proof imports. The already public
`.Triangulated` import supplies the recorded tensor triangulation input. The module
inverse-image exactness input is already imported by the recorded composition module
through its Sheaf-side version, with the identical full declaration name; adding the
WeilConjectures-side duplicate would be inappropriate. Generic factorization/composition/
whiskering inputs whose records are Mathlib leaves introduce no additional side modules.

Edge cases checked against the construction:

- L = 0 admits the zero flat complex; no nonzero-object premise appears.
- Q = 0 and zero triangles remain included; the asserted component maps have the same
  explicit factorization, even when a factor is zero.
- Empty X, Y or Z and the zero coefficient ring are not excluded. No global sections,
  stalk choice, nonempty scheme, or nontrivial ring is required.
- f = identity is allowed. The product map and pullback-composition comparison are the
  existing canonical ones, so identity coherence is not replaced by extra data.
- For a degree-p first tensor factor and Q shifted by one, the canonical second-variable
  shift has scalar (-1)^p; the fixed degree-zero exchange map preserves it. Odd p is not
  silently treated as even. The triangle image uses exactly this `.commShiftIso 1`.
- A bounded-below Q with no fixed global lower bound is allowed: the domain is D+,
  not a fixed connective subcategory, and the codomain is unbounded.
- Empty intervals a > b are allowed for the zero complex, matching the absence of a
  nonzero flat-model hypothesis. No unnecessary a ≤ b binder was added.

Searches actually run:

1. `msearch.py ... leanfinder` with query "The external tensor base change and direct image
   projection comparison is a natural transformation of triangulated functors commuting
   with shifts": eight generic hits (spectral-object connecting maps,
   `mapTriangleCompIso`, `mapTriangleCommShiftIso`, triangulated-functor restriction APIs);
   none states this particular comparison.
2. `msearch.py ... loogle` with query
   `CategoryTheory.NatTrans.CommShift, CategoryTheory.Functor.IsTriangulated`: eight generic
   isomorphism/derived-functor triangulation results; none is this statement.
3. `msearch.py ... grep` with query
   `external.*triangle|projection.*CommShift|CommShift.*projection` in `CategoryTheory`:
   zero Mathlib hits.
4. `msearch.py ... leansearch` with query "The exchange map followed by the projection
   formula defines a natural transformation of triangulated functors on bounded below
   etale sheaf complexes": eight generic triangle, natural-transformation and sheaf-map
   hits, no external exchange/projection compatibility.
5. `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
   `externalComparison|external.*[Tt]riang|kunneth.*[Tt]riang|Kunneth.*[Tt]riang|lem-trf-external-comparison-triangles`:
   no exact statement found before writing the sandbox module. A direct item-id search
   in upstream and `dag/lean_names_upstream.json` also had no hit.
6. Further source searches found and were followed by full reads of the existing
   projection, exact exchange, tensor, tensor-shift, composition and bounded-flat APIs.
   This is why no duplicate tensor, pullback, projection, shift or flatness definition
   was introduced.

No STATEMENT-DISPUTED issue or statement correction was necessary.
Compilation: the prescribed `scompile.py Q22 lem-trf-external-comparison-triangles <module>`
compiled both sandbox and named library forms cleanly, including after every final import
was added and `set_option autoImplicit false` was enabled (about 11 and 14 seconds).
The only expected proof placeholder is the main theorem's `sorry`.

## Second reading by Q22

Independent maintainer reading of immutable delivery
`4e5f8202186586ebcbbc54e2f806759d46a170e5`, performed on 2026-10-17.
This section replaces the author's explicitly labelled self-check; it does not attribute
an independent group review to the author. The reviewer read the packet, the extracted item
node and all ten statement dependencies, the delivered module, this report, the full source
blueprint proof, and the dependency declarations described below. No project clone was edited.

Hypotheses and objects, checked against the node:

- `Field k`, `Scheme.{u}`, `f`, `b : Y ⟶ Spec k`, and `c : Z ⟶ Spec k` give precisely
  schemes over the same field and a k-morphism, taking the structure map of X to be `f ≫ b`.
  This omits only redundant structure-map equality data. No finite-type, properness,
  Noetherian, separatedness, smoothness, or nonemptiness assumption occurs.
- `(A : Type (u + 1)) [CommRing A]` and `ModuleCat.{u + 1} A` use the recorded six-functor
  realization of constant-coefficient module sheaves. `DerivedCategoryModule A X` unfolds
  to the recorded unbounded derived category. `DerivedCategory.Plus` is the cohomologically
  bounded-below full subcategory, not complexes bounded below by one fixed integer.
  The u/u+1/u+2 sizes follow the dependency encoding; no extra equality of site universes
  is imposed. The size convention is metatheoretic and requires no invented declaration.
- `_hL` supplies integers a,b, a cochain complex P, bounded-flatness, and an isomorphism
  from L to Q(P). I expanded `IsBoundedFlatComplex` in `Derived/Finiteness/FlatModel.lean`:
  all terms outside [a,b] are zero and every term satisfies `ObjectProperty.flat`.
  The latter is exactness of left and right tensor in the sheaf category. Symmetry
  identifies these tests; this is the flatness of Stacks 03ER(3), not sectionwise flatness.
  It is the existing ModuleCat realization of `SheafOfModules.IsFlatOnSite`, not a second
  definition. Neither constructibility nor finite coefficients enters this hypothesis.
- The two products are actual pullbacks over Spec k. `pullback.mapOverBaseRight` is
  constructed using f, identity on Z, and identity on the base. Its published fst/snd
  equations give both required projection identities with no extra premises.

Conclusions and the canonical maps:

- `externalComparisonSource` expands to inclusion of D+, pullback along p'_Z, and
  tensor on the left by p_Y^* Rf_*L. `externalComparisonTarget` expands to inclusion,
  pullback along p_Z, tensor on the left by p_X^*L, and Rh_*. Both land in the ambient
  unbounded category on Y times Z.
- `externalComparisonExchange` first uses the hom of
  `leftDerivedUpperStarIsoMapDerivedCategory` for p_Y, then the recorded
  `exactDerivedBaseChangeMap` on the product square, then Rh_* of the inverse comparison
  for p_X. I read the exact-exchange definition: it is the mate of the termwise square
  isomorphism under the exact-inverse-image/right-derived-direct-image adjunctions.
  The symmetric fst equation has the correct orientation for `CommSq.mk`.
- `externalComparisonMap` is exactly exchange tensor identity, the recorded
  `rightDerivedLowerStarProjectionMap`, and Rh_* of identity tensor
  `leftDerivedUpperStarComp ... .inv`. The last inverse maps h^* p'_Z{}^* Q to p_Z^* Q.
  `upperStarComp` is the adjoint-conjugate of the actual direct-image composition;
  `leftDerivedUpperStarComp` derives it and composes the canonical exact-functor
  comparisons. This agrees with the underlying-comparison and unit characterization in
  `etaleInverseImageCompositionModuleLinear`. No arbitrary map or arbitrary chosen
  isomorphism replaces the canonical composition.
- The two `.IsTriangulated` conjuncts concern these exact functor abbreviations.
  The existing `.Derived.Shift` instances supply pullback by transport from termwise
  inverse image, direct image by the derived adjunction, and second-variable tensor by
  the derived monoidal shift. Composition and the D+ inclusion supply the stated shifts.
- `∃ α : F ⟶ G` asserts naturality, and `∀ Q, α.app Q = externalComparisonMap ... Q`
  fixes every component to the constructed map. This existential has no hollow data.
- The displayed equality is alpha at Q[1], then s_G, equal to s_F, then alpha_Q[1],
  precisely the node's shift equation in Lean composition order.
- For every distinguished triangle T the final conjunct asserts both image triangles
  distinguished and a triangle morphism with all three prescribed components.
  I read `Functor.mapTriangle` (Mathlib `Triangulated/Functor.lean:42`) and
  `TriangleMorphism.comm₃` (`Triangulated/Basic.lean:116`): the former uses the canonical
  shift in its connecting arrow, and the latter includes the shifted first component.
  Thus the connecting square is included. No component is asserted invertible.

Source and proof-docstring audit:

The full `lem-trf-ordinary-kunneth.proof.md` displayed comparison and Step 2 were read.
The helper is about exactness/naturality of that comparison, so it does not inherit the
finite-coefficient hypotheses needed later to prove invertibility. I also read Stacks
`sites-modules.tex:1197,1236,4243` (03D7, 03D8, 03ER), and
`sites-cohomology.tex:3300,3684,13666` (06YU, 07A4, 0B56).
The latter explicitly constructs the projection map without further assumptions.
The theorem docstring follows all eight node proof steps: exact inverse image;
K-injectives/tensor/composition; the three factors; the (-1)^p second-input tensor sign;
the projection mate; termwise composition; composition of shift equations; and the
connecting square. The degree-zero exchange preserves first degree, including odd p,
so it commutes with the sign. The final connecting equation also has the correct order.
Module and all five declaration docstrings identify the source and blueprint node.

Dependency and uniqueness audit:

I opened all ten statement-dependency records and the exact Scheme, small-etale-site,
derived-category, tensor, flatness, exchange, projection, triangulated-functor and
inverse-image-composition declarations. The missing local source of
`WeilConjectures.AlgebraicGeometry.DerivedCategories` was read through
`scompile.py --source`; it confirms the recorded encoding. The composition theorem's
full signature includes the underlying abelian comparison, composite-unit equation,
and uniqueness. The corresponding existing ModuleCat composition is used, not copied.
Independent `rg` searches over Mathlib CategoryTheory, upstream WeilConjectures, and
project lean/Sheaf for externalComparison, external/triangle, Kunneth/triangle, and
projection/CommShift found no prior statement of this full external composite.
The general projection-shift and triangulated-functor APIs found are ingredients,
not duplicates. The worker report records LeanSearch, LeanFinder, Loogle and grep
searches. No new node or dependency repair is needed, and no source-based statement
correction or citer audit is triggered. Comparing the item to the read-only clone
shows only `lean` differs.

Edge cases and mechanical checks:

Zero L, zero Q, zero triangles, zero coefficient ring, identity f, empty schemes,
arbitrary characteristic, odd tensor degrees, arbitrary lower bounds for Q, and
empty model intervals a>b remain covered. The last permits only the zero complex,
as required; no a≤b premise was introduced. All binders are explicit with
`autoImplicit false`; no universe or variable is unbound. The recorded `lean.statement`
is byte-for-byte the theorem signature up to `:=`. All four helpers have real bodies;
the only local theorem has exactly `sorry`. All lines are at most 100 characters.
This is ordinary etale work; no pro-etale substitute is present.

Compiler reproduction:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q22
lem-trf-external-comparison-triangles
snapshot/lean/Sheaf/Paper/ExternalComparisonTriangles.lean` exited 0, checking
`sandbox Sheaf/Stage2/Sandbox0.lean` in 9.3 s and
`library Sheaf/Paper/ExternalComparisonTriangles.lean` in 10.3 s, with no reported
errors or warnings. The installed wrapper now reports server per-file compilation
with a private side overlay, rather than the earlier local implementation described
in the brief; it was used as prescribed, without direct ssh commands, live-file edits,
or a global build. This reproduces the worker's recorded successful per-file checks.

Finding and repair: H1/H11 report provenance only. The original heading contained an
explicit author self-check, not an independent second reading. The full replacement
report preserves the Worker report and installs this actual independent reading.
No Lean, node, hypothesis, conclusion, or canonical map required repair.
