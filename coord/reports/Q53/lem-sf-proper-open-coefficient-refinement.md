## Worker report

The delivery states `AlgebraicGeometry.Etale.properOpenComparison_coefficient_refinement`
in `Sheaf.Paper.ProperOpenCoefficientRefinement`. The item’s natural statement and all
DAG edges are unchanged. It uses ordinary constant-coefficient ModuleCat-valued sheaves
on the small etale site, including the existing unbounded scalar-extension functor and
coefficient mate. Six declarations implement the statement and its specified maps.
Definitions have explicit data. Both postponed theorems have source and proof docstrings
and belong to this node: the open tensor identification stipulated in the normalization,
and the final refinement equality. No proof is supplied in this stage.

The source was read in `literature/stacks-project/more-etale.tex`, at
`lemma-shriek-proper-and-open` (0F7B), `lemma-shriek-well-defined` (0F7I), and
`remark-Rf-lower-shriek-change-of-rings` (0GL6). The item explicitly supplies the
clopen-section proof beyond the source’s compact-support coefficient assertion.
No repair note is present for the item.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A and B finite commutative rings, unital map A to B | `{A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)`; RingHom preserves one. The coefficient universe is the established size convention for `Scheme.{u}`. |
| X, T1, T2 schemes | `{X T₁ T₂ : Scheme.{u}}`. |
| All three schemes admit finite affine Noetherian covers | `[IsNoetherian X] [IsNoetherian T₁] [IsNoetherian T₂]`. Mathlib’s `isNoetherian_iff_of_finite_affine_openCover` gives precisely the node’s convention. |
| Proper u | `(v : T₁ ⟶ T₂) [IsProper v]`. Mathlib proper includes universal closedness, hence quasi-compactness, so its locally-finite-type condition gives finite type as required. |
| Open j1 and j2 | `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]`. |
| u composed with j1 equals j2 | `(h : j₁ ≫ v = j₂)`. Lean composition is written in traversal order. |
| Ordinary small-etale module sheaves and their derived categories | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` and `DerivedCategoryModule A T`, the dependency’s established encoding. No pro-etale or condensed category occurs in the statement. |
| Q_T = derived extension of scalars | Existing `scalarExtension φ T`, an abbreviation for the published left adjoint to actual exact scalar restriction. `scalarTensorIso` in the imported recorded dependency characterizes it as derived tensor with B on K-flat representatives. |
| L, R, I | Exact `(upperStar (ModuleCat D) v).mapDerivedCategory`, `rightDerivedLowerStar (ModuleCat D) v`, `(openImmersionLowerShriek (ModuleCat D) j).mapDerivedCategory`. |
| Geometric and open adjunctions | Existing `derivedUpperStarLowerStarAdjunction`, transported through `leftDerivedUpperStarIsoMapDerivedCategory`, and `derivedOpenImmersionLowerShriekUpperStarAdjunction`. These derive the recorded ordinary adjunctions. |
| K in D+ | `(K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))`; `K.obj` is its ambient object. |
| Q_X K in D+ | `hQ : DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj K.obj)`. The B bounded-below object is explicitly `⟨(scalarExtension φ X).obj K.obj, hQ⟩`, with precisely that ambient object. |
| lambda is the canonical tensor/pullback iso | `properOpenCoefficientPullbackIso φ v` transports existing `scalarPullbackIso φ v` through the canonical exact-inverse-image isomorphisms. The imported comparison is uniquely fixed by ordinary scalar/pullback on K-flat representatives. It is not an arbitrary witness. |
| chi has the specified counit transpose | Reuses existing `(scalarMate φ v).app M`. Its definition is `mateEquiv` of the K-flat-normalized scalar/pullback isomorphism under the two geometric derived adjunctions. Consequently its B-transpose is lambda followed by Q of the A-counit, exactly as stipulated. The canonical exact-inverse-image transport changes only the presentation of that same adjunction. |
| beta inverse has the specified open-unit transpose | `properOpenCoefficientOpenInverse φ j M` is explicitly `(openAdjB.homEquiv _ _).symm (Q_W.map (openAdjA.unit.app M) ≫ lambda.inv.app (I_A.obj M))`. |
| beta is an isomorphism | `properOpenCoefficientOpenInverse_isIso` states invertibility of that exact map; `properOpenCoefficientOpenIso` is `(asIso inverseMap).symm`. Thus its inverse is precisely the constructed transpose, not a choice of an unconstrained isomorphism. Its proof docstring gives the node’s K-flat and extension/tensor argument, with no coefficient-flatness hypothesis. |
| alpha is exactly the recorded theta-normalized map, including the clopen section | `properOpenComparisonAmbient A v j₁ j₂ h K` takes `(properOpenComparison A v j₁ j₂ h K).hom`, followed only by the canonical `rightDerivedFunctorPlusCompatibility.hom.app`. The source open functor and the input to direct image are definitionally the unbounded exact open functor on `K.obj`. The dependency’s `properOpenIdentification` was read: it is the prescribed r, e, c composite using the clopen section. No new alpha is chosen. |
| Left side Q(alpha), then chi, then R(beta1) | The theorem’s first three factors are `(scalarExtension φ T₂).map (properOpenComparisonAmbient A … K)`, `(scalarMate φ v).app (I_j1,A.obj K.obj)`, and `(rightDerivedLowerStar (ModuleCat B) v).map (properOpenCoefficientOpenIso φ j₁ K.obj).hom`. |
| Right side beta2, then alpha over B at QK | `(properOpenCoefficientOpenIso φ j₂ K.obj).hom ≫ properOpenComparisonAmbient B … ⟨Q_X.obj K.obj, hQ⟩`. |
| Equality in D(T2_et,B), with the stated source and target | Both composite terms elaborate as morphisms from `Q_T2(I_j2,A(K.obj))` to `R_u,B(I_j1,B(Q_X(K.obj)))` in `DerivedCategoryModule B T₂`. |
| Original square not assumed cartesian | There is no `IsPullback`, chosen-cartesian-square, or equivalent binder. |
| No arbitrary-input isomorphism for chi; no Tor or constructibility condition | chi is used only as a morphism; the signature contains none of these conditions, and does not require Q of any direct image to be bounded below. |

Dependency declarations read and used (namespace `AlgebraicGeometry.Etale` unless specified):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian` and its finite-affine-cover characterization.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: the recorded
  `DerivedCategoryModule`, Mathlib `DerivedCategory.Plus`, and `TStructure.t.plus`.
  The derived-category record explicitly lists these notions; torsionCohomology is not
  needed by this item. Current server source of the recorded module was read using `scompile.py --source`.
- `Sheaf.Paper.EtaleDerivedScalarTensor`: `scalarExtension`, its existing
  scalar/tensor representative normalization and `scalarTensorIso_existsUnique`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`; `…Derived.UpperLowerStarCoherence`:
  `rightDerivedLowerStar` and `rightDerivedLowerStarPlus`; `…Derived.UpperLowerStar`:
  `leftDerivedUpperStarIsoMapDerivedCategory` and `derivedUpperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek` and `openImmersionLowerShriekUpperStarAdjunction`;
  `…Derived.OpenImmersionLowerShriek`: the unbounded and bounded-below derived open adjunctions.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, whose current full signature and
  docstring were read through `scompile.py --source`; it supplies the exact ordinary
  constant-ring inverse-image interpretation used by the derived functors.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `derivedEtaleLowerShriekUpperStarAdjunction`; for opens we use the already available
  open specialization, avoiding a second definition. The ambient-right-adjoint
  comparison part of that dependency is not needed in this equality.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its representative-characterized canonical tensor comparison is imported unchanged.
  The needed constant-coefficient specialization is already published as
  `scalarPullbackIso` in `Sheaf.Paper.PurEtaleScalarMateProjection`, which also supplies
  `scalarMate`. Their full definitions and normalization theorem were read in current server source.
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`: `properOpenComparison`,
  `properOpenIdentification`, `properOpenSection`, `properOpenSectionGeometry`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  `CategoryTheory.Functor.rightDerivedFunctorPlusCompatibility`; exact open
  compatibility is the existing `mapDerivedCategoryPlusCompatibility` (definitionally reflexive).

Every recorded proof-dependency module is imported, with ordinary imports for the
proof-only tools. This retains the clopen equivalence, localization, proper/open
interchange and sheaf-support normalization, K-flat resolution, tensor descent,
ringed pullback and extension/tensor identity needed by the eight proof steps.
The mathematical content of all eight steps is in the main theorem’s docstring.

Edge cases checked before writing: zero K; empty X; identity proper refinement;
noncartesian refinement with an additional proper component over the open; zero
coefficient ring; identity coefficient map; nonflat finite quotient A to B.
The first two allow zero source/target naturally. Additional components are retained
in the clopen product proof, rather than excluded by a Cartesian assumption.
The zero ring needs no Nontrivial instance. Nonflat quotients can fail to preserve
bounded below objects, so the explicit hQ is essential; no bound on scalar extension
of direct image was introduced. No rank, residue-characteristic, connectedness,
nonemptiness, or universe-equality restriction was added.

Searches for an existing statement or duplicate maps:

- `msearch.py leanfinder`: “Derived scalar extension commutes with the normalized proper
  open refinement map from extension by zero to proper derived direct image” — eight
  hits, including ordinary `ModuleCat.extendScalarsComp`, scalar associativity, and
  normalization/localization lemmas; none states the specified etale derived square.
- `msearch.py loogle`: `CategoryTheory.mateEquiv` — twelve hits for mates and composition
  formulas; useful general machinery, no instance of this coefficient refinement equality.
- `msearch.py grep`: `properOpen|extensionByZero|lowerShriek` in Mathlib AlgebraicGeometry
  — zero hits.
- `rg` of the upstream project and `lean/Sheaf` for proper/open coefficient, scalar/open,
  scalar-extension, tensor, and refinement terms found `scalarExtension`, the uniquely
  normalized `scalarPullbackIso`, `scalarMate`, the recorded `properOpenComparison`, and
  completed/pro-etale or stricter coefficient comparisons. The exact existing scalar
  constructions were reused; no existing ordinary-etale refinement equality or open
  scalar-extension isomorphism with these endpoints was found.
- `grep -rn` for this item id in the upstream `WeilConjectures` tree — no occurrence.
- Exact searches for all new declaration names in `dag/lean_names_upstream.json`,
  Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` — no collisions.

No statement dispute or correction, new node, or dependency-record repair is needed.
The named auxiliary declarations are canonical maps and the explicitly stipulated
open tensor identification belonging to the owning node, as authorized by the
human’s helper-interface instruction. They introduce no independent mathematical notion.

Validation: `scompile.py Q53 lem-sf-proper-open-coefficient-refinement` compiles the
sandbox and the library-shaped module cleanly under the default 60-second limit
(about four seconds per invocation). `autoImplicit` is false; every variable and
universe is bound. All Lean lines are at most 100 characters. Only named theorems
contain `sorry`, as their entire proof bodies. No shared or upstream file was modified.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
