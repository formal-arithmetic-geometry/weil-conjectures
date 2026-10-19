## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SupportedGeneratorsCostalkDetection.lean`
states `AlgebraicGeometry.Etale.supported_bounds_iff_geometricCostalk` and
`AlgebraicGeometry.Etale.supportedGenerator_hom_naturally_iso`. Both proofs are `sorry`.
It supplies three actual composite constructions belonging to this node:
`geometricCostalk`, `etaleSupportedCohomology`, and `etaleSupportedGenerator`.
Their data contain no `sorry`. No statement correction or new definition node is needed.

Hypothesis and clause correspondence:

- The Noetherian scheme X is `(X : Scheme.{u}) [IsNoetherian X]`.
- The finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the project's ordinary small-etale `Sheaf ... (ModuleCat.{u+1} Λ)` encoding.
  Every finite ring is represented in this universe; no cardinal or characteristic is excluded.
- The specialization-stable subset is `(S : Set X)` and
  `hS : ∀ (x y : X), x ⤳ y → x ∈ S → y ∈ S`.
  The direction is from the general point x to its specialization y.
- The integer bound is `(a : ℤ)`, with `m : ℤ` and `m ≤ a` in both tests.
- K belongs to `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat Λ))`.
  This is the full bounded-below subcategory of the ordinary derived category, without
  constructibility, excellence, finite dimension, or a pro-etale replacement.
- Every geometric point is quantified as `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`
  and `x : Spec (.of Ω) ⟶ X`. Its underlying point is `x (IsLocalRing.closedPoint Ω)`.
  Thus the test ranges over every geometric point above every point of S, not one choice.
- `geometricCostalk Λ x` first applies the exact inverse image along the canonical
  `Scheme.strictHenselizationStructuralMap x` on D+, and then applies
  `derivedSupportedEtaleSections` on `Scheme.strictHenselizationScheme x` with open
  complement `{IsLocalRing.closedPoint (Scheme.strictHenselizationRing x)}ᶜ`.
  The scheme is the spectrum of precisely the recorded small affine-neighbourhood
  ring colimit. Its local-ring proof is selected from the existing
  `AlgebraicGeometry.strictHenselizationLocalStructure x`; only a proof of a proposition
  is selected. Openness of the complement is Mathlib's
  `IsLocalRing.isClosed_singleton_closedPoint`. No additional theorem or axiom is supplied.
- Condition (1) is the left side of the iff: membership of that underlying point in S,
  followed by `IsZero` of degree-m homology of the defined costalk for every m ≤ a.
- Condition (2) is the right side: arbitrary V and `v : V ⟶ X` with `[Etale v]`
  and `[IsAffine V]`, arbitrary Z and `i : Z ⟶ V` with `[IsClosedImmersion i]`
  and `[IsReduced Z]`, and `Set.range (i ≫ v) ⊆ S`.
  Here “affine etale object” means its source V is affine, as in the node's proof;
  no extra `[IsAffineHom v]` restriction is imposed.
- `etaleSupportedCohomology Λ v i m` is exact inverse image along v on D+,
  followed by the recorded right derived kernel of restriction to `i.openComplement`,
  followed by `DerivedCategory.homologyFunctor (ModuleCat Λ) m`.
  `IsZero` is vanishing as a module, hence as the cohomology group in the node.
- The final assertion is `supportedGenerator_hom_naturally_iso`:
  `etaleSupportedGenerator Λ v hv i m` is the degree-zero sheaf
  `v_! i_* Λ_Z`, shifted by `-m` in the full ordinary derived category.
  The constant rank-one sheaf is
  `(constantSheaf Z.smallEtaleTopology (ModuleCat Λ)).obj (ModuleCat.of Λ Λ)`;
  `lowerStar` is i_* and `etaleLowerShriek` is the actual sheafified sum over lifts v_!.
  `DerivedCategory.Plus.ι ⋙ preadditiveCoyoneda.obj (op generator)` is the functor
  K ↦ Hom_D(generator,K), with its additive group structure and postcomposition maps.
  Its natural isomorphism with `etaleSupportedCohomology ... ⋙ forget₂ _ AddCommGrpCat`
  gives exactly the asserted group isomorphism, natural in K. `Nonempty` asserts a
  natural isomorphism exists, not merely pointwise group bijections. No arbitrary
  chosen morphism or noncanonical replacement functor is a hypothesis.
- Both assertions omit excellence and constructibility, exactly as required.

The existing strict-henselization source in this machine's newer shared checkout is
not always the compiled interface. Reading the actual live sources with
`scompile.py --source WeilConjectures.AlgebraicGeometry.StrictHenselization` and
`--source WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`
confirmed that the recorded `strictHenselizationRing` is a separate affine-diagram
colimit, `strictHenselizationScheme` is its spectrum, and the recorded structural map
has exactly that source. An initial compile using the other upstream
`strictLocalization` exposed this mismatch. The final construction uses the recorded
scheme and structural map together, so no transport or equality is assumed.
The already recorded local-structure interface supplies its IsLocalRing proof.

Dependencies read and used (module, declarations):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the scheme condition is
  Mathlib `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: the recorded ordinary
  derived module-sheaf category; Mathlib `DerivedCategory.Plus`, `homologyFunctor`,
  `singleFunctor`, and the full inclusion `DerivedCategory.Plus.ι`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: reexports
  `Scheme.strictHenselizationRing`, `strictHenselizationScheme`, and their limit properties.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`: `supportedEtaleSections`,
  its kernel construction and `derivedSupportedEtaleSections`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion` and
  `Scheme.Hom.openComplement`.
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`:
  `Scheme.etaleModuleSheaves_grothendieckAbelian`, imported as the recorded dependency.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points use
  the recorded inline scheme morphism encoding (`Scheme.SpecToEquivOfField`).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, the existing adjunction; `Derived.UpperLowerStar` supplies the
  exact-functor operations on the bounded-below categories.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `Etale.etaleLowerShriek`, its sheafified Kan-extension formula, adjunction, exactness.
- `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`:
  `AlgebraicGeometry.strictHenselizationLocalStructure`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap` and its universal characterization.

The last three interfaces already have genuine DAG nodes; those ids were added to
stmt_deps, as permitted for landed notions. No dependency node was rewritten.
All recorded statement modules are public imports; already stated proof-dependency
modules are imported without public. The docstrings carry the first thirteen
proof steps for the equivalence, and the final injective/Hom calculation for the
natural isomorphism. The source check used the local ILO PDF and the full support
section of `literature/stacks-project/etale-cohomology.tex`, especially the kernel,
derived functor and supported-kernel adjunction in Tags 09XP and 09XQ.
The DAG describes the equivalence proof as an agent-formulated input, rather than
claiming it is a verbatim theorem of ILO XVII; the docstring follows that proof.

Edge cases checked before the final statement:

- Empty S: both bounds are vacuous except empty closed supports, whose kernel is zero.
- Empty X, V or Z are allowed; there is no Nonempty scheme hypothesis.
- S = X and identity etale/closed maps are included.
- Zero K and the zero coefficient ring are allowed; no Nontrivial coefficient assumption.
- All positive, zero and negative a and m are retained. Shifting by -m gives the
  intended degree m Hom calculation, not its opposite sign.
- Geometric points need not be closed in X; the support is the closed point of the
  strict localization, not the original singleton in X.
- No finite-dimensional, excellent, torsion-invertibility or constructibility assumption
  was added. The only boundedness is exactly D+ as in the item.
- Site objects, geometric fields and schemes use u; coefficient modules use u+1,
  matching the recorded ordinary small-etale interfaces without identifying site
  object and morphism universes or introducing a vacuous independent test universe.

Searches (retained `searches.jsonl` records the actual msearch results):

- LeanSearch: “Vanishing of supported etale cohomology on affine etale schemes is
  detected by geometric costalks of bounded below complexes”: eight results on
  strictly bounded complexes, affine section descent and the small etale site;
  none states this equivalence or defines this geometric costalk.
- LeanFinder: same query: eight results, chiefly affine-limit sections,
  `DerivedCategory.isGE_iff` and `isGE_Q_obj_iff`; none is this statement.
- Loogle: `"costalk"`: zero results.
- msearch grep: `costalk|supportedEtaleSections`: zero Mathlib hits.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id:
  no existing declaration. Concept search there and in `lean/Sheaf` found the
  supported-section construction and specialized costalk comparisons, but no
  identical equivalence, generator Hom statement, or duplicate geometric-costalk functor.
- Direct source searches found `Etale.etaleLowerShriek` in upstream `EtaleMap.lean`;
  it is used unchanged, rather than defining a second extension by zero.

## Second reading by Q22

This section records the dispatched worker's final cross-check, not a claim that a
second agent reviewed it. The dispatch explicitly prohibits starting other agents;
the maintainer's independent delivery review remains the independent reading.
I reread the node statement and final module clause by clause. The two concrete
interface defects found during compilation were mixing two strict-localization
models and relying on an unsynthesized local-ring instance; the final module uses
`strictHenselizationScheme`, its recorded structural map, and the existing
local-structure theorem consistently. The source shift is `-m`, the subset direction
is specialization closed, reduced support and affine-source hypotheses are retained,
and all geometric points and all integer degrees below the bound are quantified.
The Hom assertion is a natural isomorphism of additive-group functors, so additivity
and naturality are stated, not left as prose. The three definitions are actual
compositions; the only postponed declarations are the two named theorems matching
the two assertions of this one DAG node. No statement dispute was found.
