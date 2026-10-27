## Worker report

The modules `Sheaf.Paper.GeometricComparisonData` and
`Sheaf.Paper.GeometricOperations` define
`WeilConjectures.GeometricOperations`. They contain definitions and structure fields only;
no theorem is proved or postponed, and no `sorry` is added. The item statement is unchanged. Its dependency list adds the comparison-data
helper node described below. The package is parameterized by the coefficient
setup and the given exceptional adjunctions; it does not assert their existence.

Read the current blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/sk-d-six/_section.md`
and the complete reviewed DAG statement. The latter already spells out the coefficient
subcategory domains, identity composites and canonical arrows implicit in the blueprint.
The old upstream GeometricOperations name is absent from the current library; the
upstream externalProduct alone is not this package.

Clause-by-clause rendering:

- The finite-field datum is `F : FiniteFieldDatum`, with `l`, `[Fact l.Prime]`,
  `hl : l ≠ F.p`, finite extension `E` and `[FiniteDimensional (Padic l) E]`.
  The coefficient exponent is `n + 1` for `n : ℕ`, covering exactly all positive
  exponents without an extra hypothesis. The ring is the existing
  `Padic.coefficientExtensionRing l E (n + 1)`.
- Geometric schemes are `TraceFormulaGeometricSpace F`, the separated full part of
  the dependency's `SixFunctorSpace F`. Its objects are precisely separated
  finite-type schemes over `Spec F.k`; morphisms retain their actual over maps.
  `structureMap`, `point`, and `compactification` use those actual maps and the
  compactifications selected in `G : TraceFormulaCoefficientSetup ...`.
  The separatedness/finite-type/quasi-compactness instances for morphisms are
  cancellation of the known structure-map properties, not extra assumptions.
- `Ambient`, `domain`, and `Ctf` reuse the actual `proEtaleDerivedCategory`,
  `finiteTorConstructible`, and its full subcategory. Triangulatedness,
  repleteness, chosen compactifications and pullback/support preservation remain
  exactly the requirements of `G`. There is no new constructibility predicate.
- `pull`, `support`, `directCtf`, `exceptionalCtf`, `tensorCtf`, and `closed` use the
  recorded derived operations, not arbitrary supplied functors. `pullCtf` and
  `supportCtf` restrict using G's preservation fields; `directCtf`, `tensorCtf`,
  and `exceptionalCtf` restrict using thm-sf-ctf-stability. `pullDirectAdjunction`
  is the restriction of the canonical derived module adjunction.
  `ExceptionalAdjunctions` is an INPUT on Ctf for these actual support and
  exceptional functors. There is no unbounded pro-etale exceptional adjunction.
- `Comparisons.omega` is an object of Ctf for every geometric X.
  `dualizing` identifies it with the given exceptional image of the coefficient
  unit along the structure morphism; `normalization` is the base identification;
  `dualizingComp` gives the displayed f! comparison. Every geometric structure
  morphism is compactifiable, by Nagata over the field, so this is exactly the
  conditional source domain in this fixed setting. `unitDomain` records the
  membership required to regard the constant coefficient as an object of Ctf;
  it is a proof field, not a different coefficient object.
- `proper`, `composition`, and `identity` are the support/direct, support
  composition, and support identity natural isomorphisms. The compositor is
  oriented R(gf)! → Rg! Rf!, the inverse orientation of the displayed source
  isomorphism, retaining all its data.
- `Square.cartesian` uses the recorded `ChosenCartesianSquare` with its specified
  pullback isomorphism and projection equations. `baseChange` is a natural
  isomorphism on the full coefficient categories, oriented g*Rf! → Rf'!g'*.
- `projection` has exactly K in Ctf(X), L in Ctf(Y); the two
  `projection_natural_*` equations render naturality in both variables.
- `monoidal` is Mathlib `Functor.CoreMonoidal` on the ACTUAL AMBIENT pullback,
  so it contains the unit and tensor isomorphisms, their naturality, associativity
  and both unit laws. `symmetric`, `koszul`, and `braided` retain the signed
  ambient braiding and require its preservation. The existing
  `RingedDerivedTensorSymmetryModel` fixes the braiding on ALL K-flat
  representatives by (-1)^(pq), including the -1 swap on A[1] with itself.
  This is the representative description of the given derived symmetry;
  it does not choose an alternative symmetry or a new tensor product.
- `Comparisons.Coherence.leftUnit` and `rightUnit` are the support unit axioms.
  `properIdentity` is support identity followed by inverse canonical direct
  identity; `baseNormalization` is dualizing identification followed by the
  exceptional adjoint identity, as an equality of morphisms. `dualizingIdentity`
  uses the same adjoint identity. `monoidalIdentity` makes the pullback-unit
  composite with the canonical identity pullback equal the identity.
  `properComposition` uses `directComp`, the right-adjoint mate of `pullComp`;
  `dualizingComposition` uses `exceptionalComp`, the right-adjoint mate of the
  specified support compositor. `baseChangeVertical` is precisely the component
  equation for vertically pasted Cartesian squares, including both support
  compositors. The third chosen Cartesian identification remains explicit;
  the equation holds for every choice, as the statement requires.
- `dual` is the existing internal Hom into omega, `compactlySupported` is the
  support functor of the structure morphism, and `external` is the actual
  pullback tensor product on any specified fibre-product presentation. Evaluation
  is `closed.evaluation`, namely the tensor/internal-Hom counit. `biduality`
  is `closed.transpose` of braiding followed by that evaluation. The final
  package field `biduality` imposes `IsIso` on this VERY morphism for every Ctf K.
- `productSquare` is the product's Cartesian square. `trace` composes inverse
  base change, the support image of `dualizing Y`, the GIVEN exceptional
  counit at the coefficient unit, and inverse pullback monoidal unit.
  `alpha` takes the exceptional adjunct of support of the braiding, inverse
  projection, trace tensor identity, and left unitor. Its input is the actual
  `tensorCtf` of the two restricted pullbacks, so membership needed for the Ctf
  adjunction is supplied without a hypothesis or ambient adjunction.
  `kunnethVerdier` transposes the associator, pullback tensorator, pulled-back
  evaluation, and alpha. Its final package field requires `IsIso` for every
  M,N in the specified Ctf domains. Since the fixed base is Spec F.k, and the
  geometric schemes are already quasi-compact and compactifiable, no field-base
  or quasi-compact case is omitted. Every fibre-product presentation is allowed.

Dependency declarations read and used:

- `Sheaf.Paper.TraceFormulaCoefficientSetup`,
  `WeilConjectures.TraceFormulaCoefficientSetup`: full source and signature read.
- `Sheaf.Paper.SixFunctorOperationDatum`,
  `WeilConjectures.SixFunctorOperationDatum`, with its publicly imported stages;
  `SixFunctorSpace`, `sixFunctorPoint`, `sixFunctorStructure` reuse its geometric
  objects, and the actual finite tensor/Hom/pullback/support/exceptional operations
  imported by the recorded datum are used. The unrelated higher coefficient stages
  of that datum are not demanded as inputs by this finite-level package.
- `WeilConjectures.Compactification.Defs`,
  `AlgebraicGeometry.HasCompactification`: actual nonempty compactifications.
  `HasCompactification.of_over` supplies it for geometric maps; G fixes the choice.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`,
  and its `IsSeparated`, `UniversallyClosed` prerequisites: full definitions read.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`: full signature and fields read.
- `Mathlib.CategoryTheory.Monoidal.Functor`,
  `CategoryTheory.Functor.CoreMonoidal`: fields and full signature read.
- `Sheaf.Paper.FiniteTorStability`, `WeilConjectures.finiteTor_stability`,
  `sfStabilityFiniteExceptional`, with the preservation statements used to define
  the literal restrictions. Source docstrings, including (i)--(iv), (v) and the
  constructible exceptional adjunction, were read.

Canonical-map helpers are declarations belonging to this package, listed in
`lean.declarations`, and each has its own source/blueprint docstring. The signed
symmetry normalization reuses the existing ringed-derived tensor predicate rather
than defining another symmetry convention. The five-part comparison data have a helper definition node below; there are
no dependency repairs or source corrections.

Edge cases checked: empty schemes are included by the three geometric properties;
no nonemptiness or positive dimension is imposed. The zero complex and zero
morphisms are allowed in every quantified coefficient object, and their evaluation
and adjuncts are the same canonical constructions. Identity maps use the actual
adjoint identities, so no ill-typed literal identification is demanded. At X=Y=s
and the identity product projections, trace and alpha reduce to the ordinary
adjunction/unit/evaluation composite. Coefficient characteristic two is included:
-1=1 there and the signed representative normalization still applies. There is no
universe equality on the small pro-etale site: its object/morphism sizes u+1/u are
retained in `RingedDerivedTensorSymmetryModel.{u+1,u,u}` and the ambient definitions.

Searches actually run:

- msearch leanfinder, query “geometric operation package pro-etale six functors
  dualizing complex biduality Kunneth Verdier”: 8 hits, including scheme module
  adjunctions and a light condensed monoidal localization, none the package.
- msearch loogle, query `GeometricOperations, CoreMonoidal`: 0 hits, unknown
  identifier GeometricOperations. The separately read Mathlib CoreMonoidal is the
  exact strong monoidal notion required for one field.
- msearch grep, query `GeometricOperations|kunnethVerdierMap|dualizingComp` in
  CategoryTheory: 0 hits.
- rg across WeilConjectures and Sheaf for `GeometricOperations|sk-d-six`, and
  for `kunnethVerdierMapOf|properComparison_id|dualizingBase_eq|dualizingComp_id`:
  only externalProduct's source tag occurs in current Lean; no package.
- rg in dag/lean_names_upstream.json for GeometricOperations and
  kunnethVerdierMapOf: no matches.
- Read upstream `FiniteCoefficient/Derived/ExternalProduct.lean` and `Duality.lean`;
  externalProduct gives just one construction and not the operation package.
  The current TraceFormula.Basic concerns condensed rational coefficients,
  not this finite-coefficient package.

Validation uses scompile.py only, followed by the required delivery dry run.

## New nodes

`def-trf-geometric-comparison-data` records precisely the five data bullets of
`sk-d-six`, before the coherence and invertibility requirements. Its module is
`Sheaf.Paper.GeometricComparisonData`; the owning item imports it and constructs
the canonical maps and the complete package from it. This separation permits
individual-file compilation under the prescribed limit. The source is the current
blueprint unit, its five data bullets. No mathematical condition was weakened.
The full clause matching for these data and their exact dependency restrictions
is in the Worker report above. Helpers `tensorObj` and `unitObj` name the tensor
and unit of the existing closed structure with explicit arguments.

Searches for this helper: LeanSearch, query “Comparison data for geometric six
operations: dualizing complexes proper comparison shriek base change projection
formula and braided strong monoidal pullback”, returned eight unrelated Over,
scheme-module and linear duality declarations; Loogle
`GeometricOperationPackage.Comparisons` returned zero, unknown identifier; Mathlib
grep `GeometricOperationPackage|GeometricComparisonData` in CategoryTheory returned
zero. Repository/DAG grep and blueprint_refs.py search “comparison data” found
only constant-module, coefficient, projection and purity comparison nodes, none
the five-part data here. The new node retains all existing dependencies of the item.

The separately compiled comparison-data and operation-package modules elaborate
all definitions and coherence fields. An initial combined module exceeded the
per-file limit; separating the comparison data and using explicit monoidal
arguments resolved that problem without changing any quantified map or condition.
The final delivery dry run checks both files again and runs server preflight.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
