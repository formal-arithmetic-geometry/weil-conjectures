## Worker report

The module `Sheaf.Paper.IsomorphismScalarAugmentationCone` states
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.isomorphism_scalar_augmentation_cone`
with proof `sorry`. It compares actual chain maps, before localization, and includes
both the zero shifted coordinate and the common positive-level unshifted coordinates.
No statement correction, new node, or mathematical dispute is proposed.

Hypothesis and clause matching:

- The prime is `l : ℕ` with `[Fact l.Prime]`. The fields E and L carry
  `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]`; the inclusion is
  `ι : E →ₐ[ℚ_[l]] L`. A field algebra homomorphism is injective. Their valuation
  rings, chosen uniformizers and positive quotients are the recorded Padic constructions,
  not additional supplied objects.
- The schemes are `X Y : Scheme.{u}`; `g : X ⟶ Y` with `[IsIso g]` is the
  isomorphism. `hX` and `hY` assert invertibility of l in every residue field,
  equivalently invertibility on the schemes. The small site remains `Scheme.ProEt`,
  with object universe u+1 and morphism universe u. The main statement uses the
  recorded common-u constructibility convention; the two helper definitions in this module
  retain independent site and coefficient universes t,u.
- `integralTowerModules l E W` means modules over the actual completed coefficient
  sheaf R_W; replacing E by L gives S_W. `inverseImageIntegralModules` uses the
  recorded sectionwise inverse image and transports action by the inverse of
  `inverseImageCompletedCoefficientMap`, whose components are exactly the required
  finite structure maps followed by inverse images of quotient projections.
- `K` and `_hK : sfIntegralConstructible l E Y K` express membership in the exact
  recorded D^b_c: derived completeness, constructible reductions and a single uniform
  finite cohomological interval. These assumptions are retained although the strict
  coordinate calculation itself does not use them.
- `P : (integralOperationsGoodComplex l E Y).FullSubcategory` means precisely
  K-flat with every term flat. `_e : DerivedCategory.Q.obj P.obj ≅ K` specifies the
  represented derived object. This is the derived-category rendering of choosing
  a flat-term K-flat resolution of K; no particular representative of K is required.
- `completedOrdinaryScalarComplex` forms Q=P tensor S_Y and Z=G_E(P) tensor S_X
  using the universal sheafified ordinary tensor. `leftComplex` and `rightComplex`
  are the predecessor's exact functors. The binder `b` and `_hb : CompletedFormula
  l E L ι g b` specify its natural tensor isomorphism by the predecessor's full local
  formula. No arbitrary isomorphism is assumed: that formula fixes its values on
  all local tensor generators. The predecessor asserts existence of such a b.
- `integralOperationsPullbackLevel` is D^F_m, including restriction along the completed
  projection. `integralOperationsPullbackTowerFunctor` has the actual quotient
  transitions, and `integralOperationsPullbackComplexFunctor` is its fixed Roos cone.
  Every n in Lean means m=n+1, hence m=1 and every positive level are included.
- `inverseImageRoosComparisonComplex` is exactly a^E_P or a^L_Q, with product of
  `inverseImageReductionTheta` and zero degree-minus-one cochain in mappingCocone.lift.
- `specifiedPullbackConeChain` is delta_P in this same ordinary tensor presentation:
  the strict data's `generator` field fixes d_m with both finite scalars, its
  `coordinates` field fixes tensor/product on both cone coordinates, and its cone
  map is this tensor/product isomorphism followed by the strict Roos map of d.
- The first conjunct is tensor(a^E_P) followed by delta_P equals b_P followed by a^L_Q.
  Lean's `≫` is composition in source-to-target order, so it is exactly the displayed
  square, with its full chain-map codomain.
- The second conjunct sets the shifted coordinate of the right composite to zero in
  every degree. The first conjunct also gives that assertion for the left composite.
  `mappingCocone.snd ... .v i (i-1)` is precisely the shifted-product coordinate.
- The last clause evaluates the right composite on the local pure tensor with
  y=g^-1(p) and s=c_L(g^-1(s0)), projects using `mappingCocone.fst` and the nth product
  projection, and gives `s • theta^L_n(1 tensor p)`. Since D^L_n is restricted along
  pi^L_X,n, this scalar action is exactly multiplication by pi^L_X,n(s), as in the
  node. Theta sends this argument to g^-1((p tensor 1) tensor 1) tensor 1; the same
  coefficient-unit and associativity identifications of the recorded scalar model
  turn this into the displayed g^-1(p tensor 1) tensor pi^L_X,n(s). There is no
  arbitrary choice of an identification Q tensor B_L with P tensor B_L.

The docstring carries all five steps of the node proof: local pure-tensor generation;
zero shifted components; substitution a=b=1 in the left level map; the right tensor
balancing and coefficient projection identity; product and degreewise extensionality.

Recorded dependencies used (imports may be transitive public reexports):

| Node | Module and declarations |
| --- | --- |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, Padic coefficient integers, uniformizer, quotient rings, `Padic.finite_coefficientExtensionRing` |
| def-weil-scheme-morphism-properties | convention node; `Scheme`, `IsIso`, residue fields and `IsUnit` |
| def-weil-pbc-proetale-site | `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`, `ProEt.topology` |
| def-weil-completed-integral-coefficients | `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, completed integral rings and their actual projections |
| def-weil-inverse-image-pullback-comparison | `Sheaf.Paper.InverseImagePullbackComparisonDerived`, publicly retaining `inverseImageCompletedCoefficientMap`, `inverseImageIntegralModules`, `inverseImageReductionTheta`, `inverseImageRoosComparisonComplex` |
| def-pur-sheaf-tensor-product | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `SheafOfModules.cochainModulesMonoidal` |
| def-pc-tensor-complex-sheaves | `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`; scalar extension along a degree-zero ring is termwise |
| def-weil-derived-complete-integral-detailed | `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible` |
| def-pc-kflat-complex | `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`, the first clause of `integralOperationsGoodComplex` |
| lem-pc-kflat-resolution | `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` (representative existence) |
| lem-weil-isomorphism-scalar-tensor-kflat-model | `Sheaf.Paper.IsomorphismScalarTensorKFlatModel`, `leftComplex`, `rightComplex`, `CompletedFormula`, `isomorphism_scalar_tensor_kflat_model` |
| def-pur-integral-derived-operations | `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, publicly retaining the actual global pullback levels, tower, good complexes and Roos model |
| lem-weil-specified-pullback-comparison-alpha | `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`, `WeilConjectures.specifiedPullbackComparisonAlpha`; its landed record is unchanged |
| def-weil-abstract-derived-category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `DerivedCategory.Q`; the equality itself uses only the category of cochain complexes |
| lem-weil-proetale-isomorphism-inverse-image (proof) | `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`, sectionwise site equivalence and its exact module inverse image, publicly imported through the comparison module |

Edge cases checked against the constructions: g=id; E=L and the identity inclusion;
ramified extensions (no identification of E's and L's uniformizers or quotient towers);
the first positive quotient (n=0); zero complex and empty scheme; unbounded flat-term
representatives (products and the whole cone remain untruncated). Equality is strict,
not equality only in the derived category or on cohomology.

Searches performed on 2026-10-21:

- msearch leanfinder: "A zero shifted-coordinate quotient augmentation commutes with
  finite coefficient extension as a map into the entire Roos completion cone".
  Eight hits: generic mapping-cone functoriality and augmentation/truncation;
  none is this coefficient-change square.
- msearch loogle: `CochainComplex.mappingCone.ext_to_iff`. Exact generic cone
  extensionality found; it supplies no coefficient or augmentation comparison.
- msearch grep: `augmentation.*scalar|scalar.*augmentation|mappingCocone.*lift`,
  Mathlib/Algebra/Homology. Three factorization/mapping-cocone hits, none matching.
- msearch leansearch: "Equality of coefficient extension and inverse image quotient
  augmentations as chain maps into the mapping cone of one minus shift". Eight
  generic mapping-cone lift, homotopy and extensionality results, no exact statement.
- rg over both `lean/WeilConjectures` and `lean/Sheaf` for
  `scalar.*augmentation|augmentation.*scalar|lem-weil-isomorphism-scalar-augmentation-cone`.
  Other scalar augmentations, tensor resolution and completion statements found;
  none states the isomorphism inverse-image augmentation square.
- Read the source of `SpecifiedPullbackComparisonAlpha`, `ScalarPullbackStrictConeNaturality`,
  `IsomorphismScalarTensorKFlatModel` and the inverse-image construction in full.
  The strict-data interface already specifies the item helpers' notion;
  it is reused, not redefined. No new DAG node is needed.

Source checked: current blueprint's global-geometric-Frobenius unit and PDF pp. 50–51,
Bhatt–Scholze 6.5.9. The PDF supplies completed-pullback context only; the strict
identity and its proof are correctly marked as the node's agent calculation.

## Repair of H13

The return of immutable head `8d92b975fba3` identified a dependency-record narrowing:
the saved packet replaced the landed alpha theorem's record with a data definition.
The initial saved-packet dry run passed at `2c96ac64480`, but that mechanical pass
does not resolve the return's mathematical/interface requirement.

Removed the sandbox alpha-node copy and `SpecifiedPullbackConeModel.lean`.
The delivery makes no change to the live alpha node, module, declaration, signature,
or declarations list; in particular its citer
`lem-pod-isomorphism-scalar-comparison-agreement` retains the landed interface.
Moved `specifiedPullbackConeData` and `specifiedPullbackConeChain` into
`Sheaf.Paper.IsomorphismScalarAugmentationCone`, in namespace `WeilConjectures`.
Both carry this item's source/blueprint docstrings and are listed in the item's
`lean.declarations`. They select the existing uniquely normalized data from
`scalarPullbackStrictConeNaturality`: its Nonempty witness supplies data, and its
Subsingleton conjunct guarantees uniqueness. The chain definition uses the existing
`scalarPullbackConeMap` with that witness's level and cone fields. No new proof,
new notion, or modified dependency record is supplied. The item's `stmt_deps` and
the accepted theorem statement are unchanged.

Validation: the repaired module compiled cleanly through `scompile.py` against the
live server, both in its sandbox check (6.8 s) and library-module check (5.5 s).
No errors or warnings. A direct JSON comparison with live confirms that only the
item's `lean` field differs; its signature equals the recorded signature verbatim.
All Lean lines satisfy the 100-character limit. The prescribed final dry run and
delivery are run on this repaired single-module packet.

## Second reading by Q23

Author's explicit self-check; the dispatcher prohibits spawning an independent reader,
and the maintainer performs the independent mathematical review. Reopened the node and
the repaired item module. Checked every binder and all three conclusion parts against the
mapping above: no hypotheses or conclusion clauses dropped. In particular the product
projection is applied after the unshifted cone projection, and the shifted projection
is asserted zero as a module morphism, not just on tensor generators. The normalization
assumption on b is the exact predecessor's `CompletedFormula`; the selected delta's
normalization is carried by the existing strict-data fields. The restriction-of-scalars
action in the coordinate formula incorporates the actual L quotient projection. The
old alpha theorem remains publicly available through its original import and its node
record is untouched. The item's only node change is its `lean` record; its declaration
list now includes the two helpers. The theorem signature and five-step proof docstring
are unchanged. The helper docstrings now refer to this item. No dependency file is
included in the repaired packet.
