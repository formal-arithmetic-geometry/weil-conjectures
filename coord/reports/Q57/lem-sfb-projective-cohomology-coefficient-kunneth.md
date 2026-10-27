## Worker report

Item: lem-sfb-projective-cohomology-coefficient-kunneth. Module:
`Sheaf.AlgebraicGeometry.ProjectiveCohomologyCoefficientKunneth`.
All declarations are in `AlgebraicGeometry.AlgebraicSpace.ProjectiveKunneth`.
This is stage 2: every theorem proof is `sorry`; definitions have actual data.
The unchanged mathematical statement is rendered by the main theorem together with
its recorded construction and compatibility declarations, not just the main theorem alone.

### Hypotheses and objects

- `R : Type u`, `[CommRing R]`, `T : Over S`, and `e : T.left ≅ Spec (.of R)`
  give the stated affine base. `X Y : AlgebraicSpace S`, `f : X ⟶ schemeSpace T`,
  `g : Y ⟶ schemeSpace T` are the two spaces over it. The ambient scheme `S`
  permits all the geometric squares in one category; the target is explicitly affine.
- `hf`, `hg : MapIsFlat ...` are the published chartwise-flat predicates.
  `hfc`, `hgc : MapIsQuasiCompact ...` are the published affine-test predicates;
  `hfs`, `hgs` apply this predicate to the relative diagonals, exactly quasi-separatedness.
- `Poincare.product f g` is the existing `enlargedFibreProduct`, with actual
  `Poincare.fst`, `Poincare.snd`. `productMap` is its structural composite and
  `productMap_snd` records the other composite's equality.
- `O X` abbreviates the existing unit structure module. `H` is literally
  `((Sheaf.Γ ... AddCommGrpCat).rightDerived n).obj` of the underlying additive sheaf.
  `moduleH` restricts the recorded global-function action along `affineGlobalScalar`.
  Thus it does not substitute Ext, a chosen decomposition, or unrelated scalar data.
- `hX`, `hY` require `Module.Finite R H ∧ Module.Projective R H` for every natural
  degree. Finite projective is the direct-summand-of-finite-free condition.
  `bX`, `bY` say there exists a natural bound above which `H` is `Subsingleton`;
  for these additive groups this is exactly vanishing.
- `N : ModuleCat.{u} R` has no flatness, projectivity or finiteness condition.
  `coefficients` uses the existing `affineScalarPullback`: the ordinary sheafified
  O tensor_R N, fixed by its scalar-extension/global-sections adjunction.
  `baseModule` is the actual ordinary `B ⊗[R] N` after localization.
- The existing `HasDerivedCategory.{u}` binders supply localization models, as in
  the recorded ringed-site interfaces; no new abelian structure or geometric
  hypothesis is chosen. All universes and term variables are explicitly bound.

### Maps and each conclusion

- `alpha_existsUnique` fixes the canonical linear coefficient map on every tensor:
  `a ⊗ v` goes to `mapH` of the adjunction-unit sheaf map sending 1 to 1 tensor v.
  This normalization uniquely determines the map; `alpha` uses that unique object.
  `alpha_cup` additionally identifies it with the existing global cup by the
  degree-zero section `sectionClass ... (unit.app N v)` and the ordinary unitor.
- `summands ... n` is the direct sum over the subtype of pairs `(i,j)` with
  `i+j=n`, of the actual `H_X^i ⊗[R] H_Y^j`. `includeTensor` is `DirectSum.lof`
  on a pure tensor. There are exactly the indicated degree pairs.
- `external` pulls the two classes along the actual projections using
  `structurePullback`, then applies `multiply`, which is `globalCupWith` with
  structure-sheaf multiplication. `kappa_existsUnique` fixes every homogeneous
  tensor-with-coefficient generator to `alpha (external a b ⊗ v)`. Together with
  `alpha_cup` this is exactly `(pX*a cup pY*b) cup (1 tensor v)`.
- `projective_cohomology_coefficient_kunneth` asserts `Function.Bijective` for
  `alpha_X`, `alpha_Y`, `alpha_P`, and `kappa_N`, for every `N,n`. These maps
  are linear, so this is the asserted module isomorphism statement. It also records
  bijectivity of the structure-coefficient map `kappaStructure` in each degree.
- `alpha_natural` and `kappa_natural` give the full commuting squares for every
  coefficient homomorphism and every input tensor, without exactness assumptions.
- `derivedPullback` is the actual geometric derived-adjunction unit, followed by
  `spaceDerivedSectionsComposition`, followed by the universal left-derived counit
  on the coefficient single complex and the specified sheaf coefficient map.
  `pullbackH` takes homology and transports by `cohomologyComparison`.
  This construction applies to arbitrary geometric morphisms, including nonflat ones.
  It avoids imposing flatness from the older `ReducedCoproduct.pullbackFamily` API.
- `structurePullback` uses `Poincare.pullbackUnit`; `coefficientPullback` uses the
  already recorded pure-section-normalized `ReducedCoproduct.coefficientComparison`.
  `pullback_smul` gives R-linearity. `alpha_geometric` is the commuting coefficient
  square on all pure tensors; additivity and R-linearity give the entire square.
  These laws hold for all T-morphisms, hence for all the spaces in the node's hypotheses.
- `pullback_id`, `pullback_comp`, `pullback_cup` give preservation of identities,
  composition, the multiplicative unit and cup. The last law is literally a cup-product
  equality in each degree, not a merely existential choice of compatible maps.
- `cup_laws` states associativity with the necessary degree cast, both unit laws,
  bilinearity as an R-linear map into R-linear maps, and graded commutativity
  `ba = (-1)^(i*j) • ab`. `castH` transports only the degree equality.
- `kappaStructure` has the same external pure-tensor formula with structure coefficients.
  `kappa_structure_coefficients` identifies its coefficient-R version through alpha.
  `external_signed_product` is the generator formula for multiplication, with sign
  `(-1)^(j*k)` for the crossed factors b,c. Pure tensors and direct-sum inclusions
  generate, so the equality specifies the full graded-algebra multiplication.
  `external_unit` gives its unit. With homogeneous bijectivity these are precisely
  the N=R graded-algebra isomorphism clauses.
- `baseCoefficient_existsUnique` supplies the canonical coefficient identification
  for a change of affine base; it retains the commuting structural square `sq` and
  the equality `spaceAffineRingMap ... = algebraMap R B`. Its normalization is
  exactly 1 tensor v mapping to 1 tensor (1 tensor v); local tensor balancing gives
  the unique isomorphism. `basePullback` uses it and the same derived pullback.
- `localization_alpha` is the alpha square for `[IsLocalization.Away s B]`, on every
  generator. `base_cup` records base-change preservation of cup and its unit.
  `localization_cohomology` takes an actual Cartesian square and flat qcqs f and
  gives the unique bijective B-linear map from `B ⊗[R] H(X,N_X)` to the localized
  cohomology, normalized by `b ⊗ a ↦ b • pullback(a)`.
  `localization_kappa` gives the Kunneth square on every homogeneous pure generator
  for compatible maps of the two factors and their fibre products. `sqX`, `sqY`,
  `sqP`, `fstP`, `sndP` describe this actual diagram; the assertion applies in
  particular to its Cartesian localization diagram. Tensor and direct-sum generation
  give the full square, including arbitrary multiples by B.
- All coefficient categories are ordinary module sheaves on the existing small étale
  ringed models. No constant finite étale coefficient or l-adic substitute appears.

### Dependency declarations and interfaces

The original dependencies were read through their recorded declarations:
`Scheme` (Mathlib.AlgebraicGeometry.Scheme), `AlgebraicSpace`
(Sheaf.AlgebraicGeometry.AlgebraicSpace), the actual space fibre products
(Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers),
`ringedSiteModules` = `SheafOfModules` (Sheaf.CategoryTheory.RingedSiteModules),
the existing sheaf tensor (Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses),
`AlgebraicGeometry.Flat` (Mathlib.AlgebraicGeometry.Morphisms.Flat), and
`SheafOfModules.RingedSiteCup.globalCupWith`, `globalCohomologyModule`,
`globalCohomologyLinearEquiv`, `globalUnderlyingSections`
(Sheaf.CategoryTheory.RingedSiteModuleCupProduct).

Added five already-landed statement dependencies, with no changes to their records:

- def-sfb-space-affine-global-sections: `affineGlobalScalar`, `affineScalarPullback`,
  `affineScalarAdjunction`, `affinePullbackSection` in SpaceAffineGlobalSections.
- def-sfb-space-affine-hom-comparison: `spaceAffineSections`,
  `spaceAffineDerivedSections`, `spaceDerivedAdjunction`,
  `spaceDerivedSectionsComposition`, `spaceAffineRingMap` in SpaceAffineHomComparison.
- def-sfb-abelian-affine-reduced-coproduct: `ReducedCoproduct.coefficientComparison`
  in AbelianAffineReducedCoproduct; its flat-only cohomology family is NOT used.
- def-sfb-abelian-space-poincare-data: `Poincare.product`, `fst`, `snd`,
  `pullbackUnit` in AbelianSpacePoincareData.
- lem-sf-ringed-derived-native-tensor: `RingedDerivedNative.monoidal`,
  `comparison` in RingedDerivedTensorNative. `tensorModel` restricts this actual
  comparison to the flat K-flat representatives required by the cup interface.

The affine-sections comparison helper is uniquely normalized by evaluation of
O→F on 1 on every étale chart. Its derived comparison uses exact scalar restriction
and right-derived composition. It introduces no arbitrary natural isomorphism.
The geometric cohomology helper and base coefficient helper are constructions
of the maps specified by this item's own naturality/base-change clauses, and are
all listed in `lean.declarations`, with source and complete theorem proof docstrings.
They are not replacement definitions for the recorded dependency notions.
No new nodes or dependency-record repairs were necessary.

All recorded proof dependencies with modules are imported as plain proof imports.
The unstated derived external-cup proof dependency is kept as its DAG proof prerequisite;
it is not needed to type the present statement. The main docstring contains the
node's ten-step proof, including projective cycle lifts, K-flat computation, the
projection-unit coefficient normalization, localization and Koszul signs.

### Searches

- msearch.py leanfinder: `coherent cohomology algebraic spaces finite projective Kunneth
  arbitrary module coefficient cup product` returned eight unrelated cotangent,
  generic sheaf cohomology and condensed-module results; no matching theorem.
- msearch.py loogle: `Module.Projective, Module.Finite, TensorProduct` returned twelve
  module/dual/tensor results, not the coherent geometric assertion.
- msearch.py grep: `kunneth|Kunneth|coefficient.*cohomology`, restricted to
  Mathlib/AlgebraicGeometry, returned zero results.
- `rg` of WeilConjectures and Sheaf for projective/coefficient/coherent Kunneth and
  cup declarations found scheme-over-field coherent results and the ringed-site
  derived/global cup APIs, not this arbitrary-base-ring coefficient statement.
  Searching the exact item id found the citing AbelianH2ReducedCoproductInjective
  docstring, not an existing declaration of the item.
- `tools/blueprint_refs.py search 'coherent cohomology'` returned eight unrelated
  blueprint/node hits; the inspected item remains the existing node for this theorem.
- Further source searches located the exact scalar pullback, coefficient comparison,
  normalized derived adjunction, homology comparison and native tensor interfaces
  used above. In particular the older geometric cohomology pullback required flatness;
  the new helper instead composes the existing universal derived unit/counit maps.

No exact existing theorem was found. No mathematical statement correction or
STATEMENT-DISPUTED issue was needed.

### Edge cases and validation

Checked: N=0, nonflat N=R/I, R the zero ring, empty spaces, degrees zero and above
both bounds, localization at s=0 and s=1, and characteristic two. The degree-pair
sum includes (0,n), (n,0), and only (0,0) in degree zero. Vanishing uses
Subsingleton, which includes the zero group without needing a chosen zero object.
The signs are ring scalars and become 1 in characteristic two. Nothing requires
2 invertible, a field, properness, finite presentation, nonzero rings, or flat N.
Identity and arbitrary nonflat geometric maps use the same derived construction.

Every compilation used scompile.py. The final module compiles cleanly in both
sandbox and library modes, including its proof imports, within the per-file limit.
No global build or direct read-clone mutation was run.

## Second reading by Q57

The delivered section under this heading was a self-audit ("a second clause-by-clause
self-reading, not an independent agent review"; delivery-errors H11). The maintainer's
reviewer replaces it with an independent reading. That reading used the node, Stacks
spaces-perfect.tex 08IN/08IR and sites-cohomology.tex 0FPL/0FPM/0H9A, with the Lean module
and every recorded dependency declaration open.

Node clause by clause, with its Lean and the verdict:

- R a commutative ring, T = Spec R [def-pc-scheme]: `R : Type u` `[CommRing R]`,
  `T : Over S`, `e : T.left ≅ Spec (.of R)`. No other ring hypothesis is imposed. OK.
- X, Y algebraic spaces over T [def-trf-algebraic-space]: `X Y : AlgebraicSpace S`,
  `f : X ⟶ schemeSpace T`, `g : Y ⟶ schemeSpace T`. OK.
- Flat, quasi-compact, quasi-separated structure maps: `MapIsFlat f`
  (def-sfb-space-morphism-properties: chart test with scheme `Flat`, def-weil-flat-morphism);
  `MapIsQuasiCompact f.hom.hom` (def-sfb-proper-curve-moduli: every affine test);
  `MapIsQuasiCompact (pullback.diagonal f.hom.hom)`, which is the relative diagonal. The same
  holds for g. Both owners lie in the stmt_dep closure (via def-sfb-abelian-space-poincare-data).
  OK.
- P = X ×_T Y with p_X, p_Y: `Poincare.product f g` = `enlargedFibreProduct`, `fst`/`snd`
  are `pullback.fst/snd` (lem-trf-space-fibre-products-etale-covers);
  `productMap = fst ≫ f`; `productMap_snd` is a proof obligation (Prop). OK.
- H^i(Z, M) as right-derived global sections of the underlying additive sheaf:
  `H` = `(Sheaf.Γ … AddCommGrpCat).rightDerived n` applied to `toSheaf F`. The R-action is
  the global-function action restricted along `affineGlobalScalar`. OK.
- H_X^i, H_Y^i finite projective for all i, vanishing for large i:
  `Module.Finite ∧ Module.Projective` ∀ i : ℕ; `∃ b, ∀ i > b, Subsingleton`. OK.
- Arbitrary N, N_Z = O_Z ⊗_R N: `N : ModuleCat.{u} R` with no condition;
  `coefficients = affineScalarPullback` (def-sfb-space-affine-global-sections), the
  sheafified O ⊗_R N fixed by its adjunction. This is the recorded notion. OK.
- α_{Z,N}^n canonical: `alpha` = the ∃!-pinned linear map, with a ⊗ v ↦ H^n(1 ↦ 1⊗v)(a)
  (the adjunction unit). `alpha_cup` identifies it with the cup with the degree-zero section
  1⊗v, which is the node's "c·n". OK.
- κ_N^n with (a⊗b)⊗n ↦ (p_X^*a ⌣ p_Y^*b)·n: `summands` = ⊕_{i+j=n} H_X^i ⊗ H_Y^j.
  `external` = `globalCupWith` (def-sfb-ringed-site-module-cup-product) of the two
  structure pullbacks, with multiplication λ_ on the unit. `kappa` is ∃!-pinned on every
  homogeneous generator to `alpha_P(external a b ⊗ v)`. OK.
- Conclusion, ∀ N, n: α_X, α_Y, α_P and κ_N bijective (linear maps, so these are isomorphisms),
  plus κ_R (`kappaStructure`). Quantifiers are in the node's order. OK.
- Naturality in N: `alpha_natural`, `kappa_natural`, for all module maps. OK.
- Naturality for T-morphisms, with identities, compositions, units and cups:
  `pullbackH` is the derived adjunction unit, then `spaceDerivedSectionsComposition`, then the
  derived-pullback counit on single complexes. It is defined for arbitrary (also non-flat)
  maps. `alpha_geometric`, `pullback_smul`, `pullback_id`, `pullback_comp` and `pullback_cup`
  give the remaining clauses. The scope is no narrower than the node's. OK.
- Localization R → R_s and base changes: `baseCoefficient` (∃!, 1⊗v ↦ 1⊗(1⊗v)),
  `localization_alpha`, `localization_kappa` (all generators), `localization_cohomology`
  (Cartesian, flat qcqs, B ⊗ H ≅ H_B with the pinned formula), `base_cup`. OK.
- Cup associative, unital, bilinear, graded commutative with (−1)^{ij}: `cup_laws`. OK.
- κ_R* an isomorphism of graded algebras with sign (−1)^{deg b deg c}: `kappaStructure`
  bijective, `external_signed_product` (sign (−1)^{j·k}, j = deg b, k = deg c), and
  `external_unit`. OK.
- Quasi-coherent structure-module coefficients only, no constant étale or pro-étale
  substitute. OK.

Edge cases: n = 0 (only (0,0) in summands), N = 0, non-flat N = R/I, the zero ring R
(Subsingleton covers it), empty spaces, s = 0 and s = 1, characteristic 2 (signs are ring
scalars). None of these is excluded by an extra hypothesis.

Dependencies: the five added stmt_deps are landed and are used directly.
lem-sf-ringed-derived-native-tensor is a theorem node. The item uses its `comparison`, the
inverse of the native lax tensorator, which exists only through the proved `isIso_mu`. This is
an object the theorem constructs, and the node was already in the statement closure via the
cup-product definition node. No dependency record or module is changed. No duplicate notion was
found (no other corner, cup or general cohomology pullback for algebraic spaces exists;
the recorded `ReducedCoproduct.pullbackFamily` requires flatness).
