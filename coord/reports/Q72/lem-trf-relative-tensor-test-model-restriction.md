## Worker report

The new module `Sheaf.Algebra.Homology.RelativeTensorTestModelRestriction` states
`ModuleCat.exists_relativeTensorTestModelRestriction`. Its only theorem proof is
`sorry`; there are no new definitions, auxiliary theorem assumptions, or axioms.
The natural-language statement and accepted proof are unchanged. The item gains
statement dependencies `def-pc-mixed-total-tensor` and `lem-sfb-derived-monoidal`,
both already recorded in the live library: these supply the actual mixed tensor
construction and the native derived tensor that the statement uses.

Sources read: Stacks `more-algebra.tex`, `lemma-tor-amplitude-localization` (0B67),
`section-derived-tensor-product`, `definition-derived-tor` (064M),
`lemma-flip-douoble-tensor-product`, and `section-derived-base-change` (06Y5).
In 0B67 the proof explicitly uses the algebra-module structure on derived tensor
cohomology; 064M defines the unbounded tensor by a K-flat resolution of its second
input. The module docstring records the four accepted proof steps, using the
one-K-flat native tensor comparison of `lem-sf-ringed-derived-native-tensor`
(Tags 06YU, 0FPT) as in the node's proof. The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
was also read. This is an auxiliary algebraic statement, not a unit statement.

Hypothesis and clause correspondence:

- A homomorphism of commutative rings is `{R A : Type u} [CommRing R]
  [CommRing A] (φ : R →+* A)`. An arbitrary common universe covers any pair of
  rings and modules by taking its maximum; no fixed small universe is imposed.
  The derived category has arbitrary chosen morphism universe `w`, through
  `[HasDerivedCategory.{w} (ModuleCat.{u} R)]`.
- The outer existential is a single function `η`, quantified over every
  `K : CochainComplex (ModuleCat.{u} A) ℤ`, `N : ModuleCat.{u} R`,
  `P : CochainComplex (ModuleCat.{u} R) ℤ`, its K-flatness, and augmentation.
  Thus the comparisons are simultaneous, rather than independently chosen
  inside each naturality test. There are no boundedness or flatness binders.
- K-flatness is exactly the dependency's
  `(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P`.
  A resolution is `ε : P ⟶ (CochainComplex.singleFunctor ... 0).obj N`
  with `QuasiIso ε`; there is no projectivity, degreewise flatness, or
  quasi-isomorphism assumption on `K`.
- The explicit A-complex is `((mixedTotalTensor φ).obj K).obj P`.
  The recorded upstream construction is the direct-sum total of the bifunctor
  `M ⊗_A (A ⊗_R E)`, canonically `M ⊗_R E`, with A acting through M.
  Its differential is the signed total differential from `map₂CochainComplex`,
  so A-linearity and the specified action belong to the actual object type.
- Restriction is the existing `(restrictScalars φ).mapHomologicalComplex (.up ℤ)`.
  The type of `η` is precisely an isomorphism from Q of restriction of that
  explicit A-complex to `Q(Res K) ⊗ Q(N[0])` in `DerivedCategory (ModuleCat R)`.
  The tensor is the native monoidal tensor from `hasDerivedMonoidalCategory`.
  `Q_A` is not separately bound: no expression in the node's conclusion uses it;
  the explicit model already lives in complexes of actual A-modules.
- The first conjunction quantifies over `K,K',N,N',P,P'`, the two K-flatness
  proofs and two quasi-isomorphism augmentations, then `f,g,h` with exactly
  `h ≫ ε' = ε ≫ (singleFunctor ... 0).map g`. Its left total map is
  `((mixedTotalTensor φ).map f).app P ≫ ((mixedTotalTensor φ).obj K').map h`,
  which sends a pure tensor to `f(x) ⊗ h(y)` by bifunctoriality. The equality
  after applying Q is the requested commuting square, with right arrow the
  tensor of Q(Res f) and Q(g[0]). Composition uses Lean's left-to-right `≫`.
- The second conjunction is the particular scalar square, with `a • 𝟙 C`
  on the explicit complex and `Q(Res (a • 𝟙 K)) ⊗ₘ 𝟙 Q(N[0])` on the derived
  tensor. Both are actual scalar morphisms, not arbitrary endomorphisms.
- The third conjunction uses the actual A-module `C.homology n` and an
  isomorphism from its scalar restriction to the derived tensor's R-cohomology.
  It fixes that isomorphism to the composite of the inverse exact-restriction
  homology comparison, inverse `homologyFunctorFactors`, and homology of the
  same chosen `η`. Its final square says multiplication by any `a : A` on
  this actual A-module is the induced derived endomorphism. Thus no new
  arbitrary action or independent unconnected cohomology isomorphism is used.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; its recorded signatures and
  localization-at-quasi-isomorphisms instance were read. Cohomology and its
  factorization are `DerivedCategory.homologyFunctor` and
  `DerivedCategory.homologyFunctorFactors` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, both tensor functors preserve the
  quasi-isomorphism property. Also read its specialized equivalence
  `CochainComplex.kFlat_iff_preservesQuasiIso` in the recorded flat/KFlat module.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  the signed total used by the complex tensor; public import retained.
- `WeilConjectures.Algebra.Homology.MixedTotalTensor`:
  `ModuleCat.mixedTensor`, `ModuleCat.mixedTotalTensor`, with their full
  signatures and source docstrings. This is the canonical existing model.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`:
  `DerivedCategory.hasDerivedMonoidalCategory` and its monoidal instances;
  the needed flat-resolution instance for ordinary modules is in
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.
- `Sheaf.Algebra.Homology.RingedDerivedTensorNative` is a plain proof import,
  as required by the proof dependency. Read `localization_isIso_mu`,
  `inverse_naturality`, `tensorIso` and the ringed-site interface.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` supplies exact
  scalar restriction; `ShortComplex.mapHomologyIso` is the canonical
  cohomology comparison. `Mathlib.Algebra.Homology.Linear` supplies scalar
  endomorphisms of complexes.

Edge cases checked mathematically before and after writing:

- `K=0`, `N=0`, and an acyclic K-flat resolution of zero yield zero derived
  tensors. The family and squares retain these cases, with no nonzero binders.
- The nonflat map `ℤ → ℤ/2`, `K=(ℤ/2)[0]`, and the usual two-term free
  resolution `P=(ℤ --2--> ℤ)` of `N=ℤ/2` give cohomology `ℤ/2` in degrees
  -1 and 0 on both sides, with the actual `ℤ/2` action. No flat A/R condition
  may be added; none appears.
- `f=g=h=0` satisfies the augmentation square and gives the zero naturality
  square. Identity maps recover the identity square. In particular h need
  not be a quasi-isomorphism, and the formula never assumes that it is.
- Arbitrarily unbounded complexes are allowed: no finite-support, boundedness,
  or finite-sum hypothesis is present, and `mixedTotalTensor` uses coproducts
  along the full integer diagonal.
- The zero ring, scalar `a=0`, scalar `a=1`, negative cohomological degrees,
  and arbitrary derived-category morphism universe remain permitted.

Searches actually run with `msearch.py Q72 <item>`:

- LeanFinder: "Tensor an algebra module complex with a K-flat module resolution
  gives the derived tensor over the base ring naturally in both chain maps and
  augmentations". Eight hits: ordinary flat tensor exactness, tensor instances,
  `HomologicalComplex.HasTensor`, good tensor conditions, classical Tor. None
  gives the simultaneous comparison with augmentations.
- Loogle: `DerivedCategory.Q, CochainComplex.mapBifunctor`. Zero hits.
- Mathlib grep: `KFlat|kFlat|mixedTotalTensor`, subdirectory `Algebra/Homology`.
  Zero hits (the K-flat implementation is upstream, not in pinned Mathlib).
- LeanSearch: "Unbounded derived tensor of an algebra complex with a K-flat
  resolution is natural in both factors". Eight hits on ordinary left/right
  derived zero, `Functor.mapDerivedCategorySingleFunctor`, projective-resolution
  naturality, flip naturality, and classical `Tor`/`Tor'`. None is the item.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for `mixedTotalTensor`,
  scalar restriction/tensor and `tensorRightCounit`, plus exact item-id search
  and `dag/lean_names_upstream.json` search. Found the existing model,
  `MixedTensorUnderlyingHomology` (its restriction comparison is private),
  `FlatModel.QObjTensorQObjIsoOfKFlatRight` and first-input naturality,
  `BalancedDerivedTensorModel`, `DerivedTensorActionNaturality`, and base tensor
  cohomology interfaces. Those do not state this simultaneous both-input and
  augmentation square with the native base derived tensor. The new full name
  `ModuleCat.exists_relativeTensorTestModelRestriction` had no collision.

Validation: the delivered module passes `scompile.py` in module mode, both the
sandbox and library-module checks, with no errors or non-sorry warnings. All
universes and variables are explicitly bound and all lines are at most 100
characters. No statement correction, dependency repair, or disputed claim.

## Second reading by Q72

Author's second pass, not an independent review: re-opened the node and module
and checked the clause correspondence above. The initial syntax around the
function-valued existential's isomorphism needed parentheses; compiler feedback
caught it and it was repaired. Checked especially that h is unrestricted except
for its augmentation square, K is not assumed K-flat, η precedes every map
quantifier, and the cohomology isomorphism is fixed by η and the canonical
factorization rather than independently chosen. The statement dependencies now
also name the already landed mixed tensor and derived monoidal interfaces.
The maintainer's independent review is the independent reading for this direct
delivery; no other agent was started.
