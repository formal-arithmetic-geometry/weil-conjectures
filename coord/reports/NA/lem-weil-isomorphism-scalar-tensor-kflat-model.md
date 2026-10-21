## Worker report

Delivered module: `Sheaf.Paper.IsomorphismScalarTensorKFlatModel`.
Main declaration: `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.isomorphism_scalar_tensor_kflat_model`.
Only this named theorem has `sorry`. Its docstring contains all seven DAG proof steps,
with their dependency names. All helper definitions have complete data; no theorem is proved.
The node copy changes only `lean`; there are no new nodes or dependency repairs.

The prime is `(l : ℕ) [Fact l.Prime]`. The two extensions are `(E L : Type u)` with
`Field`, `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]` instances; the inclusion is
`ι : E →ₐ[ℚ_[l]] L` (injective because its source is a field). The existing Padic
coefficient constructions select the valuation rings and uniformizers. No uniformizer
compatibility, unramifiedness, finite-type scheme, or boundedness assumption is added.
The schemes are `X Y : Scheme.{t}`, the arrow is `g : X ⟶ Y`, and `[IsIso g]`
is the stated scheme-isomorphism hypothesis. `_hX` and `_hY` state invertibility of
`l` at every stalk on the two schemes. Site object size is `t+1`, Hom size `t`,
and coefficient/module size `max u (t+1)`; coefficient and scheme universes remain
independent. The already-recorded same coefficient universe for E and L is harmless:
both can be placed in their common ambient universe, without identifying it with t.

All rings and maps in the preamble are the existing constructions:
`completedIntegralCoefficientSheafUnrestricted`, its commutative presentation,
`integralCoefficientCommRingSheaf`, the completed projections, and
`integralScalarQuotientSheafMap`. The latter is the same-index map iota_m;
the index `n : ℕ` here means `m=n+1`, covering precisely every positive m.
`inverseImageIntegralModules` and `inverseImageFiniteModules` are the recorded
sectionwise inverse image with action through the inverse of c_F. In this model,
sections at U are literally the sections at `(proEtaleIsoPostcompose g).obj U`.
The completed coefficient map is the recorded limit lift of its finite components,
so its defining projection equations are retained, not supplied as extra hypotheses.

Clause-by-clause correspondence (all specification names below are in the main
namespace, and are explicit Prop-valued definitions in the delivered module):

1. Input flat-term K-flatness is exactly the full subcategory
   `(integralOperationsGoodComplex l E Y).FullSubcategory`. Its predicate is the
   recorded `IsKFlatIndependentCoefficients` and termwise `IsFlatOnSite` conjunction.
   `PreservesModels` gives that same predicate for G_E P over R_X, Q over S_Y,
   and Z over S_X. Q is `completedOrdinaryScalarComplex ... Y`; Z is `leftComplex`.
2. `b` is a natural isomorphism from the inclusion followed by `leftComplex`
   to the inclusion followed by `rightComplex`. Thus each b_P is a chain isomorphism
   of S_X-modules and is natural for every chain map between the stated inputs.
   `CompletedFormula` evaluates its hom on `completedScalarTensorSection`:
   c_L(s_0) tensor y maps to the inverse image of s_0 tensor p. The tensor API
   writes scalars first; this is the node's p tensor s with the standard symmetry.
   These are the existing scalar-extension tensors, not a second tensor product.
3. `finiteLeft` is precisely reduce P over E on Y, inverse image using c_E,m,
   then finite extension by iota_m on X. `finiteRight` is direct finite extension
   to B_L,Y,m followed by inverse image using c_L,m. `bfin n` is a natural
   isomorphism between these finite-coefficient complex functors. `FiniteFormula`
   says t tensor (a tensor p) maps to inverse image of
   (c_L,m inverse(t) * iota_m(a)) tensor p, fixing the canonical reassociation.
   Its evaluation after `integralOperationsRestrict` is the identical underlying
   section map; restriction changes only the action and is faithful.
4. `vleft` and `vright` are natural chain maps after restricting the two finite
   target actions along pi_L,m, so the upper completed and lower finite maps are
   compared in the actual common S_X-module category. `LeftQuotientFormula`
   specifies y tensor s maps to (inverse image of 1 tensor p) tensor pi_L,m(s).
   `RightQuotientFormula` is inverse image of s tensor p maps to
   inverse image of pi_L,m(s) tensor p. `QuotientSquare` is the requested equality
   b_P followed by the right quotient equals the left quotient followed by b_P,m.
   These existential maps are fixed on every local pure tensor, not arbitrary maps.
5. `tleft` and `tright` are the natural consecutive quotient maps.
   `LeftTransitionFormula` reduces t by q_L,X and a by q_E,Y in each double tensor;
   `RightTransitionFormula` reduces the final scalar by q_L,Y.
   `TransitionSquare` says exactly that b_P,m commutes with these transitions.
   No assumption equating the uniformizers or rescaling the finite index is used.
6. `β` is a natural isomorphism of the entire ordinary unbounded derived categories,
   with source `inverseImageIntegralDerived ... E g ⋙ completedDerivedScalarExtension ... X`
   and target `completedDerivedScalarExtension ... Y ⋙ inverseImageIntegralDerived ... L g`.
   Despite its name, the recorded `completedDerivedScalarExtension` is the ordinary
   derived change of rings for the completed coefficient SHEAVES, not completed tensor:
   read its definition and universal change-of-rings witness in
   `FiniteFreeCompletedScalarComparison.lean`, lines 157–197.
7. `DerivedModel` states that the existing scalar counits for P and G_E P are
   invertible, so Q represents C_Y[P] and Z represents C_X[G_E P]. Its final equation
   conjugates `[b_P]` by precisely these counits and the exact inverse-image
   `mapDerivedCategoryFactors` comparisons, identifying it with β_[P]. This is a
   normalized representative equation, not just existence of an unspecified derived iso.
   For ANY flat-term K-flat resolution q:P→K, apply naturality of β to `[q]`, which
   is invertible, and the same counit/factorization maps: it gives the stated b_K
   computed by `[b_P]`. Two resolutions give the same component β_K under those
   canonical representative identifications. This formulation therefore includes
   naturality and resolution independence without selecting a resolution of K.
   No derived completeness or constructibility predicate appears anywhere.

Dependencies read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`
  and its public `CoefficientExtension` constructions, in particular
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `coefficientExtensionTransition`.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration;
  the required Scheme and IsIso notions are the Mathlib ones.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the unchanged completed
  ring sheaves and projections, publicly retained through its imports.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`: publicly retained
  `inverseImageCompletedCoefficientMap`, `inverseImageFiniteCoefficientMap`,
  `inverseImageIntegralModules`, `inverseImageFiniteModules`, and
  `inverseImageIntegralDerived`. The comparison with COMPLETED pullback is not
  used in place of ordinary inverse image.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  independent-universe tensor and its exactness infrastructure.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  total-tensor convention used by the K-flat predicate. Scalar rings here are
  concentrated in degree zero, so termwise extension has differential d tensor 1.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: the existing arbitrary-universe
  integral scalar construction and its quotient maps (`IntegralScalarExtensionWellDefined`),
  `integralScalarReduction`, `integralScalarFiniteComplex`, `integralScalarTensorSection`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: existing `completedCoefficientMap`,
  `completedOrdinaryScalarExtension`, `completedOrdinaryScalarComplex`,
  `completedDerivedScalarExtension`, `completedScalarCounit`, `completedScalarTensorSection`.
  The finite-freeness/completeness THEOREM is not assumed or used in the statement.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`.
  `finiteChangeData` selects this already-existing universal witness; its E object
  and map functions are prescribed by obj_eq/map_eq. Only this uniquely determined
  ordinary functor and its obj_eq identification are used; no arbitrary new map,
  comparison, or derived functor is introduced by this selection.
- Proof-only imports retain the recorded
  `ringedTopoiCanonicalDerivedTensorPullback`, `changeOfRings_isKFlat_of_flat_terms`,
  `inverseImage_tensor_hom_iso`, and
  `site_derived_tensor_descent_independentCoefficients` modules. K-flat resolution
  and ordinary derived change of rings are already in the public import closure.

Searches made before writing:

- msearch leanfinder: "inverse image along an isomorphism commutes with scalar extension
  on K-flat complexes of sheaf modules". Eight hits, including
  `SheafOfModules.conjugateEquiv_pullbackComp_inv` and free-pullback lemmas; no exact statement.
- msearch loogle: `SheafOfModules.changeOfRings, CochainComplex.IsKFlat`.
  No hits; unknown identifier SheafOfModules.changeOfRings in the search service.
- msearch grep: `changeOfRings|IsKFlat` under Algebra/Category/ModuleCat/Sheaf.
  One Mathlib ChangeOfRings import hit; no statement of these normalized K-flat models.
- msearch leansearch: "inverse image along scheme isomorphism commutes with extension
  of completed coefficient rings on K-flat complexes". Eight unrelated ring-flatness,
  scheme-isomorphism, and K-projective hits; no exact match.
- rg and grep in `lean/WeilConjectures` for the item id, scalar/inverse-image tensor
  names, and K-flat scalar models: no exact item declaration.
- rg in `lean/Sheaf`: found `KFlatScalarComparisonNormalization`,
  `ScalarInverseImageTowerDiagram`, and `IsomorphismComparisonScalarExtension`.
  Read their interfaces. The first two use different general presentations/universes;
  the parent gives a module tensor comparison with an equal-universe exact ordinary
  scalar functor, not this independent-universe finite-tower K-flat and counit assertion.
  Reused all applicable coefficient and tensor constructions rather than copying them.
- Searched the new namespace and theorem name in both project roots: no collision.

Source check: read the node and all eleven statement-dependency statements/records,
the recorded declarations and their public constructions, and the seven-step proof.
Read Bhatt–Scholze PDF pages 50–51 with pdftotext: 6.5.9(4) concerns completed pullback;
the ordinary coefficient-extension identity here is explicitly the node's own calculation.
The source does not justify adding qcqs, completeness, or constructibility hypotheses
to this site-equivalence tensor calculation, and none are added.

Edge cases checked before drafting: P=0; g=id; E=L with the identity inclusion;
positive exponent m=1 (n=0); ramified E⊂L (same-index quotient inclusions, no
uniformizer equality); empty schemes; arbitrary unbounded complexes; independent
scheme and coefficient universes. All formulas retain these cases. For E=L the
completed and finite formulas are ordinary scalar multiplication after unit insertion;
for g=id they are the same reassociation maps. There is no disputed statement or
source-based correction.

Validation: every delivered file is compiled through scompile.py. The large original
conjunction was decomposed into ten explicit specification definitions, and unnecessary
unfolding was restricted locally; this changes no mathematical clause. The 60-second compile limit
was never increased. The final sandbox and module compiles were clean (7.9 and 7.6 seconds). The final source has no local notation, local instances, private definitions,
auto-implicit variables, or data holes.

## Second reading by NA

This is the worker's own clause-by-clause self-check above, not an independent second
agent review. The dispatcher explicitly prohibits starting other agents and specifies
independent review by the maintainer. Reopened the node and the final Lean file to check
all ten specifications, map directions, transported actions, positive indexing, and the
last representative equation. Corrected the finite scalar type annotation and evaluated
finite comparison generators after the faithful restriction functor. No mathematical
statement was changed. The maintainer's independent review remains the delivery review.
