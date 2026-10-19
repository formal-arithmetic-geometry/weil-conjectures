## Worker report

The item is stated by `WeilConjectures.isomorphismComparison_scalarExtension` in
`Sheaf.Paper.IsomorphismComparisonScalarExtension`. The original natural-language
statement, proof and dependencies are unchanged. The dependency repair is an ambient-object evaluator for the specified integral
comparison. It directly uses the existing independent-coefficient K-flat resolution
theorem and transports its published flatness conclusion through the existing
canonical tensor presentation isomorphism. The evaluator publicly retains the original comparison. No statement correction or new DAG node
is needed. All theorem proofs in this packet are `sorry`; definitions have real data.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite coefficient extensions: `E L : Type u`, their `Field`, `Algebra ℚ_[l]`,
  and `FiniteDimensional ℚ_[l]` instances, with `ι : E →ₐ[ℚ_[l]] L`.
  A unital field algebra homomorphism is injective, so this represents E⊂L without
  requiring a particular ambient algebraic closure. The recorded coefficient
  constructors retain their integer rings, chosen uniformizers and finite quotients.
- Scheme isomorphism: `g : X ⟶ Y`, `[IsIso g]`.
- Ell invertible on both schemes: `hX` and `hY` assert
  `IsUnit (l : W.presheaf.stalk x)` at every point.
- Small pro-etale sites and completed rings: `integralTowerModules l F W`, based
  on `Scheme.ProEt.topology W` and the existing completed coefficient sheaf.
  Site objects have universe u+1 and arrows universe u; these are not identified.
- G_F and transported actions: `inverseImageIntegralDerived l F g`, the exact
  localization of `inverseImageIntegralModules`. The latter uses the inverse of
  the actual `inverseImageCompletedCoefficientMap`, fixed by its finite projections.
- Specified κ: `inverseImagePullbackComparisonDerived l F g hX hY K` evaluates
  exactly `inverseImagePullbackComparison`, part (b), on a chosen representative
  and its K-flat flat-term resolution, then conjugates by the representative iso.
  There is no arbitrary map, existential comparison assumption, or assumed naturality.
- K in D^b_c(Y,O_E): `K : DerivedCategory (integralTowerModules l E Y)` and
  `hK : sfIntegralConstructible l E Y K`. This is the existing completeness
  predicate plus finite constructible reductions with one common finite interval.
- Integral T_W: `integralScalarExtension l E L ι W`. The independent-universe
  recorded `integralScalarExtensionOfUniverses` specializes definitionally to this
  same chosen descent and the same normalized strict-tower comparison.
- Ordinary C_W: `integralOrdinaryDerivedScalar l E L ι W`, the exact finite-free
  tensor model. `isomorphismScalarSheafModel_existsUnique` fixes the comparison
  with `completedOrdinaryScalarExtension` on EVERY sheafified pure tensor.
  `isomorphismScalarModel_existsUnique` then fixes its comparison with
  `completedDerivedScalarExtension` by the universal counit on EVERY complex.
  Its second equation identifies `scalarCompletion` with the SPECIFIED
  `completedScalarComparison` through this actual natural isomorphism. Thus this
  is a change of tensor model retaining χ, rather than a substitute completion map.
- b_K: `isomorphismScalarTensorDerived l E L ι g`. The underlying sheaf natural
  isomorphism is uniquely characterized at every U and every pair of local sections:
  its input is the pure tensor of y and `c_L(a)`, and its output is the pure tensor
  of y and a over `(U,g∘u)`. In this canonical sectionwise inverse-image model,
  y=g⁻¹y₀ is literally the same underlying section. This is exactly the node's
  y⊗a↦g⁻¹(y₀⊗a₀) formula, including the specified coefficient transport. The
  displayed `mapDerivedCategoryCompIso` factors descend that SAME isomorphism.
- χ_{W,H}: `scalarCompletion l E L ι W |>.app H`, identified by the explicit
  model-comparison equation above with the finite-free specified completion map.
  Its full quotient augmentation and zero shifted-product coordinate are retained.
- α_K: `isomorphismComparisonScalarAlpha`; expand it as inverse χ on Lg_E*K,
  the recorded `scalarPullbackOrdinary.hom.app K`, then Lg_L*(χ_{Y,K}).
  This is the existing `scalarPullbackCompleted` formula, without adding proof
  binders for completeness consequences of `hK`. Its ordinary comparison is
  normalized by all strict tower maps and BOTH Roos coordinates.
- β_K: `isomorphismComparisonScalarBeta`; its definition is exactly inverse χ on
  G_E K, then b_K, then G_L(χ_{Y,K}), in Lean's left-to-right composition order.
- G_E K and Lg_E*K being constructible/complete are stated consequences of the
  recorded isomorphism-derived-pullback theorem, not additional assumptions here.
  The named `isomorphismComparisonInputs_constructible` states those two existing
  consequences. Its two completeness projections let `scalarCompletionIso` supply
  the actual inverses in α and β. Both definitions take the same hK as the item;
  no additional completeness assumption enters the claimed equality.
- The final equality is `T_X.map κ_E ≫ α = β ≫ κ_L` in the actual target derived
  category. This reverses the written order of composition, exactly as Lean's `≫`
  requires. The second κ is evaluated at the actual object T_Y K.

The helper statements are the model identifications and canonical b appearing in
this very item's statement, not independent mathematical hypotheses. Their docstrings
include their normalization and complete construction proofs. The main docstring
carries all eight DAG proof steps, including the cone-coordinate computation and
cancellation. No theorem has been proved in this stage.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its publicly retained coefficient
  integers/uniformizer/quotient constructors.
- `def-weil-scheme-morphism-properties` is explicitly a convention collection,
  with no declaration; the ordinary `Scheme` and `IsIso` notions are used.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; the completed rings it imports are
  `completedIntegralCoefficientSheafUnrestricted` and the commutative-ring version.
- `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageCompletedCoefficientMap`, `inverseImageIntegralModules`,
  `inverseImageIntegralDerived`, `inverseImagePullbackComparison`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`
  and its publicly retained `integralDerivedPullback` and representative comparison.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses`; its retained equal-universe `integralScalarExtension`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarPullbackOrdinary`, `scalarCompletion`, `scalarPullbackCompleted`,
  `scalarPullbackChain`, and `scalarOperationsOrdinary_tower`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedDerivedScalarExtension`, `completedScalarCounit`,
  `completedOrdinaryScalarExtension`, `completedScalarTensorSection`,
  `completedScalarComparison`, `finiteFreeCompletedScalarComparison`.
- `Sheaf.Paper.PurInverseImageTensorHom`: `Scheme.inverseImage_tensor_hom_iso`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `Scheme.isoSectionwiseInverseImage_equivalence`, `proEtaleIsoPostcompose`,
  `isoSectionwiseModuleInverseImage` and its exactness interfaces.
- `Sheaf.Paper.IsomorphismDerivedPullback`:
  `isomorphismIntegralDerivedPullback_termwise` and its full source docstring.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  its essential-surjectivity representative isomorphism and localization.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, imported and used
  directly by `inverseImagePullbackComparisonDerived`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`:
  `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`, retained as a proof import.

The proof-only nodes `lem-weil-isomorphism-derived-pullback-comparison-normalization`
and `lem-weil-specified-pullback-comparison-alpha` have no recorded declaration in
the read-only DAG. Consequently there is no proof-only module to import for them.
Their precise role remains in the main proof docstring; neither is an assumed
hypothesis and neither is needed to type the statement. Existing recorded K-flat
resolution and change-of-rings proof dependencies are imported.

Edge cases checked: identity extension E=L, identity scheme isomorphism, empty
schemes, zero complexes, arbitrary cohomological degrees (including degree zero),
ramified extensions with different uniformizers, and arbitrary choices of the
fixed K-flat representatives. The finite tower is indexed by n+1, so it includes
all positive quotient exponents and never inserts a spurious zeroth quotient.
The formulas require neither flatness of the Roos cone nor a K-flat presentation
of T_Y K. Completeness and constructibility are not asserted for arbitrary inputs;
only the final square is restricted by the recorded bounded constructible predicate.
No statement is disputed.

Searches (2026-10-17 UTC):

- msearch.py leanfinder, “Inverse image to completed pullback commutes with finite
  l-adic coefficient extension”: eight adic-completion results (piEquivFin,
  StrictMono.of_comp_lift, etc.); none concern the specified pro-etale comparison.
- msearch.py leansearch, “Inverse image to completed derived pullback comparison
  is compatible with finite free coefficient extension”: eight results, including
  pullback of free sheaves, sheafificationCompPullback and algebraic adic-completion
  tensor maps; none state the specified scalar square.
- msearch.py loogle, `"SheafOfModules", "pullback"`: twelve ordinary presheaf-module
  pullback results; no completed comparison compatibility.
- msearch.py grep, `inverseImage.*[sS]calar|[sS]calar.*inverseImage|completed.*pullback`:
  no Mathlib hits for the new statement.
- rg in the named upstream WeilConjectures and shared lean/Sheaf trees found the
  chosen-resolution comparison, scalar-operation comparison and other scalar
  exchange constructions, but no declaration with this specific κ scalar square.
  The prescribed grep of the item's blueprint id in upstream found no match.
  A name collision search for the new declarations found none.
- The recorded source PDF was read at its printed pp. 50--51 with pdftotext.
  Lemma 6.5.9(4) supplies completed pullback context; the DAG correctly labels
  the displayed scalar square an agent calculation, not a quotation of that lemma.

## Dependency modules

`def-weil-inverse-image-pullback-comparison` receives the module
`Sheaf.Paper.InverseImagePullbackComparisonDerived` under §1(B). Its old declaration
requires a cochain complex, a good resolution and an augmentation, so cannot be
applied directly at the arbitrary derived object T_Y K. The added evaluator chooses
an essentially-surjective Q representative and the existing flat-term K-flat
resolution, applies the old SPECIFIED part-(b) formula unchanged, and conjugates
by Q's representative isomorphism. The resolution represents the same derived
object through its quasi-isomorphism; it is not a choice of an unspecified map.
All original coefficient maps, finite comparisons and integral comparison remain
publicly imported. Only the dependency's `lean` field changes.

`lem-pc-kflat-resolution` needs no dependency module or node change. The evaluator
imports and uses `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`
directly. Compilation shows that the published artifact returns flatness through
`MonoidalCategory.tensorRight`, while the current source text uses `IsFlatOnSite`.
The existing `SheafOfModules.siteSheafTensorRightIso` from
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients` identifies the two
functors. Applying Mathlib's `(exactFunctor _ _).prop_of_iso` to its inverse
transports that existing flatness proof. This uses only existing declarations and
adds no theorem or assumption. The returned adapter module and resolution node
copy have both been removed. The independent universes are preserved.

## Second reading by NJ

The dispatcher brief explicitly requires this worker to deliver itself and forbids
starting another agent; the maintainer supplies the independent delivery review.
This section records the worker's final source-against-signature recheck, not a
claim that an independent second worker has read the packet. The final square
has the four correct endpoints, the prescribed tensor rule at every site object,
and both coefficient maps in their specified directions. The finite-free tensor
model bridge retains χ rather than merely choosing a nonempty isomorphism.
No extra completeness or resolution-independence assumption was introduced.

Validation: all delivered files are compiled individually through scompile.py;
only the expected sorry warnings are permitted. Final preflight and push are run
through deliver2.py, which also compiles every delivered module again.

## Return repair

The immutable-head return identified the duplicate K-flat resolution statement.
Compared the saved packet against the current shared source and the source returned
by `scompile.py --source Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
The textual signatures agree word for word after changing the theorem name: the
explicit `universe r u v`, `C : Type u`, `Category.{v} C`, coefficient size r,
K-flatness, flat terms, quasi-isomorphism and degreewise epimorphism all coincide.
Removed `KFlatResolutionForIntegralComparison.lean` and its node copy. The evaluator
now imports and calls the existing resolution theorem directly. Compilation of
this direct call diagnosed a source/artifact difference in the flatness predicate.
The already published `siteSheafTensorRightIso` and `exactFunctor.prop_of_iso` supply
the required transport at the point of use. No new theorem, main statement change,
canonical comparison change, or resolution-node metadata replacement is needed.
The saved packet passed its initial dry run; that mechanical pass did not resolve
the independent review's duplication finding, which this repair addresses.
