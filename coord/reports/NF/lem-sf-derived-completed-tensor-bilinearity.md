## Worker report

The item is stated in `Sheaf.Paper.DerivedCompletedTensorBilinearity`, declaration
`CategoryTheory.DerivedCompletedTensor.bilinearity`. This is stage 2: its sole theorem
ends with `sorry`. Its natural-language proof records all seven DAG proof steps.
The new definition node `def-sf-koszul-small-model-completed-tensor` owns all six
`KoszulSmallModel` declarations and `DerivedCompletedTensor.tensor`. It has no postponed
theorem. All definitions contain actual data. The item statement is unchanged.

Hypotheses and objects, checked with the node and source open:

- A site small relative to coefficients is `{C : Type u} [Category.{v} C]
  [EssentiallySmall.{r} C] {J : GrothendieckTopology C}`; no equality between u, v and r.
- The sheaf of commutative rings is `R : Sheaf J CommRingCat.{r}`; module sheaves are
  `KoszulSmallModel.Modules R`, transparently the recorded `ringedSiteModules`.
- `A : Type a`, `[CommRing A]` and the unital ring homomorphism `s` into
  `RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)` render exactly the
  coefficient ring and its global-section action. `coefficientLinear R A s` restricts
  the existing `SheafOfModules.homLinear` along s, using `Module.compHom` on every Hom.
  Its action is `(a f)_U(x)=s(a)|U f_U(x)`; it is never an arbitrary linear structure.
- `DerivedCategory (KoszulSmallModel.Modules R)` and `[HasDerivedCategory.{w} ...]`
  are the unbounded derived category and chosen morphism universe. Its A-action is
  Mathlib `DerivedCategory.instLinear` for that precise module-sheaf A-action.
  The instance-binding lambda supplies the constructed action, not a new hypothesis.
- T is exactly `SheafOfModules.siteDerivedTensorIndependentCoefficients J R`, the
  recorded localization of signed total tensor on flat-term K-flat homotopy representatives.
- `n : ℕ` and `b : Fin n → ...sections` include every finite global-section list.
  The mono `ι : I ⟶ unit` on the canonical small model, and `_hgen` using the existing
  `IsRingedIdealGeneratingList`, specify the generated ideal, without choosing a different
  ideal or requiring a global finite-generation property beyond this very list.
- `KoszulSmallModel.complete R I ι` is the existing local derived internal-Hom vanishing
  condition on every slice and every section in the ideal, transported along the canonical
  site equivalence and its exact derived equivalence. The HasDerivedCategory
  instances on this small model and its slices are the ordinary size convention, not
  boundedness or product-exactness hypotheses. The two derived morphism universes w,w₀
  are independent.
- `L` has codomain the full subcategory defined by that predicate. `η` is an actual
  natural transformation from the identity into L followed by inclusion. `_hL` is exactly
  the universal precomposition bijection stipulated by “its Koszul completion reflector”.
  There is no additivity or scalar-linearity hypothesis on L, T or B. The binders
  describe the given completion reflector by its unit and universal Hom bijection;
  the definition module neither chooses nor asserts existence of a reflector.
- `tensor R I ι L` gives B = inclusion×inclusion, then T, then L,
  definitionally the already landed generic `CompletedTensorComparison.tensor`.
  The new definition node owns this specialization, written directly as the same
  ordinary functor composite. The rational-naturality theorem node is not a statement
  dependency: its plain tensor definition is not a choice from that theorem.

Every conclusion clause:

- `L.Additive ∧ L.Linear A` is the full additivity and A-linearity of the reflector.
- The next universal quantifier over every derived M states Additive and Linear A for
  `(Functor.curry.obj T).obj M` and its `.flip.obj M`, exactly both separate variables.
- The following universal quantifier over complete M states those same four assertions
  for B = `tensor R I ι L`.
- `∀ p : A` introduces S as `Localization.Away p`. `HomAction ...` abbreviates an
  S-linear map into S-linear maps between the actual scalar-first tensor Hom modules.
  These are definitionally the Hom groups of the recorded raw `ScalarLocalization`.
- `∃ β : ∀ M M' N N', HomAction ...` supplies all four-object bilinear maps. The first
  conjunct is `β (x ⊗ f) (y ⊗ g) = (x*y) ⊗ B.map (f,g)`. The second conjunct says
  every other S-bilinear map with that formula equals this one, object by object.
  Thus existence plus the second conjunct renders the node's unique map, not mere existence.
- The third conjunct is the identity equation with `1 ⊗ id`, the raw localized identities.
- The fourth conjunct uses `ScalarLocalization.composition` on arbitrary four localized
  composable arrows; it states β(f≫f',g≫g') = β(f,g)≫β(f',g'). It is not restricted to
  pure tensors and does not assume injectivity of the integral-to-localized Hom map.
- The fifth conjunct substitutes `(IsLocalization.Away.invSelf p)^k` and its t analogue,
  yielding the single denominator of exponent k+t for every k,t : ℕ. Parentheses explicitly
  separate scalar powers from tensor notation.
- The final existential supplies an actual functor F on the product of the two raw
  ScalarLocalization categories, its required object map and its map equal to β on every
  localized pair. HEq only accommodates the propositionally specified object map.
  Functor laws therefore hold on all localized arrows, as asserted in the node.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, the additive and essentially-surjective localization instances.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`; and
  `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`, together with
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `Functor.Additive`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the signed
  total tensor used by the recorded site-derived tensor construction.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`.
- `Sheaf.Paper.WeilCompletedTensorReflector`: `wfCompletionReflector`, read with
  `wfCompletion`, `WfIsComplete`, its actual object and unit; publicly preserved.
  `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`:
  `CategoryTheory.ringedKoszulCompletionReflector`, read in full. The existing live
  reflector attachment and both reflector modules are unchanged by this delivery.
- The unchanged proof dependency supplies the existing `RingedKoszulLimitPresentation` and its `completion`,
  `unit`, strict tower factorization, total right-derived universal property and
  computation on K-injective towers; and `IsLocallyDerivedRingedIdealComplete` plus
  `IsRingedIdealGeneratingList`. Neither these notions nor Koszul complexes are copied.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`, `composition`,
  `localization` and its category/preadditive/linear structures; scalar-first convention.
- `Sheaf.CategoryTheory.LinearScalarLocalization`:
  `exists_linear_scalarLocalization_category`, including raw composition formula.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
  `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated` for proof Step 3.
- `Mathlib.CategoryTheory.Localization.Linear`: `Localization.linear`,
  `functor_linear`, `functor_linear_iff`; and
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange` and
  `TensorProduct.AlgebraTensorModule.distribBaseChange` for bilinear Hom base change.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`:
  `SheafOfModules.homLinear`, valid for independent site and coefficient universes.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.pushforwardPushforwardEquivalence`, used with the actual equivalence
  unit ring maps; `CategoryTheory.Equivalence.mapDerivedCategory` from the upstream
  ExactFunctor module transports this actual equivalence to derived categories.

Searches made (actual results are also in the sandbox searches.jsonl):

- msearch leanfinder, “Derived completed tensor on module sheaves is additive and linear
  separately and extends uniquely to localized Hom modules”: eight hits, including
  IsLocalizedModule.map_lTensor/rTensor, IsLocalization.moduleTensorEquiv,
  PresheafOfModules.Monoidal.tensorObj/tensorObjMap/tensorHom. None states the item.
- msearch loogle, `"Linear", "tensor"`: twelve hits, LinearMap.lTensor/rTensor and their
  identity lemmas, LinearEquiv.lTensor/rTensor; no derived completed assertion.
- msearch grep, `derived.*[Bb]ilinear|[Bb]ilinear.*derived|completionLinear|rationalTensorHom`:
  zero Mathlib hits.
- msearch leansearch, “The derived tensor of module sheaves and its derived completion
  are separately linear and give unique bilinear maps after scalar localization”: eight
  hits, including TensorProduct.mapBilinear, AlgebraTensorModule.mapBilinear, ordinary
  finite Noetherian AdicCompletion, and IsLocalization.moduleLid; no whole-item match.
- rg of the same patterns in WeilConjectures and Sheaf found private `derivedBilinear`,
  `completionLinear` and public `wfRationalTensorHom_exists` in WeilTensorProduct.
  Read them: these require the completed adic coefficient of a scheme, and do not state
  the arbitrary ringed-site, arbitrary global coefficient A, or all conclusion clauses.
- rg for completed tensor definitions found `CompletedTensorComparison.tensor` in
  CompletedTensorRationalNaturality; read and its ordinary composite used directly.
- rg for scalar/global linearity found `scalarSectionLinear` and
  `scalarLocalizationCoefficientLinear`: both require the equal-universe small-site
  encoding. The generalized `coefficientLinear` uses their same restriction construction
  on the independently-universed category; the upstream `homLinear` itself is fully general.
- rg of `KoszulSmallModel|DerivedCompletedTensor` in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json found no collision. Searches for small-model transport
  found scheme-specific completedCechDerivedEquiv and generic module sheaf equivalence;
  the definition module uses that generic equivalence and the existing local completeness predicate.

Sources checked: the current blueprint def-wf-tensor-product; Stacks algebraization.tex
lemma-derived-completion-koszul at line 1091 (0A0E) and the preceding reflector lemma;
sites-cohomology.tex lemma-K-flat-resolution at line 3207 (06YS) and
 definition-derived-tor at line 3300 (06YU). No source statement is changed.

Edge cases: n=0 is allowed and the zero ideal gives identity completion; the unit ideal
has only zero complete objects. A and the ring sheaf may be zero rings, the site may be
empty, p may be zero, nilpotent or a unit, and Hom groups may have p-torsion. The bilinear
base change and raw functor laws use no cancellation or injectivity; S=0 has zero Hom
modules and unique β. k=t=0 and arbitrary k,t are included. The selected derived tensor
is unbounded and no cohomology-flatness or exactness-of-products assumption appears.
No STATEMENT-DISPUTED flag remains.

## New nodes

`def-sf-koszul-small-model-completed-tensor` owns
`Sheaf.CategoryTheory.RingedKoszulSmallModelCompletedTensor`. Its six transport declarations
are `KoszulSmallModel.ring`, `globalSection`, `Modules`, `modulesEquiv`, `derivedEquiv`,
and `complete`; its main declaration is `DerivedCompletedTensor.tensor`.
The first two restrict the coefficient ring and sections along the canonical equivalence;
Modules reuses `ringedSiteModules`; modulesEquiv uses the actual pushforward equivalence
with ring maps from the canonical equivalence unit; derivedEquiv uses its exact derived
transport; complete applies the existing local vanishing predicate on that model.
The final declaration is the actual composite B. No theorem, sorry or reflector choice
occurs in this module. The source and the independent site/coefficient/derived universes
are unchanged. New searches are recorded verbatim from msearch in the new node:
LeanSearch (8 hits, derived categories and ordinary completion), LeanFinder (8 condensed
monoidal hits), and Mathlib grep (0 hits). Direct rg in WeilConjectures, Sheaf and the
upstream name index found scheme-specific constant completion uses only. DAG and whole
blueprint searches found no node owning this canonical transport specialization.
The generic CompletedTensorComparison.tensor was read and its composite reused, so this
node adds the transported completeness specialization rather than a rival tensor notion.

## Repair of immutable head b92b3ac11a59

H13/H2: the reflector dependency node file is removed from this packet. Thus the live
`lem-weil-pbc-ringed-koszul-completion-reflector` record remains byte-identical, with
NJ's `Sheaf.Paper.WeilCompletedTensorReflector` and primary `wfCompletionReflector`.
That module remains owned by its proved node and is imported as the item's proof dependency.
The old `RingedKoszulReflectorSmallModel` module is not delivered. Its `exists_reflector`
theorem is removed, not reattached to any node. Only its real transport definitions survive
in the module owned by the new definition node. The item cites this definition node;
`lem-sf-completed-tensor-rational-naturality` is no longer an added statement dependency.
No item clause or signature changed. The theorem remains the sole postponed theorem.

Validation: both files compiled separately and as their published module names through
scompile.py, with no errors or warnings: the definition module in 5.1 seconds and the
item in 27.4 seconds. The item signature was compared verbatim with lean.statement;
both files have all variables explicitly bound and no line over 100 characters.
The repaired deliver2.py --no-push returned OK: d4cfbb335fb passed server preflight
and compilation; the staged files contain only the item, new definition node, their
two modules and this report.

## Second reading by NF

No second reading by a worker: the dispatch brief requires this worker to deliver directly
without starting agents. The maintainer's independent review reads this delivery.

Self-check of this repair: reread the node, theorem and new definition module. The
site binders retain independent u/v/r, the derived categories retain w/w₀, and the
coefficient action remains the restriction along s. The finite list, generated ideal,
natural unit and universal Hom bijection are identical. The L, T and B linearity
conjuncts, β pure/unique/identity/composition/denominator clauses and actual localized
bifunctor F are all unchanged. The only definitional change to B expands the transparent
CompletedTensorComparison.tensor composite. The new module's actual module equivalence
and exact derived equivalence were retained without changing their data or using a new
choice. Its complete predicate still quantifies through the existing predicate over
all slices and local sections. The empty list, empty site, zero ring/localization and
torsion Hom cases remain admitted. The live reflector JSON is absent from this packet,
and the sole sorry is bilinearity, owned by the item node.
