## Worker report

Item: `lem-sfb-ringed-equivalence-resolving-tensor-descent`; group Q12, stage 2.

The delivery states the resolving-localization and coherent ordinary unbounded
K-flat tensor transfer across the specified additive symmetric monoidal equivalence.
Its main theorem has `sorry` as its proof; its docstring gives the complete ten-step
natural-language proof, with the DAG proof dependencies. All other declarations
are real constructions or predicates spelling out clauses of this same node.
No resolutions are selected, functorially or otherwise.

### Hypotheses and notation

| Node text | Lean rendering |
| --- | --- |
| Site small relative to coefficient universe | `C : Type c`, `Category.{v} C`, `J : GrothendieckTopology C`, `EssentiallySmall.{r} C` |
| Commutative ring sheaf R | `R : Sheaf J CommRingCat.{r}` |
| M = Mod(R), with the sheaf tensor | `Modules R`, a transparent abbreviation for recorded `ringedSiteModules` of the ring sheaf obtained by `sheafCompose` and `forget₂`; the imported independent-coefficient canonical sheaf tensor |
| A abelian and symmetric monoidal, including symmetry involution and hexagon | `Category.{b} A`, `Abelian A`, `MonoidalCategory A`, `SymmetricCategory A`; the latter extends Mathlib's braiding with its naturality, hexagon and involution |
| Tensor additive in both variables | `MonoidalPreadditive A` |
| Countable coproducts | `HasCountableCoproducts A` |
| Tensor preserves those coproducts in both variables | `leftCountable` and `rightCountable`, quantified over every countable `I : Type` and every `X : A`, with `PreservesColimitsOfShape (Discrete I)` for `tensorLeft X` and `tensorRight X` |
| Ordinary unbounded homotopy and derived categories | `HomotopyCategory _ (.up ℤ)`, `DerivedCategory _`, `Q`, `Qh`, with independently bound `HasDerivedCategory.{wR}` and `HasDerivedCategory.{wA}` |
| Signed direct-sum total tensor | The existing `HomologicalComplex.monoidalCategory _ (.up ℤ)` and the native braiding imported from `HomotopyCategory.Braided`; the countable instances only supply its existing graded sum hypotheses |
| Flat = tensor exact | Target flatness is `exactFunctor A A (tensorRight M)`; source flatness is the recorded `SheafOfModules.IsFlatOnSite` |
| K-flat and the two-sided quasi-isomorphism test | Source `CochainComplex.IsKFlatIndependentCoefficients`; target `CochainComplex.IsKFlatForTotalTensor`, the recorded two-sided test (equivalent to acyclic-tensor flatness here) |
| F and G additive exact quasi-inverse equivalences | `e : Modules R ≌ A`, `e.functor.Additive`, `e.inverse.Additive`. An additive equivalence of abelian categories is exact; the existing derived-equivalence API supplies these exactness instances, so no stronger separate resolution hypothesis is imposed |
| Coherent ordinary strong monoidal symmetric comparisons | `e.functor.Braided`, `e.inverse.Braided`, with `NatTrans.IsMonoidal e.unitIso.hom` and `NatTrans.IsMonoidal e.counitIso.hom`; `Braided` includes the strong monoidal structure |
| Specified coherent signed-total comparisons and inverse for G | `tc` and `gc : _.CoreMonoidal`, with inverse tensorators `tc.μIso.inv` and `gc.μIso.inv`; `InverseTotalComparisons` writes all four monoidality equations for the termwise unit and counit (tensor and unit for each), using exactly these specified structures |
| Total comparisons use the ordinary units and signed symmetry | `hUnitF`, `hUnitG` identify their units with `mapCochainComplexεIso`; `hSymF`, `hSymG` write the native symmetry squares explicitly |
| Preservation and reflection of flat objects | `hFlatF` and `hFlatG`, both biconditionals |
| Preservation and reflection of K-flat complexes | `hKFlatF` and `hKFlatG`, both biconditionals on every unbounded complex |
| Fixed ringed derived tensor with model maps | The source derived monoidal and symmetric structures and `mR : TensorModel` specify the ordinary K-flat model maps, their naturality, localized unit, associativity, both unitors, and native symmetry. This presentation is invariant under replacing the tensor by a coherently isomorphic ordinary K-flat presentation |
| P_R and P_A | `resolvingRinged R` and `resolvingTarget A`, full-subcategory object predicates: K-flat and every integer-indexed term flat |
| W_R, W_A | `HomotopyCategory.quasiIso _ (.up ℤ)` restricted by `.inverseImage` along the resolving full-subcategory inclusion |

The site object, site morphism, coefficient, target object, target morphism, and
two derived hom universes are independent (`c v r a b wR wA`). No equality of
universes or closedness, Grothendieck, all-small-coproduct, boundedness, or
functorial-resolution hypothesis is added. `I : Type` represents countable sums:
every countable indexing set in another universe is equivalent to a small
countable set. Only countably indexed degree diagonals are used by native totals.

### Conclusions, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| Termwise unit and counit induce mutually inverse D(F), D(G) | `derivedEquivalence e := e.mapDerivedCategory`. This is the actual existing equivalence, with functor `e.functor.mapDerivedCategory`, inverse `e.inverse.mapDerivedCategory`, and localized termwise unit/counit. It is constructed as data rather than restated as a mere nonempty equivalence |
| Resolving localization on A is equivalent to D(A) | First conjunct of the main theorem: a functor from the actual restricted-quasi-isomorphism `.Localization`, `L.IsEquivalence`, and a natural isomorphism between localization followed by L and resolving inclusion followed by `Qh` |
| Ordinary K-flat derived tensor on A with canonical model maps | Existential target `dA`, `sA`, and `mA : TensorModel` inside `TransferSpec`; every pair of target K-flat complexes has a natural model isomorphism and the native associator, unitors and symmetry equations |
| Natural isomorphism t | `TensorComparison e` is an isomorphism of the two tensor bifunctors; `comparisonOfCore e s` is the inverse of the canonical natural tensorator of the existential `CoreMonoidal` structure on D(F) |
| Specified normalization formula | `NormalizationEquation` is literally `DF.map(mR.pair).hom ≫ t.hom ≫ (κP ⊗ₘ κQ) = κ(P⊗Q) ≫ Q.map(tc.μIso.inv) ≫ mA.pair.hom`; `mapDerivedCategoryFactors` is the actual exact-functor κ |
| Uniquely determined on flat-term K-flat pairs | `ResolvingNormalization` quantifies precisely such pairs. The last conjunct of `ComparisonSpec` quantifies over **all** natural isomorphisms `t' : TensorComparison e` satisfying this normalization, and equates each to t. It does not assume t' is already coherent monoidal |
| Associator and both unitors | The existential derived `CoreMonoidal` structure includes its associativity, left-unit and right-unit coherence equations |
| Localized ordinary unit comparison | `unitComparison` is the explicit composite of DF applied to the source model-unit inverse, κ at the ordinary unit complex, Q of the specified total-unit inverse, and the target model-unit map; `ComparisonSpec` fixes `s.εIso` to its inverse |
| Native Koszul symmetry | `ComparisonSpec` includes the explicit D(F) braiding square. `TensorModel.symmetry` identifies each model braiding with the existing signed complex braiding, with no sign replacement |
| Formula for every K-flat pair, without flat terms | The normalization conjunct of `ComparisonSpec` quantifies over all source K-flat complexes, with no term-flatness hypotheses; source and target `TensorModel.pair` are defined on all K-flat pairs |
| Agreement with any independently specified ordinary K-flat tensor carrying the model maps | `ModelAgreement` universally quantifies over another target derived monoidal/symmetric structure and its `TensorModel`. It supplies the coherent identity comparison j, fixed by old-model inverse followed by new-model map (and by the model units), respects the two symmetries, and states that every independently normalized t' equals t followed by j |
| No functorial resolutions | No resolution functor or chosen objectwise resolution occurs in the statement or its definitions |

`TensorModel`, `ComparisonSpec`, `TransferSpec`, and the related helpers package
the structure, model equations and comparison clauses of this very node; they
are not alternative definitions of the sheaf category, K-flatness, localization,
total tensor or derived category. `countableCochainMonoidal` calls Mathlib's real
native construction, with real countable sum and zero-object preservation data.
The local `letI` bindings inside helper **definitions** distinguish two structures
on the same derived category; the theorem has no opaque `let` hypothesis.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`,
  with the equivalent `GrothendieckTopology` presentation used by the recorded
  module-sheaf declarations. The size-convention node supplies independent universes.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: canonical
  independent-coefficient module tensor, symmetry, preadditivity and colimit instances.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor` and the native binary total-tensor test.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and
  `SiteDerivedTensorDescentSpec` (including its localization, representative
  comparisons and fully faithful natural-transformation extension clauses).
- Mathlib: `Abelian`, `MonoidalCategory`, `SymmetricCategory`, `Functor.CoreMonoidal`,
  `Functor.Braided`, `NatTrans.IsMonoidal`, `DerivedCategory.Q`, `DerivedCategory.Qh`,
  `HomotopyCategory.quasiIso`, `MorphismProperty.Localization` and the full-subcategory
  inclusion. These are the recorded Mathlib matches; they do not need lean records.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Equivalence.mapDerivedCategory`, `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryFactors` and the localized natural-isomorphism construction.
- `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`:
  `Functor.mapCochainComplexεIso` (and the existing total comparison API).
- `WeilConjectures.Algebra.Homology.HomotopyCategory.Braided`: native complex
  monoidal/symmetry instances.

Proof dependencies are imported as proof imports where they are not also statement
inputs: `Localization.Predicate` (`lift`, `liftNatIso`, `natTrans_ext`),
`Localization.Pi` (`Functor.IsLocalization.pi`), `Monoidal.Braided.Transport`
(`Monoidal.Transported.instSymmetricCategory`),
`Sheaf.Algebra.Homology.RingedDerivedTensorNative` (native model constraint squares),
and `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
(`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`). The existing
native-ringed theorem is a proof dependency, not a reason to equate the site's
object/morphism universes or to restrict the coefficient universe.

### Edge cases checked before stating

- Unbounded complexes: every degree is in ℤ, with no boundedness assumption.
- Empty sums/zero objects: the countable family includes the empty set; additive
  tensor preserves zero objects, supplying the native total unit's empty-sum conditions.
- The zero complex, zero module category and zero commutative coefficient ring
  are allowed; no nonzero or nontriviality hypothesis occurs.
- The unit complex is covered separately by `kflat_unit`, and both unit equations
  use its actual localized model map.
- K-flat complexes with nonflat terms are retained by the general normalization
  clause; only the uniqueness testing subcategory imposes flat terms.
- An arbitrary natural comparison is included in uniqueness; the statement does
  not restrict this to already strong monoidal competitors.
- Different target derived tensor presentations are not silently identified:
  `ModelAgreement` keeps the two monoidal structures explicit and compares them
  through the actual identity functor and canonical model arrows.
- Identity equivalence and either coefficient/target universe larger than the
  other are admitted; the existing exact-derived-equivalence API has independent
  derived hom universes.

### Searches

- `msearch.py Q12 <item> leanfinder "An exact symmetric monoidal equivalence transports the flat term K flat resolving localization and the normalized unbounded derived tensor comparison"`:
  eight results concerning Tor, flatness and localizers; none states this transfer.
- `msearch.py Q12 <item> loogle '"mapDerivedCategory", "Monoidal"'`:
  no results.
- `msearch.py Q12 <item> grep 'mapDerivedCategory.*[Mm]onoidal|[Rr]esolving.*[Ee]quivalence' CategoryTheory`:
  no results.
- `rg -n` in `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf` for the full namespace and theorem name found no name collision.
- `rg -n` for this node id and `RingedEquivalenceResolving` in both
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration of this statement.
- Broader project searches found `ExactTensorNormalization`; its full statement
  assumes additional Grothendieck/closed/resolution machinery and takes an existing
  derived comparison as input, so it is not this existence/localization/coherence
  theorem. `RingIsomorphismTensorTransport` specializes to ring isomorphisms, not
  arbitrary exactly equivalent target coefficient categories.
- Read the recorded declaration signatures and docstrings and the source Tag 0G7D
  (`sites-cohomology.tex`, lemma-factor-through-K-flat), together with the native
  tensor, exact-derived-equivalence and symmetric transport APIs.

`ringedLeftCountable` and `ringedRightCountable` name the existing source
countable-preservation instances. `ringedCochainMonoidal` supplies those arguments
to the same native construction explicitly. These helpers avoid repeated universe
and higher-order instance inference; they do not introduce a second tensor.

No statement correction, disputed statement, unusable dependency interface or new
independent definition node is needed. The previous worker's stage-1 live-wins
message does not bar this stage-2 assignment: the accepted live node has no Lean
record, as clarified by the current standing brief's stage handoff.

### Validation

All compiler invocations use the prescribed `scompile.py` wrapper. The final module compiled cleanly as both `Sheaf.Stage2.Sandbox0` and
`Sheaf.Algebra.Homology.RingedEquivalenceResolvingTensorDescent` (28.5 seconds
each; exit 0). There were no warnings, errors or diagnostic commands in the
delivered module. Only the main theorem contains `sorry`.

The required `deliver2.py Q12 <item> --no-push` passed: `OK (dry run)`
for commit `6558e557175`, with server preflight and per-file compilation successful.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
