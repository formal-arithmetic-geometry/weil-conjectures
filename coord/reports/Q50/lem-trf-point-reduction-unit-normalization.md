## Worker report

The module `Sheaf.Paper.PointReductionUnitNormalization` states the canonical, unit-normalized point-section comparison in BOTH coefficient cases. Its main declaration is `WeilConjectures.pointReductionUnitNormalization`. The node statement is unchanged. The new definition node `def-trf-point-reduction-units` supplies the canonical units and exact restriction/sections identification as a separately compiled interface. No dependency repairs are needed. The auxiliary declarations in `Sheaf.Paper.PointReductionUnits` name the actual restrictions, normalized coefficient adjunctions, and identity-on-sections comparison used in the equation. Their owning new definition node does not assert invertibility of the point comparison. Every postponed theorem has the owning blueprint id and its proof in its docstring. All definitions contain actual data.

### Hypotheses and clauses

* `D : FiniteFieldDatum.{u}` supplies the prime `D.p`, the positive finite-field exponent, its finite field, and its algebraic closure `D.k`. The site throughout is `Scheme.ProEt (Spec (.of D.k))` with `ProEt.topology`; it is the small pro-etale site. `[Fact l.Prime]` and `hl : l ≠ D.p` give the second prime and its inequality.
* `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the finite extension. The dependencies use the existing `Padic.coefficientExtensionIntegers`, its maximal ideal, and `Padic.coefficientExtensionRing`. Quotients by maximal-ideal powers are exactly the uniformizer-power quotients, independently of the chosen uniformizer; no additional choice of coefficient ring is made.
* In case (1), `∀ n : ℕ` uses exponent `n+1`, hence exactly all positive reduction levels. `scalarReductionSource` is the completed integral ring sheaf; `scalarReductionTarget` is the constant finite quotient. `pointReductionQuotient` and `scalarReductionDerivedExtension` use their published quotient projection, not a variable ring map. `N : sfIntegralConstructibleCategory l E (Spec (.of D.k))` is exactly the integral derived-complete constructible input category. Its inclusion introduces no resolution or boundedness hypothesis.
* `pointReductionTensorSections` and `pointReductionSectionsTensor` are the two existing integral functors from the reduction theorem. `∃! χ : ... ≅ ...` asserts a natural isomorphism and its unique characterization. The equality of natural transformations uses `whiskerLeft` for the units and canonical sections identification, and `whiskerRight χ.hom Res` for restriction of the comparison. At each object this is exactly `eta_GammaN ≫ Res.map (χ.hom.app N) = Gamma.map eta_N ≫ e.hom.app ...`; equality of natural transformations is pointwise equality. Lean composes in the opposite written order from the TeX function-composition convention. `eta_N` is the unit of the EXISTING tensor-normalized `derivedScalarExtensionRestrictionAdjunction`. `pointUnitIntegralModuleUnit` names the ordinary-module unit from `pointUnitIntegralModuleAdjunction`, normalized on every K-flat representative by `x ↦ 1 ⊗ (1 ⊗ x)` in the existing mixed tensor model. It is not the unit of an arbitrary unspecified adjunction.
* In case (2), `∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)` gives precisely `b=n ≥ a=j ≥ 1`. The ring and sheaf maps are `pointFiniteReductionRingMap` and `pointFiniteReductionSheafMap` from the recorded dependency, hence actual quotients. `(pointFiniteReductionBoundedAbove D.k l E n).FullSubcategory` permits all cohomologically bounded-above inputs, including complexes unbounded below.
* The finite unit equation is likewise equality of natural transformations on the entire bounded-above full subcategory, hence the required equation at every object. The finite natural isomorphism relates the same `pointFiniteReductionSections`, `pointFiniteReductionModuleTensor`, and `pointFiniteReductionSheafTensor` as the finite reduction dependency. `pointUnitFiniteModuleAdjunction` fixes the actual ordinary-module tensor unit on every K-flat representative. `pointUnitFiniteSheafAdjunction` first fixes the ordinary sheaf unit by its sheafified `1 ⊗ x` formula, then fixes the derived unit by the existing universal computation map on flat-term K-flat representatives. These determine the units on all derived objects. `pointUnitFiniteSheafUnit` names the unit of its chosen derived adjunction `.choose_spec.2.choose`; the first chosen witness is its normalized ordinary adjunction. `pointUnitFiniteModuleUnit` likewise names the fixed normalized module unit. `pointUnitIntegralSheafUnit` names the existing integral sheaf unit. These explicit natural-transformation interfaces keep elaboration from repeatedly expanding the existence witnesses; they introduce no arbitrary data.
* In BOTH equations, the exact sections/restriction identification is fixed: `pointUnitIntegralSectionsRestriction` and `pointUnitFiniteSectionsRestriction` uniquely specify the identity on every underlying section element. Their derived comparison is constructed using `Functor.mapDerivedCategoryCompIso` and `Functor.mapDerivedCategoryNatIso`. Thus the right side is sections of the actual sheaf unit under the canonical restriction identity.
* The finite ordinary-module derived localization uses exactly the existing Grothendieck small-Hom-universe instance, while the integral ordinary-module category uses its existing larger localization. The helpers `pointUnitFiniteQ`, `pointUnitFiniteModuleFactors`, and the local instances explicitly retain this distinction; there is no imposed equality of universes or replacement category.

### Dependencies used

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing` and reexported `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionRing`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
* `Sheaf.Paper.PointProEtaleSectionsExact`: `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact`, `pointModuleSections`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: `WeilConjectures.integralConstantToCompletionOfUniverses`, reexported completion/constant coefficient constructions.
* `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructibleCategory`, `sfIntegralConstructible`.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`: `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`; the published specialized tensor functors retain this derived pair.
* `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, including exact restriction and tensor-unit normalization.
* `Sheaf.Paper.PointSectionsDerivedReduction`: `pointReductionQuotient`, `pointReductionModuleTensor`, `pointReductionTensorSections`, `pointReductionSectionsTensor`, and the published coefficient/sections instances. The integral sheaf unit is `derivedScalarExtensionRestrictionAdjunction` from its reexports.
* `Sheaf.Paper.PointSectionsFiniteReduction`: `pointFiniteReductionRingMap`, `pointFiniteReductionSheafMap`, `pointFiniteReductionSheafExtension`, `pointFiniteReductionSheafExistence`, both tensor functors and their universal computation maps, `pointFiniteReductionTensorGenerator`, `pointFiniteReductionSections`, `pointFiniteReductionBoundedAbove`.
* `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`: `HasDerivedCategory.ofIsGrothendieckAbelian`; `Mathlib.Algebra.Category.ModuleCat.AB` supplies the ordinary-module Grothendieck instance.
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategoryCompIso`, `Functor.mapDerivedCategoryNatIso`; the exact-functor API also supplies the localization factorization isomorphisms.

All recorded statement dependencies are public imports. All stated proof dependencies are also imported (non-public when not already statement dependencies), so the imports retain the node's stage-3 proof plan.

### Edge cases

Integral `n=0` means quotient exponent 1, not the zero quotient. Finite levels permit `j=n`, including `n=j=1`: both actual quotient maps are identity and the unit equation still fixes the canonical comparison. Positive-level hypotheses exclude the unintended exponent-zero quotient. Zero input complexes satisfy the same uniquely characterized equation. No flatness of `A_n → A_j` is assumed: for example a proper reduction from length two to length one is covered. Bounded above means cohomologically bounded above, with no lower bound. Integral representatives can be unbounded on either side. The lift `ULift.{u+1,u}` is the published coefficient size convention and does not alter scalars.

### Searches and sources

Read every statement dependency's node record and the full recorded declaration/interface. Read Stacks `sites-cohomology.tex`, Tag 07A6 (`lemma-adjoint`), the cited constant exactness/completion quotient results in `sites-modules.tex`, and the current blueprint integral-model proof clause (4). The two module docstrings and their theorem docstrings preserve the cited source places and the node's ten-step proof, including the unbounded integral cone argument and the finite cyclic-ideal flatness test.

`msearch.py` LeanFinder query "canonical point section coefficient reduction comparison normalized by derived scalar extension unit" returned eight unrelated coefficient-normalization/tactic hits, with no point comparison. The initial Loogle query "DerivedCategory tensor restriction adjunction unit, point sections" was invalid (`Unknown identifier tensor`), and is not counted as a no-match search. The valid Loogle query `ModuleCat.extendRestrictScalarsAdj` returned six ordinary module scalar-adjunction declarations and unit formulas; these do not assert the derived pro-etale point comparison. The msearch grep `pointReductionUnitNormalization|point_sections_derived_reduction|point_sections_finite_reduction` with subdirectory `WeilConjectures` returned no hits. Direct `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf` for the item id, the chosen main declaration, and its finite unit helper returned no existing exact statement. Direct source searches for the point-sections reduction interfaces found the two recorded reduction modules; those give isomorphisms and representative formulas, and this node adds the specified scalar-unit characterization. There is no exact existing declaration to reuse.

No `STATEMENT-DISPUTED` issue or correction to the original node statement is asserted.

## New nodes

`def-trf-point-reduction-units` defines the actual integral and finite quotient scalar-extension units and the canonical identity-on-sections restriction comparison. These are the data named in the original node before its comparison theorem. The existing generic adjunction theorem supplies normalized adjunctions for any universal derived pair; the two published point reduction modules fix tensor functors and computation maps, but do not provide their ordinary-module derived units or their canonical restriction/sections identification. This new node specializes that existing normalized construction to those actual functors. It asserts no point-reduction comparison isomorphism, so the main theorem retains its entire mathematical content. The new definition also permits exponent-zero finite quotients, where the quotient ring is zero; the main theorem uses only the required positive levels. The module provides four explicitly typed unit natural transformations, exact restrictions, the representative normalization statements, and the identity comparison and its exact-localization transport. Choices are taken only from properties that fix the selected units or isomorphisms uniquely. All underlying functors, coefficient rings, quotient maps and tensor models are reused.

Its source is Stacks Tag 07A6 (`lemma-adjoint`) and derived Tags 0FND and 09T5, as used by the current blueprint integral-model proof clause (4). `blueprint_refs.py ancestor` returned `prop-trf-rational-frobenius-integral-model`. A search for definition-node ids matching point plus unit/restriction/scalar found no equivalent definition; `blueprint_refs.py search 'point.*(reduction|restriction).*unit'` returned zero blueprint nodes. Read the relevant point reduction and normalized adjunction sources before constructing the specialized data.

The additional actual searches are logged in `searches.jsonl` and recorded in the new node. LeanSearch query "Canonical restriction and extension of scalars adjunction units for derived module categories and exact global sections at a pro-etale point" returned eight ordinary module extension/restriction/coextension adjunction declarations. LeanFinder query "Restriction of coefficient scalars commutes with point sections by the identity on elements and its canonical derived comparison" returned eight ordinary presheaf/sheaf restriction or unrelated module-section declarations, including `SheafOfModules.restrictScalars_map_val`. The Mathlib grep `point.*(unit|restriction)|derived.*(adjunction|unit)` under `CategoryTheory` returned 25 hits, beginning with pointwise Kan-extension and monoidal unit formulas. None provides these fixed derived point data. Direct `rg` in the upstream `WeilConjectures` tree and shared `lean/Sheaf` for the new declaration names found no existing exact declaration. The old module reduction interfaces were read and reused. Extraction into this separate definition module also keeps each delivered file within the mandated per-file compilation budget.

### Validation

The original report supplied no final compiler log here. Reproduced per-file compiler evidence is recorded in the independent second reading below; no delivery or dry run was invoked during this review.

## Second reading by Q50

Independent maintainer second reading, 2026-10-18, of immutable delivery
f195cf9f720ce46f472185acb6eaa2d8fb7c5747. This reading was performed after delivery;
it is not a claim that a second Q50 worker read the original delivery.

I opened both delivered modules, the item and every statement-dependency node,
the new definition node, their recorded declaration sources, and the source places.
The statement agrees with the node, clause by clause:

- `FiniteFieldDatum D` gives p prime, d=D.a positive and the chosen algebraic closure
  D.k of the finite field of cardinality p^d. `Fact l.Prime` and `hl : l ≠ D.p`
  supply precisely the other prime and its inequality. `Field E`, `Algebra ℚ_[l] E`
  and `FiniteDimensional ℚ_[l] E` give the finite extension. The coefficient objects
  reuse `Padic.coefficientExtensionIntegers`, the chosen uniformizer and its ideal
  powers; no different valuation ring or scalar map is introduced.
- The site in the dependencies is `Scheme.ProEt (Spec (.of D.k))` with
  `ProEt.topology`. Its objects are weakly etale schemes and its covers are the
  pro-etale/fpqc covers. The completed integral coefficient is the limit of finite
  constant coefficient sheaves, not a replacement by a discrete constant integral
  sheaf. `pointIntegralSections` restricts its section action through the canonical
  constant-to-completion map, and `pointFiniteSections` uses the constant-section map.
- Integral n ranges over ℕ and denotes exponent n+1, covering every positive level.
  The domain is exactly the full subcategory `sfIntegralConstructible`: derived
  completeness, constructible reductions, and a common finite cohomological interval
  for the reductions. There is no additional bound on an integral representative.
  `pointReductionTensorSections` and `pointReductionSectionsTensor` reuse both
  published reduction functors and their actual quotient maps.
- Finite n,j and hypotheses `1 ≤ n`, `1 ≤ j`, `j ≤ n` give b≥a≥1. The full
  subcategory `pointFiniteReductionBoundedAbove` is the minus part of the standard
  t-structure, hence cohomologically bounded above, with no lower bound or flatness
  assumption. The ring map is `Ideal.Quotient.factor` with the recorded ULift,
  and the sheaf map is its constant sheafification.
- Each `∃! χ` is over natural isomorphisms between exactly these functors. The left
  side of each equation is the module unit followed by restriction of χ.hom. The
  right side is exact sections of the sheaf unit followed by the fixed derived
  restriction/sections identification. Thus at every N it says precisely
  Res(χ_N)∘η_{ΓN}=Γ(η_N), with the explicitly supplied identification. Naturality is
  part of χ. Pointwise uniqueness follows from the scalar-extension Hom bijection;
  the theorem does not claim equality with an unspecified earlier isomorphism.

I checked the canonical-data helpers in `PointReductionUnits` separately. Actual
restrictions use the existing Mathlib functors. The integral module adjunction is
normalized by the generator `1 ⊗ (1 ⊗ x)` and its fixed universal computation map.
The finite module adjunction has the same normalization. The finite sheaf adjunction
first specifies the ordinary unit on every local tensor generator and then its
localization on flat-term K-flat complexes. The integral sheaf unit reuses
`derivedScalarExtensionRestrictionAdjunction`, whose ordinary and derived unit
formulas I read. Every derived object has such a resolution, so these conditions
fix the units; these choices are not arbitrary maps or hollow existence choices.
The two ordinary section comparisons satisfy the identity-on-every-element
condition and are unique. Their derived versions are actual composites of
`Functor.mapDerivedCategoryCompIso` and `Functor.mapDerivedCategoryNatIso`.
The five helper theorem proofs and the main theorem proof are exactly `sorry`;
all definitions and the two exactness instances contain real terms.

Source checks: Stacks `sites-cohomology.tex` Tag 07A6 (`lemma-adjoint`),
`derived.tex` Tags 0FND (`lemma-pre-derived-adjoint-functors-general`) and 09T5
(`lemma-derived-adjoint-functors`), and `sites-modules.tex` Tags 093J
(`lemma-constant-exact`), 093M (`lemma-completion-flat`), and
`lemma-adjointness-tensor-restrict`. I read current blueprint
`sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
clause (4). The normalized point comparison supplies the needed reduction
compatibility before composition with u. The main docstring includes all ten
proof steps. Steps 1 and 9 identify the actual adjunct; steps 2–8 prove that map
invertible, rather than inferring this from the existence of another isomorphism;
step 10 gives naturality and uniqueness. The unbounded integral cone argument
uses termwise injectivity of the uniformizer power. The finite cyclic-ideal test
uses no injectivity of the quotient scalar map. These are the correct distinctions.

Edge cases checked: integral n=0 is exponent one; finite j=n (including n=j=1);
proper nonflat reduction from length two to one; the zero input; complexes unbounded
below in the finite case and arbitrary representatives in the integral case.
The new definition also covers j=0 and n=j=0, where the quotient ring is zero;
its tensor/restriction and unit formulas remain valid. No empty-index or empty-scheme
case is required by this point statement. The ambient universe is u; site objects
have size u+1 and morphisms size u. Coefficients/modules use u+1. Integral ordinary
modules retain the standard larger localization, and finite ordinary modules retain
`HasDerivedCategory.ofIsGrothendieckAbelian.{u+1}`. No equality of site universes,
new Abelian structure, or replacement of the small pro-etale site is imposed.

Independent searches: LeanSearch query “Derived global sections and scalar extension
at an algebraically closed pro-etale point with normalized adjunction units” returned
eight results (Gamma/Spec, skyscraper and coextension adjunctions), none matching.
LeanFinder query “Derived sections commute with coefficient reduction and the
comparison is the transpose of the tensor adjunction unit” returned eight unrelated
Kaehler/unramified results. Loogle `ModuleCat.extendRestrictScalarsAdj` returned six
ordinary scalar-adjunction declarations; I read the adjunction and unit formulas in
Mathlib `ChangeOfRings.lean`, lines 885–921. Direct rg searches in Mathlib,
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the group clone's
`lean/Sheaf` and `lean/WeilConjectures` found related reduction/pullback interfaces,
but no existing statement for this point comparison and these fixed functors.
The existing generic adjunction and exact-localization interfaces are reused.
I also read `coord/pefw-upstream-framework.md`; no condensed/module-object
substitute is introduced by this delivery.

Records and conventions: the new definition has the required fields, empty proof
and proof_deps, its owning module, source, ancestor/via, three search kinds and
statement dependencies. The item cites it. Both delivered `lean.statement` strings
are verbatim the full signatures before `:=`; every declaration is recorded.
Both module docstrings and all declaration docstrings carry source and owning
blueprint identifiers. No delivered line exceeds 100 characters. No statement
correction or dependency repair is needed, so no §1(C) citer audit is applicable.

Finding repaired in this replacement report: H1/H11, the original second-reading
section explicitly said that no reading had occurred. Its validation section also
contained no actual compile result. I preserve the Worker report and supply this
substantive independent reading and the reproduced compiler evidence. The Lean
modules and both node records require no changes.

### Reproduced per-file compilation

On 2026-10-18 I ran:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q50 lem-trf-point-reduction-unit-normalization snapshot/lean/Sheaf/Paper/PointReductionUnits.lean snapshot/lean/Sheaf/Paper/PointReductionUnitNormalization.lean
```

Exit status 0, no errors or warnings. The installed wrapper reports server-side
private-overlay compilation rather than the older local-overlay implementation.
It compiled the files separately in dependency order, using the supplied immutable
texts and private artifacts, with the 60-second per-invocation limit. Reported times:
private helper overlay 30.2 s; helper preliminary 22.9 s; helper sandbox 23.6 s;
helper library 30.7 s; main sandbox 28.7 s; main library 28.5 s. The artifact directory
was `/dev/shm/nt-tmp/nt-local-compile-swx801g6/.lbuild`.

No global build, direct SSH command, delivery, merge, Git mutation or live Lean write
was performed. The immutable snapshot and branch head were not changed.
