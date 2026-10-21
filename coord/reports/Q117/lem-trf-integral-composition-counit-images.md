## Worker report

The module `Sheaf.Paper.IntegralCompositionCounitImages` states
`WeilConjectures.integralCompositionCounitImages`, with proof `sorry`. It asserts
both displayed counit-image identities as equalities in the derived category of
whole strict completed-module towers. All auxiliary definitions contain real data.
No node statement, dependency list, proof plan or other metadata was changed.

The source is the current main-20261015 blueprint,
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`,
Step 1, Global powers, read in full. This node's five-step calculation is
agent-written, as its source record explicitly says; Tag 0941 supplies the
normalization background. The theorem docstring reproduces those five steps.

The presentation binders expand the node's instruction to choose the actual
quotient tower of its resolution. They do not assume either asserted identity,
equality of a and b, reduction detection, or arbitrary comparison maps.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A prime ell and finite extension E/Q_ell | `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. |
| Integers, chosen uniformizer, positive quotients, and completion | The recorded `Padic.coefficientExtensionRing`, `unrestrictedIntegralFiniteComplex`, and `integralTowerModules` constructions, inherited without redefining any coefficient. Index `n` means positive exponent `n+1`. |
| Schemes Z -> W -> V and isomorphisms h,k | `{V W Z : Scheme.{u}}`, `h`, `k`, `[IsIso h]`, `[IsIso k]`; composite `h ≫ k`. |
| Ell invertible on all three schemes | `hV`, `hW`, `hZ` assert that ell is a unit in every stalk, the exact hypotheses of the recorded comparison. |
| Small pro-etale sites and completed-module derived categories | `Scheme.ProEt`, `integralTowerModules`, `DerivedCategory`. The site retains objects in universe `u+1` and morphisms in `u`; no equality of these two universes is imposed. The coefficient size is `u+1`, as in the recorded normalized comparison system. |
| N in D^b_c(V,O_E) | `K` is a cochain representative of N and `hK : sfIntegralConstructible l E V (DerivedCategory.Q.obj K)` imposes precisely derived completeness, constructible reductions and their common finite amplitude. `⟨DerivedCategory.Q.obj K, hK⟩` is the full-subcategory object used by eta. No boundedness of the representative K or P is imposed. Every derived object has such a representative. |
| Chosen flat-term K-flat resolution q:P->N | `P : (integralOperationsGoodComplex l E V).FullSubcategory`, `q : P.obj ⟶ K`, `[QuasiIso q]`. Both kappa_k and kappa_kh use `inverseImagePullbackComparison ... K P q`, hence exactly this same resolution, rather than an unrelated chosen representative. |
| Actual quotient complexes P_m and their quotient transitions | `C`, `e`, `κ`, `hC`. The recorded `CoefficientReductionPresentation` identifies each evaluation of C with the ordinary quotient complex and requires every horizontal transition to be the ordinary quotient map. Its first clause normalizes e against the recorded derived-reduction counit. These are strict presentations, rather than independently selected finite-level isomorphisms. |
| C_g = Res g* P_m | `integralCounitImagesTower l E g C`: ordinary whole-sequence pullback applied to C, followed termwise by completed coefficient restriction. |
| The strict maps theta_g with components reduced x tensor 1 | `θk`, `θkh` are morphisms of complexes of entire towers; `hθk`, `hθkh` use `IntegralCounitImagesTheta`. That predicate fixes the value on EVERY section: ordinary quotient tensor unit, inverse κ to the simultaneous quotient presentation, sequence-pullback adjunction generator, comma-arrow restriction, and the actual completed restriction. It contains no asserted derived equality. Thus the maps are canonically prescribed, not free arrows or existentially chosen natural isomorphisms. |
| Transported completed module action | `inverseImageIntegralModules` and its exact localization `inverseImageIntegralDerived`, using `inverseImageCompletedCoefficientMap`; no discrete constant O_E is substituted. |
| Constant-tower functor Delta | `Functor.const ℕᵒᵖ` termwise and its exact localization `integralComparisonConstantTower`. |
| M=Lk*N and D=h*C_k | M is `(integralDerivedPullback l E k).obj (DerivedCategory.Q.obj K)`; D is `integralCounitImagesDoubleTower l E h k C`, retaining both finite pullbacks and all transitions. |
| X=h^-1 k^-1 N | The source of both equalities is `integralComparisonConstantTower` applied to the double exact inverse image of `DerivedCategory.Q.obj K`. |
| Canonical inverse-image compositors d_P,d_N | The natural isomorphism d is specified on every module and every section by `hd`, the canonical restriction along `Over.mapComp`. `mapDerivedCategoryCompIso` followed by `mapDerivedCategoryNatIso d` is its exact localization, evaluated at P or K. This section characterization determines the specified linear compositor, not a freely varying comparison. It avoids importing the downstream composition theorem. |
| Strict finite pullback compositor c | The first right side ends in `DerivedCategory.Q.map` of `NatTrans.mapHomologicalComplex (integralComparisonSequenceComposition ...).hom`, followed termwise by scalar restriction. This is the actual strict compositor on C, including its quotient transitions. |
| Strict unit u_(h,C_k) | The second right side ends in `DerivedCategory.Q.map` of the termwise `integralTowerInverseImageUnit` at the strict complex k*C. The preceding exact-derived factor identifies its source with H_tow(Q C_k). |
| Exactly the normalized eta and c^E | Eta is `integralResolutionMatchingEta`, an evaluation of `integralComparisonEta` with the equivalent stalk-unit convention. In the first left side, `c^E ≫ eta` is expanded by the definition `integralComparisonComposition`: the recorded pullback realization followed by total limit of the actual system compositor. It is not an assumed equation for arbitrary eta. |
| Normalized total derived limit and whole-tower counit | `coefficientConstantTowerLimit` and `integralComparisonTowerCounit`, the existing derived diagonal/limit adjunction. Its recorded `integralComparisonTowerCounit_computes` identifies its value on K-injective towers with the ordinary cone. `D.coefficient E` contains the specified `IntegralComparisonRoosModel` and normalized pullback models. |
| Transport back to the actual quotient tower | `integralCounitImagesResolutionPresentation` is exactly inverse reduction of Q(q), followed by e. `integralCounitImagesDoublePresentation` uses only functorial images of this iso and the canonical `mapDerivedCategoryFactors` at k*, h*, and scalar restriction. Applying total limit to this iso transports eta to Rlim of the actual D. This makes the target literally `DerivedCategory.Q.obj (integralCounitImagesDoubleTower ... C)`. |
| First displayed formula | The first conjunct is Delta(a) followed by epsilon_D, equal to Delta([HG(q)]^-1), Delta(d_P), the localized strict theta_kh, and the localized strict finite compositor. Lean's `≫` reads left to right, the reverse order from the node's `∘`. |
| Second displayed formula | The second conjunct is Delta(b) followed by epsilon_D, equal to the SAME Delta([HG(q)]^-1), the canonical Delta/H commutation, H_tow of strict theta_k, and the localized strict tensor unit. |
| No equality a=b or faithfulness claim | The conclusion is exactly the conjunction of those two equations. All maps have their whole-tower target; there is no derived evaluation of the conclusion. |

Dependencies were read at their recorded signatures and source docstrings. The
module imports the recorded statement dependencies explicitly. The constructions used are:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported coefficient constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  the existing completed coefficient sheaf, quotient projections and coefficient sizes.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full subcategory.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` and
  `KFlatResolutionIndependentCoefficients`: the existing K-flat predicate and resolution
  interface, underlying `integralOperationsGoodComplex`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and its public dependencies:
  `integralDerivedPullback`, `unrestrictedIntegralFiniteComplex`,
  `integralOperationsGoodComplex` and the actual quotient constructions.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `inverseImageIntegralModules`, `inverseImageIntegralDerived`,
  `inverseImagePullbackComparison`, `inverseImagePullbackComparisonDerived`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: the existing inverse-sequence convention.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the pro-etale inverse-image framework;
  its specified sectionwise isomorphism model is used through the comparison module.
- `Sheaf.Paper.IntegralFinitePullbackComposition` and the imported
  `IntegralComparisonSequenceSystems`: `integralComparisonSequencePullback`,
  `integralComparisonSequenceComposition`, `integralComparisonSystemComposition`.
- `Sheaf.Paper.IntegralTowerInverseImageUnit`: `integralTowerInverseImageUnit`,
  `integralDerivedTowerInverseImage`, `integralTowerInverseImageDiagonal`.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, its normalized pullback realization and `integralComparisonEta`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  the existing total-limit/K-injective convention, used by the existing
  `integralComparisonTowerCounit` in `IntegralComparisonRealizationModels`.
- Proof imports: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition` and
  `Sheaf.Paper.IntegralPullbackResolutionMatching`; the latter also supplies the
  statement-level stalk-unit wrapper `integralResolutionMatchingEta`.
  `lem-trf-integral-comparison-counit-characterization` currently has no recorded
  Lean module, so there is no module to import for that proof dependency.
  The convention node `def-weil-scheme-morphism-properties` fixes no declaration.

Searches actually run with msearch.py under Q117 and this item:

- LeanFinder: “The two completed integral pullback comparison composites have whole
  strict tower counit images with the same inverted K-flat resolution denominator”.
  Eight hits: ordinary `PresheafOfModules.pullbackComp`, `SheafOfModules.pullbackComp`,
  right-derived comparison fac lemmas, finite pullback unit and conjugacy lemmas.
  None asserts these completed integral whole-tower equations.
- Loogle: `SheafOfModules.pullbackComp, CategoryTheory.Functor.mapDerivedCategoryCompIso`.
  The service returned OK, zero hits for this combined query.
- Mathlib grep: `constLimAdj|pullbackComp`, subdirectory `CategoryTheory`.
  Twenty-five hits (ordinary localization/limit adjunction and ordinary categorical
  pullback composition); none is the requested integral formula.
- LeanSearch: “Whole strict tower counit images of completed integral pullback
  comparisons under composition, with common inverse K-flat resolution denominator”.
  Eight hits including `Functor.totalLeftDerivedCounit`, abelian coimage comparison,
  condensed counits and generic completion identities; no exact match.
- `rg` over `lean/Sheaf`, `lean/WeilConjectures` and `dag/lean_names_upstream.json`
  for the item id, `integralCompositionCounitImages`, `integralCounitImages`,
  `IntegralCounitImagesTheta`, counit/whole-tower/composition patterns; upstream
  `grep -rn` for the item id. No existing statement or conflicting proposed name.
  Related project modules found and read: `IntegralPullbackResolutionMatching`,
  `IntegralTowerInverseImageUnit`, `IntegralPullbackComparisonRealization` and
  `IntegralInverseImageComparisonComposition`. The last contains the downstream
  equality a=b, not this node's formulas. Its canonical compositor characterization
  was read, but that module is NOT imported: this avoids a downstream import cycle.
- Additional upstream `rg` for `inverseImage.*[Cc]omparison|integral.*[Cc]ounit|completed.*[Pp]ullback`
  found other completed exchanges and stalk comparisons, not these two identities.

Edge cases checked: empty schemes (the section conditions become vacuous exactly
where the sheaves are terminal/zero, without excluding the case), N=0, identity h
or k, exponent one, unbounded K-flat representatives, and arbitrary common universe u.
Neither finite Tor amplitude nor nonzero N nor nonempty underlying schemes is
assumed. The two different site universes remain those of the recorded small site.

Validation: `scompile.py Q117 lem-trf-integral-composition-counit-images <module>`
compiled the module against the live published library; both sandbox and actual
module-name modes were clean. The sole theorem remains `sorry`, as required.
The final dry run and delivery results are recorded below after packaging.

## Second reading by Q117

A second author pass read the node, its five proof steps, the source Global powers
paragraph, and the entire final Lean module side by side. No separate worker was
started, in accordance with the dispatcher brief; the maintainer supplies the
independent review.

This pass matched every hypothesis and clause using the table above. It checked
that `hC` imposes all quotient transitions, that the theta condition is on all
sections of a strict tower morphism, and that `hd` fixes the canonical compositor
without assuming the desired formula. Kappa_k and kappa_kh use the same q. The
second kappa, at M, uses the recorded arbitrary-derived-object comparison. Both
right sides start with exactly the same functorial image of inverse HG(Q(q)).
Both targets are Q of the actual iterated finite-pullback tower; both left sides
use its whole-tower counit. The first left side unfolds c^E followed by eta, and
the second uses the existing normalized eta directly.

One clarity improvement was made during this pass: the final maps on both right
sides are now explicitly localizations of the ordinary strict finite compositor
and the ordinary strict tensor unit. Earlier equivalent conjugated presentations
were removed. This makes their exact correspondence to c_bullet and u_(h,C_k)
visible and eliminates an unused helper. No hypothesis or conclusion was changed.
No statement correction, dependency repair or new independent definition node is needed.

Packaging check: `deliver2.py Q117 lem-trf-integral-composition-counit-images
--no-push` returned `OK (dry run)` for commit `2e165f1dd71`: server preflight
passed and the final file compiled. The delivered files are exactly the module,
the item's lean-only node update, and this report.
