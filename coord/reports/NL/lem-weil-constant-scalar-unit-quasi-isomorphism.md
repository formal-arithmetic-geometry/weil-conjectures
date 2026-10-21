## Worker report

`Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism` states
`WeilConjectures.ConstantScalarUnitQuasiIsomorphism.regular_scalar_unit_quasi_isomorphism`.
Its proof is `sorry`; there are no proved theorems or hollow definitions in the delivery.
The helper abbreviations name the already recorded scalar tower and its actual termwise
product, and the two helper maps compose the existing strict first projection with eta
and the existing product projections. No tensor, coefficient, completion or derived-limit
construction is replaced.

Hypotheses and objects, clause by clause:

* The finite-field tuple is `(D : FiniteFieldDatum.{d})`. The prime and characteristic
  condition are `[Fact l.Prime]` and `(_hl : l ≠ D.p)`.
* Finite coefficient extensions are `(E L : Type u)`, their `Field`, `Algebra (Padic l)`
  and `FiniteDimensional (Padic l)` instances, and `(ι : E →ₐ[Padic l] L)`.
  A field algebra embedding is automatically injective. The existing coefficient
  construction chooses a uniformizer and uses its actual ideal-power quotients.
* `(Y : Scheme.{t})` has no geometric or finiteness assumption. The dependency uses
  its actual `Y.ProEt` site, object universe t+1, morphism universe t, and module size
  max u (t+1). The datum universe d is independent of both.
* `regularComplex l E Y` is R_E[0], not a constant discrete O_E sheaf.
  The recorded `integralScalarTowerFunctor` supplies T_n, its reduction transitions,
  and restrictions along the target completed-ring projections. Our `tower` merely
  specializes it to that regular source. Natural number n always means exponent n+1.
* `product` is the actual categorical product of complexes, computed termwise;
  `boundary` from the strict-unit dependency is its actual one-minus-shift.
  `integralScalarComplexFunctor` is its strict mapping cocone, including the signs.
* Eta is bound with exactly `quotientCoordinates ∧ zeroSecondComponent`.
  The first condition quantifies over every level, site object and section s and
  prescribes 1 tensor pi_n(s); the second kills every graded shifted component.
  `regular_scalar_strict_unit` proves there is exactly one such map, so binding eta
  this way is the node's 'Let eta be the uniquely normalized map', not an arbitrary
  comparison map or an extra mathematical assumption.

Conclusions, in the order of the Lean conjunction:

1. `∀ n, Finite (Padic.coefficientExtensionRing l L (n+1))` is finiteness of all
   positive-level target quotient rings.
2. `∀ n, Epi (integralCoefficientSheafTransition l L Y n)` asserts the actual constant
   ring-sheaf reductions are epimorphic.
3. `∃ e : regularComplex l L Y ≅ limit (tower ...), ...` identifies the ordinary
   limit as a module complex, with `e.hom ≫ limit.π ... = leg ... eta n`.
   Each leg is eta followed by fst and pr_n, so the normalization makes it exactly
   u_n inverse composed with pi_n. The multiplication maps and inverse tensor
   formulas are those already fixed by `finiteMultiplication` in the dependency.
4. `QuasiIso eta` is the assertion for the specified chain map before localization.
5. `Nonempty (IsLimit (Fan.mk (Q.obj product) (fun n => Q.map (Pi.π ... n))))`
   says that this actual termwise product represents the derived product with its
   given projections, without assuming derived products exist.
6. `∃ δ, Triangle.mk (Q.map (inclusion ... eta)) (Q.map boundary) δ ∈ distTriang ...`
   is exactly the stated distinguished triangle. Together with clause 5 it is the
   Roos triangle of `CategoryTheory.IsDerivedLimitTriangle`, expressed on this
   specified product object rather than introducing an unrelated chosen product.
7. The existential isomorphism from `Q.obj` of the strict scalar cone to R_L[0]
   has inverse **equal** to `Q.map eta`. Its further equation
   `e.hom ≫ Q.map (leg ... eta n) = Q.map (fst ≫ pr_n)` is precisely compatibility
   of the inverse identification with every quotient projection. The strict cone
   is the existing integral-scalar representative on the regular K-flat source.
8. `IntegralOnSlice.IsComplete l E Y none (Q.obj (regularComplex l E Y))` is exactly
   canonical derived completeness of R_E[0]. The global `none` branch unfolds to
   the recorded `IsDerivedCompleteUnrestricted`, whose condition uses the actual
   augmented reduction tower. In the identity extension, `reductionUnits` in the
   dependency equates its units with the prescribed quotient legs, so clause 6 has
   precisely the required first map. Completeness is not substituted for this
   normalized triangle: both are stated.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  module: `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public completed
  coefficient modules: `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`, `integralCoefficientSheaf`,
  `integralCoefficientSheafTransition`.
* `Sheaf.Paper.IntegralScalarExtensionUniverses` and the publicly retained strict
  construction: `integralScalarExtensionOfUniverses`,
  `integralScalarTowerFunctor`, `integralScalarComplexFunctor`,
  `integralScalarFiniteComplex`, `integralScalarTensorSection`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing sheafified tensor.
* `Sheaf.Paper.ConstantScalarStrictUnit`: `regularComplex`, `boundary`,
  `quotientCoordinates`, `zeroSecondComponent`, `finiteMultiplication`,
  `finiteDerivedComputation`, `reductionUnits`, `regular_scalar_strict_unit`.
* `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle` and `CategoryTheory.IsDerivedLimit`.
* `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`; `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `DerivedCategory.Q`, `QuasiIso`.

The modules of all already recorded proof dependencies are imported as ordinary imports:
DVR arithmetic, finite DVR quotients, constant sheaves and underlying-set sheafification,
local sheafification sections, sectionwise module limits, the pro-etale surjective-tower
theorem and the degreewise-epi kernel/cocone theorem. The proof docstring follows the
node's eight steps, including the strict uniqueness argument and the inverse projection
equation. The cited Bhatt--Scholze PDF was read locally; its replete-topos statements
provide the surjective-tower input, while the strict tensor coordinates are the explicit
agent-written refinement already identified by the node.

Edge cases checked before writing: n=0 is exponent one, never the zero quotient level;
E=L and ι the identity are admitted with no nontriviality requirement; ramified extensions
have no restriction on ramification; disconnected Y and the empty scheme are admitted.
For the empty scheme every module and comparison is zero, so the zero source/target
maps are still quasi-isomorphisms and all triangle and projection clauses make sense.
No connectedness, finite type, quasi-compactness or cohomological boundedness is assumed.
The zero section ring (1=0) is covered by full-section normalization.

Searches for an existing statement:

* `msearch.py leanfinder`, query 'The normalized scalar extension unit of the regular
  completed coefficient sheaf on the pro-etale site is a quasi-isomorphism and yields
  a Roos triangle': 8 hits, including representation resolutions and generic mapping
  cones; no exact statement.
* `msearch.py loogle`, query `QuasiIso, CochainComplex`: 12 hits including
  `DerivedCategory.isIso_Q_map_iff_quasiIso`, shifts and resolutions. These supply
  localization infrastructure, not this coefficient tower and normalized triangle.
* `msearch.py grep`, query `constantCoefficientScalarUnit|scalar.*unit.*quasi|Roos`:
  zero Mathlib hits.
* `rg` of `lean/WeilConjectures` for the exact node id: no match; searches for scalar
  units found unrelated scheme-module comparisons, not this normalized pro-etale tower.
* `rg` of `lean/Sheaf` for `regular_scalar_strict_unit` and
  `constantCoefficientScalarUnit_isIso` initially found the strict-unit dependency and
  the old parent `ConstantCoefficientScalarNormalization`. That parent's theorem
  asserted only invertibility, used a common scheme/coefficient universe, and lacked
  this node's derived product, ordinary limit and normalized Roos conclusions. It was
  not an exact match; subsequent shared-source refresh removed that old parent module.

No statement correction and no STATEMENT-DISPUTED flag are needed.

## Dependency modules

`lem-weil-constant-scalar-strict-unit`: the shared node recorded the complete strict-unit
interface, which was read before writing the consumer. The prescribed scompile call
failed because `Sheaf.Paper.ConstantScalarStrictUnit.olean` did not exist, including in
its server confirmation, and `scompile.py --source Sheaf.Paper.ConstantScalarStrictUnit`
returned `Module source unavailable`. A subsequent authorized shared refresh also removed
the local file, while its node and accepted interface remained. Section 1(B) therefore
restores that interface in this delivery. Its definitions and theorem signature retain
the recorded bodies and all clauses; docstrings are rewritten to document the restoration.
Only the dependency node's `lean` field changes, with a note explaining this failure.
There is no new notion, no alternate scalar construction, and no mathematical change.
Its theorem remains `sorry`; it includes K-flatness with flat terms, finite multiplication
and derived tensor computation, identity reduction units, unique strict normalization,
and equivalence with the unit-only condition.

Validation: scompile.py compiled both delivered files separately in dependency order,
including both their sandbox and library forms, with exit zero and no warnings.
The only elaboration repair was qualifying `Pretriangulated.Triangle.mk` in the
consumer; this changed no mathematical statement. Both files satisfy the 100-character
line limit and explicitly disable auto-implicit variables. The dependency theorem
signature in its node record was updated to the exact multiline text of its restored file.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
