## Worker report

The item is stated in `lean/Sheaf/Paper/SfRationalLocalGlobalPowerTorsion.lean` as
`WeilConjectures.sfRationalLocalGlobalPowerTorsion`.  It is a theorem statement with
proof `sorry`; no mathematical claim is proved at this stage.  The module uses the
independent universes `u` for the coefficient field and `t` for the scheme and uses
`max u (t + 1)` for sheaves on the pro-etale slices.

The Lean rendering of each part of the node statement is as follows.

* “Fix a prime `l`” is `(l : ℕ) [Fact l.Prime]`.
* “A finite extension `E/Q_l`” is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
* “`l` is invertible on `X`” is
  `(_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))`.
* “`X` is a scheme” is `(X : AlgebraicGeometry.Scheme.{t})`.
* The derived object with completed integral coefficients is
  `(C : DerivedCategory (integralTowerModules l E X))`.
* A finite covering family, including the empty family, is
  `(n : ℕ)`, `(U : Fin n → AlgebraicGeometry.Scheme.ProEt X)`, and
  `hU : (AlgebraicGeometry.Scheme.ProEt.topology X).CoversTop U`.
* The global coefficient category is equipped with the stated linear structure by
  `[Linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (integralTowerModules l E X))]`.
* For each `j : Fin n`, the slice coefficient category and its linear structure
  are expressed by
  `[∀ j : Fin n, Linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (SheafOfModules.{max u (t + 1)}
      ((completedIntegralCoefficientSheafUnrestricted l E X).over (U j))))]`.
* Termwise restriction to the slice is
  `(SheafOfModules.overFunctor.{max u (t + 1)}
    (completedIntegralCoefficientSheafUnrestricted l E X) (U j)).mapDerivedCategory.obj C`.
* The local scalar-localization zero condition is exactly `hzero`, with
  `ScalarLocalization.localization ... (Padic.coefficientExtensionUniformizer l E)`
  applied to that restricted object and wrapped in `IsZero`.
* The conclusion is
  `∃ N : ℕ, ∀ d : ℤ, (DerivedCategory.homologyFunctor
  (integralTowerModules l E X) d).map
  ((Padic.coefficientExtensionUniformizer l E) ^ N • 𝟙 C) = 0`.
  Thus one exponent works simultaneously for every cohomological degree.

Dependency declarations used:

* `def-weil-completed-integral-coefficients`: `WeilConjectures.integralConstantToCompletionOfUniverses` and the accompanying declarations in `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` (the module also supplies the unrestricted completed coefficient sheaf used here).
* `def-weil-pbc-proetale-site`: Mathlib's `AlgebraicGeometry.Scheme.ProEt` and
  `AlgebraicGeometry.Scheme.ProEt.topology` from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
* `def-pur-localized-ringed-site`: Mathlib's `SheafOfModules.overFunctor` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, including its
  `mapDerivedCategory` extension used by the side module.
* `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` from
  `Sheaf.CategoryTheory.RingedSiteModules`, transparently the Mathlib
  `SheafOfModules` category.
* `def-weil-abstract-derived-category`: Mathlib's `DerivedCategory` and
  `DerivedCategory.homologyFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
* `def-weil-linear-scalar-localization`: `CategoryTheory.ScalarLocalization` and
  `CategoryTheory.ScalarLocalization.localization` from
  `Sheaf.CategoryTheory.ScalarLocalization`.

I read the full recorded signatures and docstrings in the corresponding source
modules.  The source module also declares only the needed universe-polymorphic
sheafification, slice exactness, finite-limit/colimit, and derived-category
instances; these are concrete instances and contain no `sorry` data.  The theorem
itself is the only postponed proof.

Edge cases checked:

* `n = 0` is permitted by `Fin n`; `CoversTop` therefore includes the explicitly
  allowed empty cover.
* The global exponent is `ℕ`, so exponent zero is represented and the empty-cover
  case is expressible.
* The conclusion quantifies over all `d : ℤ`, including degrees outside a bounded
  range.
* `u` and `t` are independent, and slice sheaf categories use
  `max u (t + 1)`; no silent universe equality is imposed.
* The invertibility hypothesis is explicit and applies to every stalk of `X`.

Searches performed:

* Existing node search: `rg -n lem-sf-rational-local-global-power-torsion
  dag/nodes` found only this node; no duplicate declaration node exists.
* Project/source search: `rg -n 'rational|local-global|power torsion|uniform.*power|scalar.*localiz'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no matching declaration.
* Mathlib searches recorded on the node were rerun conceptually and checked by
  source inspection: LeanFinder/LeanSearch returned only generic localization,
  homology, or affine-local annihilation results; Loogle returned
  `CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished`; grep of
  `Mathlib/CategoryTheory/Sites` found no completed-coefficient finite-cover
  statement.  None has the same completed sheaf-coefficient hypotheses and
  conclusion, so no existing declaration matches.
* `rg` source checks confirmed that the only pro-etale declarations are
  `Scheme.ProEt` and its topology, while the scalar-localization construction is
  project-specific.

No new nodes or dependency modules were required, and no statement correction or
`STATEMENT-DISPUTED` flag is needed.  The file was compiled with
`scompile.py Q151 lem-sf-rational-local-global-power-torsion` and completed without
errors or warnings (the expected `sorry` declaration warning is suppressed by the
module option).

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
