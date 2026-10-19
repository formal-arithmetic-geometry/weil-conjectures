## Worker report

The module `Sheaf.Paper.TwConventions` bundles the given inputs and specializes the
recorded constructions to the geometric base change. No definition has postponed data,
no new theorem is stated, and there are no `sorry`s in the module. The source is the
current main-20261015 blueprint, `sec-six-functors/sk-rem-sf-pf-done/def-tw-conventions.md`,
order 2448. Its short convention paragraph agrees with the existing node's more explicit
expansion, so the natural-language statement is retained without a correction.

Clause-by-clause matching to the node:

* Prime `p`, positive exponent `r`, and `q = p ^ r`: `TwConventions.datum` is the
  existing `FiniteFieldDatum`; its `p`, `a`, `prime`, `exponent_pos`, `q`, and
  `cardinality_eq` fields give these exact data. A positive natural exponent gives
  precisely the positive integer exponents of the statement.
* The field `k = F_q` and chosen algebraic closure `kbar`: the same datum has `k₀`
  with a field structure, finiteness and `Nat.card k₀ = q`, and `k` with its field,
  `Algebra k₀ k`, and `IsAlgClosure k₀ k`. Here `D.k₀` is the node's `k`, and `D.k`
  is the node's `kbar`, exactly the renaming specified in the node.
* Prime `ell != p`, `Q_l`, and a chosen algebraic closure: `coefficients` is the
  recorded `datum.CoefficientDatum`; its `l`, `Fact l.Prime`, `different`, `Qbar`,
  `Field`, `Algebra (Padic l) Qbar`, and `IsAlgClosure` fields give all these data.
  `Padic l` is the existing `Q_l`, with no new coefficient-field definition.
* The separated finite-type `k`-scheme is `X : Over (Spec (.of datum.k₀))`, with
  instance fields `IsSeparated X.hom`, `LocallyOfFiniteType X.hom` and
  `QuasiCompact X.hom`. These are the conventions of the scheme-conventions node.
  No smoothness, properness, connectedness, or nonemptiness condition is added.
* `X_kbar = X ×_Spec(k) Spec(kbar)` and its structure map are exactly
  `datum.geometricFiber X` and its `.hom`, supplied by the finite-field dependency.
  The three `geometric*` instance declarations specialize existing base-change
  instances to that exact fiber; they introduce no new hypothesis.
* The Qbar coefficient category is `TwConventions.coefficientCategory`, whose final
  expression is precisely `Scheme.pbcQbarCategory` on that geometric fiber. Its
  noetherianity is obtained from the existing finite-type theorem, its finite
  dimension from `exists_topologicalKrullDim_le`, and coefficient invertibility by
  mapping `finiteFieldDatumPrimeUnit` through the canonical field-to-global-sections
  map followed by the germ map. These are consequences, not additional inputs.
* For each `i : ℤ`, `TwConventions.compactlySupportedCohomology T i` is the second
  component of `qbarConstantCohomology` on that geometric fiber. This component is
  definitionally `qbarCompactCohomology` applied to `qbarCohomologyCoefficient`.
  Therefore it is exactly the stated `H_c^i` of the constant coefficient object,
  including zero and negative degrees.
* The constant coefficient object is reused from the ordinary-compact-cohomology
  dependency. Its definition uses `constantCoefficientPair`'s underlying completed
  integral object, the integral constructibility proof, and rational localization.
  We use `Padic.finiteCoefficientBase`, the least finite field inside Qbar, so no
  arbitrary finite extension is added as a parameter. The cohomology construction
  uses its recorded completed-coefficient presentation; no definitional equality
  between the two coefficient-category presentations is asserted here.

The canonical compactification in the last definition is the existing
`HasCompactification.compactification`, supplied by
`hasCompactification_of_finiteType_over_field`. This is the same normalization used
by the project's intrinsic compact-support construction. The already landed
`def-asd-compactifiable` was added to `stmt_deps` to record that input. There are no
new nodes or dependency repairs.

Dependency declarations and sources read:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `WeilConjectures.FiniteFieldDatum.CoefficientDatum`, and
  `WeilConjectures.FiniteFieldDatum.geometricFiber` (full structures, docstrings,
  and base-change definition).
* `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory`
  (including its noetherianity, dimension, and stalk-invertibility binders).
* `def-weil-pbc-scheme-conventions`: this is recorded as a convention, with no
  module or single declaration; it explicitly uses Mathlib `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` for the properties used here.
* `Sheaf.Paper.OrdinaryCompactCohomology`: `WeilConjectures.qbarConstantCohomology`,
  `WeilConjectures.qbarCohomologyCoefficient`, `WeilConjectures.qbarCompactCohomology`,
  and `WeilConjectures.qbarCompactSections` (signatures and complete definitions).
* `Sheaf.AlgebraicGeometry.CompactifiableOverField`:
  `AlgebraicGeometry.hasCompactification_of_finiteType_over_field` (all hypotheses).
* `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.exists_topologicalKrullDim_le`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`.

Edge cases checked: exponent one is allowed, exponent zero is excluded exactly by
`exponent_pos`; both the empty scheme and `Spec k` are allowed; disconnected and
nonproper schemes are allowed; the dimension bound works for empty schemes because
it is an upper bound, not an equality with a natural dimension; all `i : ℤ` are
accepted; and `ell = p` is excluded exactly by the coefficient datum.

Searches for an existing whole convention:

* `msearch.py NL def-tw-conventions leanfinder
  "finite field conventions algebraic closure compactly supported Qbar l cohomology"`:
  eight results including `FiniteField.Extension`, finite-extension instances,
  Hilbert 90 helpers, and absolute Galois groups. None defines this convention.
* `msearch.py ... leansearch
  "compactly supported l-adic cohomology of the constant algebraic closure of Q_l coefficient object on the geometric base change of a finite field scheme"`:
  eight results, including base-change stability, `PadicAlgCl`, and proper global
  sections finiteness. No complete match; the base-change instances are reused.
* `msearch.py ... loogle
  "FiniteFieldDatum, qbarConstantCohomology, compactlySupportedCohomology"`:
  rejected because the side-project identifier `FiniteFieldDatum` is absent from
  the index. Retried with the valid quoted query `"EllAdicCohomology"`: three hits.
  Its source `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`, lines 59–85,
  defines ordinary integral cohomology in natural degrees, not this construction.
* `msearch.py ... grep
  "TwConventions|twConventions|compactlySupportedCohomology" AlgebraicGeometry`:
  no Mathlib match. Direct `rg` for `TwConventions`, `twConventions` and the blueprint
  id in `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json` also found
  no whole-convention declaration.
* Direct source searches for `compactlySupportedCohomology`, `FiniteFieldDatum`, and
  `qbarConstantCohomology` identified the reused dependencies. Upstream
  `WeilComplex.compactlySupportedCohomology` and `WeilSheaf.compactlySupportedCohomology`
  take Weil objects and use a fixed `PadicAlgCl`; they are not the present convention.

No node fault or `STATEMENT-DISPUTED` issue was found. The previous stage-1 report's
coefficient-prime concern is handled explicitly by `CoefficientDatum.different`.

## Second reading by NL

This is the dispatcher's requested author self-check, not an independent review; the
maintainer performs the independent reading. I reopened the node, its current blueprint
paragraph, all four original dependency records, the additional compactifiability record,
and the completed module. The finite-field renaming and positive exponent agree. The
scheme has exactly the three required morphism properties. The geometry is the recorded
pullback, not an independently chosen model. The coefficient category is now literally
`pbcQbarCategory`: an initial draft used the other coefficient presentation directly,
which was corrected before delivery. Its domain conditions are derived using existing
results without extra inputs. The constant object and all-degree compact cohomology are
exactly the ordinary-compact-cohomology definitions. No arbitrary coefficient object,
comparison, or additional finite-stage choice enters the interface. Both citers,
`def-tw-eigenvalue` and `def-tw-frobenius-action`, retain the same conventions. The latter
explicitly describes the canonical completed-coefficient presentation used for cohomology.

The file passed the prescribed `scompile.py` sandbox and library-name compiles without
errors or warnings. Final delivery preflight is run on this completed version.
