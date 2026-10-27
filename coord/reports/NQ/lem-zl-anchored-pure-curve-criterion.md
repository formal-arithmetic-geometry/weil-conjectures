## Worker report

The module `Sheaf.Paper.AnchoredPureCurveCriterion` states
`WeilConjectures.anchoredPureCurveCriterion`. Its proof is `sorry` and its docstring
contains the node's seven-step proof, including the nonzero anchor fibre, positive
logarithmic denominators, the power calculation, comparison with further curves,
global purity, and uniqueness. Every auxiliary definition contains actual data.
The TeX statement is unchanged. There are no disputed statements or dependency repairs.

Clause correspondence:

- The finite field, algebraic closure and specified subfields are `D : FiniteFieldDatum`.
  The prime and its inequality are `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
  `Ω : Type (u + 1)` with its field, Padic algebra and algebraic-closure instances
  is the coefficient closure; `iota : Ω ≃+* ℂ` is the stated field isomorphism.
- The scheme is `X₀ : Over (Spec (.of D.k₀))`; `[LocallyOfFiniteType X₀.hom]`
  and `[QuasiCompact X₀.hom]` express finite type. `[IsSeparated X₀.hom]`,
  `[Nonempty X₀.left]`, and `[GeometricallyConnected X₀.hom]` express the other
  three hypotheses with Mathlib's recorded notions.
- `S : ZlClassicalWeil D l Ω X₀` is the actual classical lisse Weil sheaf
  (`EtaleLisseWeilSheaf`, an IsoAlgebra for classical adic Frobenius pullback).
  `hne : ¬ IsZero S.carrier` says its underlying classical sheaf is nonzero.
  `A : ZlClassicalRealization ...` is the recorded normalized interpretation;
  `anchoredRealizedSheaf ... A S` is precisely `(A.weil ...).obj S`.
  The structural prime-unit Fact is constructed inline from
  `zlClassicalStalkInvertible`, not imposed as a new hypothesis.
- `anchor : {x : X₀.left // x ∈ closedPoints X₀.left}` is the chosen closed point.
- The arbitrary collection is `I : Type w`, `tests : I → AnchoredCurveTest D X₀`.
  The bundle has `m`, `positive : 1 ≤ m`, a scheme `curve` over the specified
  `D.extensionSubfield m positive`, finite-type and quasi-compact structure,
  `Smooth curve.hom`, `GeometricallyConnected curve.hom`, `IsAffine curve.left`,
  and `curve.left.IsPureDimension 1`. Its `immersion` is a morphism over k_m
  into `constantExtensionModel ...`, with `IsClosedImmersion immersion.left`.
  These are the chapter's curve convention, with no properness or rational-point
  assumption. Geometric connectedness over a field also ensures nonemptiness.
- `R m hm` and `hR m hm : ConstantExtensionRestrictionSpec ... (R m hm)`
  name the specified constant restriction, including its canonical carrier
  comparison and m-fold Weil map. They are presentation data for that recorded
  construction, not arbitrary functors. `t.restriction ... (R t.m t.positive) F`
  is the actual `zlWeilPull ... t.immersion` applied to `R.obj F`.
- Hypothesis (i) is `hcover`: for every closed `x`, some `i` has closed points
  `za`, `z` whose actual composite projection equals `anchor.val`, `x.val`.
  It includes `x = anchor` and does not require the two lifts to be distinct.
- Hypothesis (ii) is `hpure`: the given real `weights i` is a punctual purity
  weight of the actual restriction, using `SfIsPunctuallyPureOfWeight` with
  datum `constantExtensionDatum D (tests i).m (tests i).positive`.
- Hypothesis (iii) is `hpower` and the expanded `AnchoredCurveTest.LocalPower`.
  For every closed `z`, closed `x`, and equality of its actual image with x,
  it asserts `1 ≤ projection.residueDegree z.val`, the exact integer identity
  `Nat.card κ(z) = Nat.card κ(x) ^ projection.residueDegree z.val`, and equality
  of the local eigenvalue multiset with the image of that at x under `α ↦ α ^ f`.
  `Hom.residueDegree` is the finrank for the actual induced residue-field map.
  `anchoredFiniteLocalSpectrum` evaluates the existing
  `localClosedFrobeniusCohomology` on H^0 of each finite Weil presentation, maps
  its characteristic polynomial along the prescribed Shrink coefficient
  inclusion, then takes `.roots` in Ω. This retains algebraic multiplicities
  and zero eigenvalues. All finite presentations and residue embeddings are
  quantified, making the statement independent of auxiliary choices. The two
  presentations may use different coefficient fields; each is included into
  Ω, so there is no common-stage existence assumption or hidden field bound.
- The conclusion `∃ weight : ℝ` gives punctual purity, followed by a separate
  `∀ weight', ... → weight' = weight`. This asserts uniqueness among all
  punctual purity weights, not merely among weights satisfying extra clauses.
- The anchor clause quantifies every `α` satisfying `SfPunctualEigenvalue` and
  asserts `α ≠ 0 ∧ weight = 2 * Real.logb (Nat.card κ(anchor) : ℝ) ‖iota α‖`.
  Thus the formula is independent of α. `Real.logb b x` is `log x / log b`.
- The next clause states `weights i = weight` for each supplied member with a
  closed point over the anchor, including supplied members unused by hcover.
- The further-curve clause universally quantifies `t : AnchoredCurveTest D X₀`
  and `v : ℝ`; an anchor lift, LocalPower and purity of weight v imply `v = weight`.
  There is no requirement that t be in `tests` or have a point over another x.
- The final clause explicitly asserts the requested modulus formula for every
  closed x and each `SfPunctualEigenvalue` β, with actual `Nat.card κ(x)`.

Dependency declarations read and used:

- `Sheaf.Paper.AdicPunctualWeights`: `SfPunctualEigenvalue`,
  `SfIsPunctuallyPureOfWeight`, with their complete finite-stage signatures.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` and
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`: geometric-property classes;
  `GeometricallyConnected` is used, as allowed by the existing dependency record.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`:
  `LisseIntegralSheafOfUniverses`, the coefficient-stage underpinning of the
  classical category; `Sheaf.Paper.EtaleWeilFundamentalRepresentation`:
  `AlgebraicGeometry.Scheme.EtaleLisseWeilSheaf`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPointComplex`, `localClosedPoint`,
  `localClosedFrobeniusCohomology` (the recorded local operator, in degree zero).
- `Sheaf.Paper.RealSheavesSetup`: `RealSheaves.Setup.IsCurve`; its smooth,
  pure-dimension-one, separated finite-type and geometric-connected convention
  was read. Curve geometry is rendered directly with the same Mathlib notions
  and the finite-field datum already needed for constant extension.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and
  `CategoryTheory.Over.pullback` for the underlying base-change construction.
- `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`: `constantExtensionDatum`,
  `constantExtensionModel`, `constantExtensionProjection`, and
  `ConstantExtensionRestrictionSpec` (full return-comparison equation read).
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded common-stage pullback;
  its existing Weil-heart lift is `zlWeilPull` in
  `Sheaf.Paper.WeilIndSheafCategory`.
- `Sheaf.Paper.NormalizedClassicalWeilRealization`: `ZlClassicalWeil`,
  `ZlClassicalRealization`, `ZlClassicalRealization.weil`,
  `zlClassicalStalkInvertible`. The normalized comparison is the existing
  integral/unit-pinned realization, not an arbitrary map or stalk isomorphism.
- `Sheaf.Paper.CoefficientCohomologyModules`:
  `DerivedCategory.coefficientFdCohomology_finite` supplies the actual finite
  dimensionality needed by charpoly inside the helper definition.
- `Mathlib.Analysis.SpecialFunctions.Log.Base`: `Real.logb` and the recorded
  proof lemmas `Real.rpow_logb`, `Real.logb_le_iff_le_rpow`; natural log and
  real power are the existing `Real.log`, `Real.rpow`.
- Proof-only imports include `GaloisLisseRepresentations`, `ClosedPointField`,
  Mathlib separated/base-change/noetherian modules and
  `Mathlib.LinearAlgebra.Eigenspace.Triangularizable` (`Module.End.exists_eigenvalue`).
  The proof dependency `lem-zl-classical-local-frobenius-iterate-comparison`
  has no recorded Lean module at this delivery; its proof use is described in
  the docstring, with the defining normalized realization imported.

Two already landed nodes were added to stmt_deps because their interfaces are
explicitly used: `def-zl-normalized-classical-weil-realization` and
`def-zl-weil-ind-sheaf-category`. No new nodes are needed: the six helpers are
packaging/evaluation declarations belonging to this criterion, and each has its
own source and blueprint docstring and is listed in lean.declarations.

Edge cases checked: empty I contradicts hcover at the anchor; empty X is
excluded explicitly; zero classical sheaf is excluded exactly where uniqueness
needs it. Rank-zero fibres on some points still have empty spectra, with no
invented eigenvalue. Taking x equal to the anchor is included and allows za=z.
The case m=1 and residue degree f=1 is included; m=0 is excluded. Power collisions
preserve repetitions through Multiset.map. Characteristic-polynomial roots keep
zero eigenvalues, so LocalPower does not discard the case whose impossibility
is established from curve purity. The smallest residue cardinality is 2; no
logarithm of 1 is assumed invertible. Additional family members need not pass
through the anchor. Dimension-zero X simply has no test family satisfying hcover.
The collection universe w is independent because it indexes an arbitrary
collection, not a universal quantification over test field extensions. The
coefficient universe u+1 is the recorded classical-lisse convention.

Searches for an existing exact statement/notion:

- msearch leanfinder: "Pure restrictions of a nonzero lisse Weil sheaf on curves
  through a fixed closed point imply unique global punctual purity": eight hits
  about scheme germs and residue fields, no match.
- msearch loogle: "Real.logb, Real.rpow": zero hits. Source reads locate the
  elementary logarithm lemmas, not the geometric criterion.
- msearch grep: "anchored|PunctuallyPure|WeilSheaf": zero Mathlib hits.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for anchored, pure curves,
  the item id, and the proposed declaration names found no exact statement.
  Existing curve-purity and stalk/pullback results were inspected.
- The additional leanfinder query "multiset of Frobenius eigenvalues
  characteristic polynomial roots local stalk" returned only ring Frobenius
  results; grep for the proposed helper names had zero hits. The existing
  `fdWeilLocalEigenvalues` was read in `WeilPullbackLocalFrobenius`: it takes
  a same-universe coefficient datum and uses common-stage fibres, whereas this
  statement's classical category has Ω in u+1. The helper here evaluates the
  finite-stage operator already used by SfPunctualEigenvalue and maps charpoly
  into Ω; it introduces no independent spectrum construction or chosen object.
- Proposed full declaration names were also searched in
  `dag/lean_names_upstream.json`, with no collisions.

Validation: scompile.py checks each source separately against the published live
library. Final compile and delivery-preflight results are recorded below.

Self-review against the opened node and source found no missing conclusion:
uniqueness is separate from ancillary clauses, the further-curve quantifier is
unrestricted by family membership, and condition (iii) retains multiplicities.
Removed an initial Prop-valued helper definition after the compiler warned;
the same derived structural fact is now constructed inline, without any new theorem.
Final scompile.py run passed in sandbox and module modes (9.5 s and 5.2 s),
without errors or additional warnings. Initial deliver2.py --no-push passed
preflight and per-file compilation. Final delivery repeats those checks.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
