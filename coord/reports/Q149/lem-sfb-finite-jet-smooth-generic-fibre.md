## Worker report

Item: lem-sfb-finite-jet-smooth-generic-fibre. Source read: Stacks Project,
`literature/stacks-project/examples-defos.tex`, Tag 0E7T,
`lemma-criterion-smoothing`, lines 2899–2931, including its proof.

The module `Sheaf.AlgebraicGeometry.FiniteJetSmoothGenericFibre` states
`AlgebraicGeometry.smooth_genericFibre_of_finiteJet_fitting`, with `sorry` as its
entire proof. The only other declaration is the canonical map
`AlgebraicGeometry.Scheme.powerSeriesJetBaseMap`: it is constructed as `Spec.map`
of `Ideal.Quotient.mk` for `(t^n)`, with real data and no postponed proof. This is
the canonical map introduced by the item, not a separate independent notion.
The theorem docstring carries all nine steps of the node's proof.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; the base is
  `Spec (.of (PowerSeries k))`. This is the one-variable form explicitly permitted
  by def-weil-pbc-multivariate-power-series and the POWER SERIES convention.
- The given family is `(f : Y ⟶ Spec (.of (PowerSeries k)))`, with
  `[IsProper f] [Flat f] [LocallyOfFinitePresentation f]`. Properness supplies
  quasi-compactness and separatedness, hence quasi-separatedness, so this is
  exactly the node's proper flat finitely presented family. No extra finiteness
  assumption is imposed. The Stacks source need not say finite presentation
  separately because the power-series base is Noetherian.
- The special fibre is the actual `pullback f (Spec.map (CommRingCat.ofHom
  (PowerSeries.constantCoeff (R := k))))`, using the canonical map to k.
  `hCM` quantifies over every point of this scheme and equates
  `IsLocalRing.depth (R := O) O`, cast into `WithBot ℕ∞`, with `ringKrullDim O`,
  for its stalk O. This states equality of local-ring depth and dimension,
  without replacing it by regularity or a global-dimension condition.
- `(d : ℕ)` includes zero; `hpure` is `Scheme.IsPureDimension d` on that very
  special fibre. It quantifies over all irreducible components by the recorded
  definition and is vacuous for the empty scheme.
- `Scheme.powerSeriesJetBaseMap k n` has source
  `Spec (.of (PowerSeries k ⧸ Ideal.span {PowerSeries.X ^ n}))`. Thus
  `pullback f (Scheme.powerSeriesJetBaseMap k n)` is exactly X_n and
  `pullback.snd` is its structure map to S_n. Stacks writes k[t]/(t^n);
  coefficient truncation canonically identifies it with this quotient for n≥1,
  as already explained in step 1 of the node. No source or node correction occurs.
- `hjet : ∃ n : ℕ, 1 ≤ n ∧ ...` is exactly the existential positive jet order.
  Inside it `Ideal.Quotient.mk _ (PowerSeries.X ^ (n - 1))` is the requested
  image of t^(n-1). `Scheme.ΓSpecIso ... .inv` views this as a global section
  on S_n, and `(pullback.snd ...).appTop` pulls it back to X_n. Membership in
  `(Scheme.Modules.fittingIdealSheaf (...).relativeDifferentials d).idealOfOpens ⊤`
  says that this global section lies in the d-th Fitting ideal sheaf. The read
  upstream `IdealSheaf.Module` defines `idealOfOpens` on arbitrary opens and
  proves `range_toModulesι_app_eq_idealOfOpens`; hence this is actual global
  ideal-sheaf membership, including when X_n is nonaffine.
- The conclusion is `Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom
  (algebraMap (PowerSeries k) (LaurentSeries k)))))`. The read Mathlib instance
  `LaurentSeries.of_powerSeries_localization` identifies this canonical algebra
  map as localization at t, so it is exactly the Laurent-series generic fibre
  over k((t)), with its specified structure morphism.

Statement dependencies used, with their recorded declarations read in source:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; scheme
  pullbacks are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `WeilConjectures.RingTheory.Depth`: `IsLocalRing.depth` (and `Ideal.depth`).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.FittingIdealSheaf`:
  `Scheme.Modules.fittingIdealSheaf`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`; its one-variable
  form `PowerSeries` and `PowerSeries.constantCoeff` are read in
  `Mathlib.RingTheory.PowerSeries.Basic`.
- Added the already landed `lem-trf-dth-fitting-smooth-locus` to `stmt_deps`:
  `Sheaf.AlgebraicGeometry.DthFittingSmoothLocus` supplies its recorded helpers
  `relativeDifferentials_isFiniteType` and
  `relativeDifferentials_isQuasicoherent`. These are the existing instances
  needed to form the Fitting ideal of the base-changed differential sheaf.
  Their only hypothesis is locally finite presentation, inherited by base
  change. The main smooth-locus theorem is not used to impose any additional
  geometric-equidimensionality hypothesis. No dependency node is modified.

Plain proof imports follow the existing node's plan:
`WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
(`MvPowerSeries.power_series_field_cohen_regular_complete`),
`WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus`
(`isOpen_fibre_depth_eq_ringKrullDim`),
`WeilConjectures.AlgebraicGeometry.CohenMacaulayFibreDimensionDecomposition`
(`exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim`),
`WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension`
(`topologicalKrullDimAt_eq_of_equidimensional_open`),
`Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally`
(`Scheme.Modules.fitting_ideal_generate_locally`),
`Sheaf.RingTheory.PresentationFittingIdeal`
(`LinearMap.presentationFittingIdeal_independence_baseChange`),
`Sheaf.AlgebraicGeometry.SmoothAtPointDifferentialCriterion`
(`Scheme.Hom.smoothAtPoint_iff_flat_stalkMap_and_differentials_generators`),
`Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource`
(`smooth_iff_of_jointly_surjective_etale`), Mathlib's
`RingTheory.Kaehler.TensorProduct` (`KaehlerDifferential.tensorKaehlerEquivBase`,
`tensorKaehlerEquiv`), `AlgebraicGeometry.Morphisms.Etale` (open immersions are
étale; smooth/étale base-change interfaces), and
`AlgebraicGeometry.Morphisms.QuasiSeparated` (qcqs permanence, with finite
presentation permanence in the public finite-presentation import).

Edge cases checked before writing: n=1 means t^0=1 and unit Fitting ideal on
X_1; n=0 is excluded by `1 ≤ n`. Dimension d=0 uses the zeroth Fitting ideal,
without an artificial d>0 assumption. Empty special fibre satisfies both CM and
pure dimension vacuously, and properness then forces Y empty; the statement
adds no nonemptiness assumptions. Empty jets and empty generic fibres likewise
remain allowed. The field may have any characteristic. The single universe u
places the coefficient field and all schemes in one common scheme universe;
there is no quantification over undersized test algebras and no extra universe
equality hypothesis.

Searches actually run:

- msearch.py leanfinder: “A proper flat family over power series over a field has
  smooth generic fibre if a power of the parameter lies in the Fitting ideal of
  relative differentials of an infinitesimal fibre”. Eight hits, including
  `Algebra.Smooth.flat`, `Algebra.IsSmoothAt`, `Algebra.Smooth`, and
  `RingHom.smooth_def`; none states the proper-family finite-jet criterion.
- msearch.py loogle: `PowerSeries.constantCoeff, LaurentSeries,
  AlgebraicGeometry.Smooth`. Zero hits.
- msearch.py grep: `finite.*jet|criterion.smoothing|smooth.*generic.*fibre|Fitting.*smooth`
  in Mathlib/AlgebraicGeometry. Zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
  `finite.jet|criterion.smoothing`: no declaration of this criterion; the
  isolated-LCI smoothing theorem mentions it only in its proof plan.
- rg in the same project sources for finite type/quasi-coherence of
  `relativeDifferentials` found the existing DthFittingSmoothLocus helpers.
- rg in Mathlib and both project roots for `FiniteJetSmooth`, `finiteJetSmooth`,
  `powerSeriesJetBaseMap`, `powerSeriesJetParameter`: no existing declaration
  with the proposed names. Read LaurentSeries' canonical localization and the
  existing ideal-sheaf arbitrary-open interface rather than duplicating them.

No statement dispute, correction, new definition node, or dependency-module
repair was necessary. The only node changes are its Lean record and the added
landed helper-owning node in `stmt_deps`.

Validation: scompile.py compiled the sandbox probe and actual module separately,
cleanly in 6.4 s and 6.1 s. The initial compile found an ambiguous coercion in
`∀ x : pullback ...`; explicitly writing `∀ x : ↥(pullback ...)` fixes its category
to Scheme and its points to the carrier of that scheme. No diagnostic commands
remain, and `autoImplicit` is false.

## Second reading by Q149

A second pass by this worker reopened the final Lean file and the node. No
separate agent was started, as the dispatcher explicitly forbids that; the
maintainer's independent delivery review is still required. This pass checked
that hCM uses the special-fibre stalk three times consistently, hpure uses that
same fibre and the same d as the Fitting index, and hjet pulls back the quotient
class of the power (not a freely chosen section or map). The quotient map and
the Laurent inclusion both have their canonical directions under Spec.map.
The finite-presentation assumption is equivalent to the node's under properness.
The global ideal membership uses idealOfOpens at top, which the upstream module
identifies with the image of the ideal's module inclusion on global sections.
No extra Cohen--Macaulay or dimension hypothesis is imposed on generic fibres.
The empty case, d=0 and n=1 remain included. The only change from this reading
was documenting the use of the existing differential finiteness helpers and
adding their owning landed node to stmt_deps; no source statement was changed.
