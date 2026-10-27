## Worker report

The delivery states `lem-sfb-trait-section-differential-defect-criterion` in
`Sheaf.AlgebraicGeometry.TraitSectionDifferentialDefectCriterion`. Its sole theorem,
`AlgebraicGeometry.trait_section_differential_defect_criterion`, has proof `sorry`.
Two helpers belonging to this same notion have real data:
`traitSectionDifferentials` applies Mathlib's `moduleSpecΓFunctor` to the recorded
`Scheme.Modules.tensorPullback` of `f.relativeDifferentials`, and
`traitSectionDifferentialDefect` takes `Module.length` of `Submodule.torsion` of that module.
These are the node's V_a and delta_X(a), not extra input modules or arbitrary substitutes.

Source read: BLR, Néron Models, §3.3 opening paragraph and Lemma 1, printed pp.64–65,
PDF pages 70–71, at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The flat case of its argument applies on a finite-type affine neighbourhood of the closed
image. The inverse image of that neighbourhood contains the closed point of a local spectrum,
so contains the whole section. This justifies the node's locally finite type refinement.
No natural-language statement, dependency, or proof field was changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| R is a DVR | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| K is its fraction field | `[Field K] [Algebra R K] [IsFractionRing R K]` |
| k is the residue field | Mathlib's canonical `IsLocalRing.ResidueField R` |
| Choose k^sep | `[Field ksep] [Algebra (IsLocalRing.ResidueField R) ksep] [IsSepClosure (IsLocalRing.ResidueField R) ksep]` |
| R-algebra action on k^sep comes through k | `[Algebra R ksep] [IsScalarTower R (IsLocalRing.ResidueField R) ksep]` |
| Chosen strict henselization A | `[CommRing A] [Algebra R A]` and `P : Algebra.StrictHenselizationPresentationIn.{u, u} R ksep A` |
| Scheme X over Spec R | `(X : Scheme.{u}) (f : X ⟶ Spec (.of R))` |
| Flat and locally finite type | `[Flat f] [LocallyOfFiniteType f]` |
| Smooth generic fibre | `Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))` |
| Any R-morphism a | `(a : Spec (.of A) ⟶ X)` with `ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))` |
| V_a is Gamma(Spec A, a*Omega) | `traitSectionDifferentials f a`; `moduleSpecΓFunctor` gives precisely global sections with scalars restricted through `ΓSpecIso` |
| A is the discrete valuation ring over which V_a is considered | The conclusion supplies `∃ (_ : IsDomain A) (_ : IsDiscreteValuationRing A), ...`; the DVR property of A is derived, not an added hypothesis |
| V_a is finitely generated | `Module.Finite A (traitSectionDifferentials f a)` |
| Torsion means killed by a nonzero scalar | `Submodule.torsion A ...`; its non-zero-divisors are exactly nonzero elements under the concluded `IsDomain A` |
| The torsion has finite length | `traitSectionDifferentialDefect f a ≠ ⊤`; the helper is exactly `Module.length A (Submodule.torsion A ...) : ℕ∞` |
| delta_X(a) = 0 iff smooth at the closed image | `traitSectionDifferentialDefect f a = 0 ↔ ∃ U : X.Opens, a (IsLocalRing.closedPoint A) ∈ U ∧ Smooth (U.ι ≫ f)` |
| No quasi-compactness and no uniform bound | Neither is a binder or conclusion; the theorem applies to each arbitrary a and locally finite type X |

All rings and schemes are in one arbitrary common universe `u`; the chosen strict
henselization presentation is the recorded `. {u, u}` specialization (without the space).
Every universe and variable is explicit; both auto-implicit options are disabled.
The standard same-universe scheme category is used throughout, and no quantification over
smaller test algebras or a potentially vacuous independently small category is introduced.

Recorded statement dependencies read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, with its domain and non-field conventions.
- `def-sc-ring-strict-henselization`: `Algebra.StrictHenselizationPresentationIn`,
  `Sheaf.RingTheory.StrictHenselizationPresentationIn`. Its full pointed-etale diagram,
  universal cocone and algebra identification are retained by taking the presentation as input.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat` (the affine condition is equivalent to stalk flatness).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; no `QuasiCompact` assumption.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; smoothness at a point is smoothness on an open neighbourhood.
- `def-sc-relative-differential-sheaf`: `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`,
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`.
- `def-pc-module-pullback`: `Scheme.Modules.tensorPullback`, exposed by the recorded
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`; its source
  `WeilConjectures.AlgebraicGeometry.TensorPullback` constructs inverse image and scalar extension.
  No alternative pullback or adjunction is chosen.
- `def-weil-pbc-module-length`: `Module.length`, `Mathlib.RingTheory.Length`.

The source signatures and docstrings of these declarations were read. The global-sections
functor and its scalar-action instance were read in `Mathlib.AlgebraicGeometry.Modules.Tilde`;
the actual torsion definition was read in `Mathlib.Algebra.Module.Torsion.Basic`.

All recorded, stated proof-dependency modules are plain imports. In particular these include
`AffineStrictLocalRingComparison`, `StrictHenselizationDVR`, `ModulePullbackAffineSections`,
`SmoothDifferentialsFreeRankFibreDimension`, `SmoothAtPrimeDifferentialsDimension`,
`LocalFibreDimensionOpen`, and `SmoothAtPointDifferentialCriterion`, plus the Mathlib
PID, Smith basis, DVR dimension, length, Nakayama, and locally Noetherian APIs. The existing
`StrictHenselizationDVR` module currently contains its theorem in a withdrawal comment;
it is imported, but the present statement does not depend on that theorem being available.
`lem-trf-relative-differential-sheaf-base-change` currently has no recorded Lean declaration
or Mathlib match; its future proof import is therefore omitted. This is only a proof
prerequisite, not a missing notion required to type this statement. Stage 3 must establish
those proof steps; none is silently assumed as an extra hypothesis here.

Edge cases checked before writing:

- Rank zero, the zero differential module, and zero torsion are included by Module.Finite
  and Module.length; zero length is not expressed using categorical IsZero on a bare type.
- Unit Smith coefficients and an empty torsion direct sum give length zero as required.
- The empty X has no a, so the universally quantified section assertion has no instances.
- A non-quasi-compact X remains allowed; a section lies in one affine neighbourhood as above.
- No perfectness of k, algebraic closedness of ksep, characteristic condition, excellence,
  completion, separateness or rationality of the image points is imposed.
- The zero ring and fields are excluded for R by exactly the recorded DVR definition.
  No DVR or local-ring hypothesis is imposed independently on A.
- The length remains in ℕ∞, so finiteness is an actual conclusion; no premature natural-number
  truncation could turn infinite length into zero.

Searches for an existing statement (raw wrapper output is preserved in `searches.jsonl`):

- LeanFinder: “Torsion length of differentials pulled back along a section of a flat
  generically smooth scheme over a discrete valuation ring is zero exactly at smooth points”.
  Eight results, including `Algebra.smoothLocus`, its cotangent/support description, and
  formal-smoothness criteria. None gives this section-module torsion-length criterion.
- Loogle: `Module.length, KaehlerDifferential`. Successful query, zero hits.
- Mathlib grep wrapper: `torsion.*smooth|smooth.*torsion|length.*[Dd]ifferential` in RingTheory.
  Successful query, zero hits.
- LeanSearch: “Neron defect length of torsion in differentials along a strict henselian
  trait section vanishes if and only if smooth at the closed point”. Eight hits involving
  smooth loci, formal smoothness, H1Cotangent and standard-smooth bases; no exact assertion.
- `rg` over project `lean/WeilConjectures` and `lean/Sheaf` for trait/section differential
  defect and torsion/smooth patterns, and the exact node ID: no existing criterion.
  Related smooth-section basis and torsion-sheaf declarations have different statements.
- `rg` over Mathlib and both project roots for all three proposed declaration names:
  no collisions. Existing `Submodule.torsion`, `Module.length`, `tensorPullback`,
  `relativeDifferentials`, and `moduleSpecΓFunctor` are reused directly.

No new DAG nodes, dependency replacements, statement corrections, or disputed statement.

Validation: the prescribed `scompile.py` is used for every compiler invocation. The first
compile identified an underdetermined ModuleCat universe in the section helper; it was
repaired by specifying `ModuleCat.{u}` and the `CommRingCat.of A` parameter explicitly.
The repaired module compiled successfully in both the wrapper's sandbox and library checks,
with no warnings or errors. The single-file limit was left unchanged.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
