# Stage-2 delivery: lem-per-henselian-component-dimension

## Worker report

The module `Sheaf.AlgebraicGeometry.HenselianComponentDimension` states
`AlgebraicGeometry.Scheme.henselian_has_one_dimensional_component_iff_strictHenselization`.
Its only proof is `sorry`. No definitions, new nodes, dependency repairs, or statement
corrections are needed. The node copy changes only `lean`.

I read the item's statement, all six proof steps and all five statement dependency
records, and opened their recorded declarations and docstrings. I also read ILO,
Travaux de Gabber, Expose XIV, Lemma 2.1.5 and its proof, printed page 210, using
`pdftotext -layout` on the supplied PDF. The source says that a Noetherian henselian
local scheme has a one-dimensional irreducible component if and only if its strict
henselization at a geometric closed point has one. The node and Lean express that
same statement.

Hypothesis and clause correspondence:

- The commutative ring A is `(A : Type u) [CommRing A]`.
- Noetherianity is `[IsNoetherianRing A]`.
- The local and henselian conditions are together `[HenselianLocalRing A]`, which
  extends `IsLocalRing A`. There is no added strict-henselian assumption.
- T = Spec A is written directly as `Spec (.of A)` throughout.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(barX : Spec (.of Ω) ⟶ Spec (.of A))`.
- That geometric point lies over the closed point precisely means
  `hbarX : barX (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint A`.
  A field spectrum has just its closed point, so this evaluates the geometric point
  at its unique underlying point.
- Existence of an irreducible component of T of dimension one is
  `∃ C ∈ irreducibleComponents (Spec (.of A)), topologicalKrullDim C = 1`.
  The type coerced from `C` has exactly its subspace topology.
- The strict localization is the dependency's existing
  `strictHenselizationScheme barX`, the spectrum of the affine pointed-etale
  coordinate-ring colimit, now an abbreviation for the upstream construction.
- The right-hand clause is
  `∃ C ∈ irreducibleComponents (strictHenselizationScheme barX),
  topologicalKrullDim C = 1`. The connective `↔` retains both implications.

The statement definitions used are:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded henselian terminology
  interface; the relevant `HenselianLocalRing` is from its Mathlib import.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, with a geometric point
  represented inline as prescribed by `def-weil-geometric-point`. The signature and
  docstring of `AlgebraicGeometry.Scheme.SpecToEquivOfField` were also read in
  `Mathlib.AlgebraicGeometry.ResidueField` to check this representation.
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationScheme` and its ring construction.
  The current server source was additionally read with `scompile.py --source`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- Mathlib's `irreducibleComponents` and `IsLocalRing.closedPoint`, whose definitions
  were read in `Topology.Irreducible` and `RingTheory.Spectrum.Prime.Topology`.

All recorded proof dependency modules are imported without `public`, in addition to
public imports exposing the statement notions. In particular, these include
`WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`,
`Sheaf.RingTheory.StrictHenselizationTriples`,
`Sheaf.RingTheory.StrictHenselizationFaithfullyFlat`,
`Sheaf.TraceFormula.IndEtaleLocalHenselianIntegral`, the recorded ind-etale and
henselization interfaces, Mathlib's faithfully flat, going-down, spectrum and minimal
prime results, and `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp` for
`ringKrullDim_eq_of_isIntegral`. The declaration docstring spells out every one of
the node's six proof steps: identify the colimit and flatness, obtain integrality and
injectivity, contract and lift minimal primes, compare prime-quotient dimensions,
and translate through component and quotient-spectrum identifications.

Edge cases checked before drafting: a field and an Artinian henselian local ring
have no dimension-one component on either side; a strictly henselian DVR has one
on both sides; reducible rings may have several components and the statement asks
only for existence, not a bijection of components or equidimensionality. Nilpotents
are permitted. The zero ring has no geometric closed point and is excluded by
local-ring/geometric-point data, as in the source. No characteristic, excellence,
reducedness, normality or universal-catenarity condition has been introduced. All
universes and variables are explicit, with `autoImplicit false`. Using a common
universe for A and Ω follows the existing strict-localization interface; arbitrary
sizes can be placed in their common larger universe.

Searches for an existing complete statement, performed with the prescribed tools:

- `msearch.py ... leanfinder` query: "A Noetherian henselian local ring has a one
  dimensional irreducible component if and only if its strict localization at a
  geometric closed point does". Eight hits: DVR TFAE and cotangent criteria,
  finite ring dimension, local henselian inheritance, local dimension-one criteria,
  and spectrum specialization facts. None compares components with strict localization.
- `msearch.py ... loogle` query:
  `HenselianLocalRing, irreducibleComponents, topologicalKrullDim`: zero hits.
- `msearch.py ... grep` query: `strictHensel|StrictHensel|HenselianLocalRing`,
  subdirectory `RingTheory`: five hits in Mathlib's `Henselian.lean`, all terminology
  or henselian root criteria, with no strict-localization component theorem.
- `rg` in the upstream `WeilConjectures` tree, the shared `lean/Sheaf` tree and
  `dag/lean_names_upstream.json` for henselian/component/dimension combinations,
  strict-henselization/component combinations, and the proposed declaration name:
  no existing theorem with this statement. The exact blueprint id search in the
  upstream tree also found no declaration.
- Existing `Sheaf.RingTheory.StrictHenselizationDimension` concerns the dimension
  of the whole local ring, which does not state this existence claim for components.
  `StrictLocalClosureComponentCriterion` instead compares closures of lifted points
  with components of a reduced local closure; it is also a different statement.

No statement dispute or node fault was found. The theorem has exactly one `sorry`;
no theorem was proved. The single delivered file compiled cleanly through
`scompile.py NK lem-per-henselian-component-dimension <module>` in both sandbox
(1.9 seconds) and library (2.4 seconds) modes. No compiler warnings or errors were
reported.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
