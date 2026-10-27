## Worker report

Item: lem-pur-relative-external-power-regrouping. The single module
`Sheaf.Paper.RelativeExternalPowerRegrouping` states all geometric and finite-Tor
claims as `WeilConjectures.RelativeExternalPower.relative_external_power_regrouping`
(with the sole new postponed theorem proof). Its public definition `regroup` supplies
rho itself as an actual derived-category isomorphism. All thirteen declarations
are listed in lean.declarations. There are no new DAG nodes, dependency repairs,
statement corrections, disputed statements, or additional theorem obligations.

Hypothesis and conclusion correspondence:

- `P : PurityFiniteSetting` is exactly def-pur-conventions' finite field, distinct
  coefficient prime, finite subextension of the fixed coefficient closure and
  positive level. `P.Ring` is the actual quotient O_E/(varpi^n), with the standard
  coefficient universe lift performed by the existing pro-etale category. No
  divisibility of the level by the ramification index is imposed.
- `B`, `b : B ⟶ Spec (CommRingCat.of P.field.k)`, and the three instances
  `IsSeparated b`, `LocallyOfFiniteType b`, `QuasiCompact b` express exactly the
  separated finite-type base over k. Finite type is locally finite type plus qc.
- `r`, `hr : 1 ≤ r`, `X : ℕ → Over B` and `hX : ∀ i < r, ...` encode the r
  factors and their separated finite-type maps to B. The zero-based factor i is
  the paper's i+1. The infinite family is an indexing convenience, not an
  additional mathematical restriction: extend any nonempty finite family beyond
  r by repeating its first factor and first complex. There are no hypotheses on
  those unused entries. Every construction at index j uses only entries ≤ j.
- `K` consists of actual objects in `proEtaleDerivedCategory (X i).left P.Ring`.
  `hK` uses the recorded pro-etale `finiteTorConstructible` for precisely i < r;
  it does not infer finite Tor amplitude from bounded constructibility.
- `product X 0 = X 0` and `product X (j+1)` is literally the chosen Mathlib
  pullback of `(product X j).hom` and `(X (j+1)).hom`, with structure map fst
  followed by the old structure map. Thus product index j is P_(j+1).
  `fst`, `snd` are its actual two projections. `projection` starts at the
  identity, extends old coordinates by fst and uses snd for the last coordinate.
- `external` is T_(j+1), namely `tensorPrefix` of the derived pullbacks along
  those coordinate projections. The nonempty tensor is explicitly left
  associated, starts with the one input at index zero, and never inserts an
  empty tensor or coefficient unit.
- The first quantified conjunction, `∀ j < r`, asserts separated finite type
  of P_(j+1) over k, of its structure map to B, and of every coordinate
  projection. Its last clause is membership of T_(j+1) in precisely the recorded
  bounded constructible finite-Tor predicate.
- The second conjunction, `∀ j, j+1 < r → ...`, asserts separated finite type
  of a_(j+1) and b_(j+1), then the two individual finite-Tor constructible
  pullback-domain conditions on P_(j+2).
- `regroup X P.Ring K j` is rho_(j+1), with source the tensor of those exact
  two pullbacks and target literally `external ... (j+1)`. An isomorphism is
  constructed as data rather than postponed under an existential proposition.
  `pullbackPrefix` recursively uses `proEtaleCanonicalTensorComparison`, with
  the flat K-flat representative normalization and canonical constant-section
  coefficient identification. `externalPullback` then tensors the components
  of `proEtaleConstantRingPullbackComposition a (p i) A`, the inverse of the
  source's c_(a,p). Finally `regroup` applies the tensor bifunctor to that
  isomorphism and the identity on the last pullback. Its `simpa only` performs
  just unfolding and the two Fin lastCases equations and val computations.
  No theorem from this node is used to define its own map. Left association
  makes additional associators unnecessary; the target matches T_(j+2).
- There is no flatness, compact-support, exceptional-adjoint or duality premise.
  All comparisons are isomorphisms of derived objects, never only degreewise
  cohomology isomorphisms.

Recorded dependency declarations and actual source inspection:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, and the inherited coefficient field/ring instances.
- `Sheaf.Paper.FiniteTorAmplitudeSites` publicly exposes
  `WeilConjectures.finiteTorConstructible` from `FiniteTorAmplitude`. Its
  ordinary-etale primary predicate is not substituted for the pro-etale one.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; existence on schemes is supplied by the
  existing scheme pullback imports.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` exposes the general
  normalized tensor-pullback theorem of the recorded dependency.
  Its existing original-small-site specialization in
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback` supplies `ProEtaleTensorModel`
  and `proEtaleCanonicalTensorComparison`. Both are declarations of that same
  DAG dependency, not a replacement theorem or an unconstrained isomorphism.
- `Sheaf.Algebra.Homology.RingedDerivedTensorNative`: `RingedDerivedNative.monoidal`,
  `tensorIso`, `tensorIso_naturality` supply the existing derived tensor and its
  representative comparison. `tensorModel` only packages those existing data;
  it defines no second derived tensor.
- `Sheaf.Paper.IntegralFinitePullbackComposition` publicly imports
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`, providing
  `proEtaleConstantRingPullbackComposition`. Read its full definition: it is the
  inverse of `proEtaleCanonicalPullbackComposition` followed by the equality
  of composite constant coefficient identifications. Its direction is exactly
  La* Lp* → L(pa)*. This works for any A, so no off-by-one positive-level
  specialization of integralFiniteCanonicalPullbackComposition is required.
- Proof imports: `Sheaf.Paper.PullbackTorAmplitude` (`sfFiniteDerivedPullback`,
  `sf_pullback_torAmplitude`, `sf_pullback_finiteTorConstructible`);
  `Sheaf.Paper.FiniteCoefficientTensorCtf`
  (`AlgebraicGeometry.Scheme.finiteCoefficient_tensor_ctf`);
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` (constant-section coefficient
  identification); `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
  (`ringedDerived_closed_symmetric_monoidal`). The geometric mathlib leaves use
  `IsSeparated` composition/base-change instances, `locallyOfFiniteType_comp`,
  `quasiCompact_comp` and their pullback instances, read in their source files.

Sources read: Stacks sites-cohomology.tex, lemma-pullback-K-flat (0G7E),
lemma-derived-pullback-composition (0D6D), and lemma-pullback-tensor-product (07A4),
including their proofs. Also read the current blueprint's affine-space composition
law and proof under sk-prop-sp-composition and the finite-Tor pullback statement
under sec-proetale-coefficients. The module's docstring carries the node's four-step
proof: geometry induction; fixed Tor intervals with additive bounds; tensor
pullback and composition; tensor lambda with the final identity.

Edge cases checked: r=1 has exactly j=0 and no successive regrouping assertion;
r=2 has the binary regrouping, whose prefix distribution is the identity before
its one composition comparison; j=0 has the actual identity projection. Empty
schemes and zero inputs are admitted. No nonempty-scheme or nonzero-object condition
appears. Positive coefficient level and ell different from p come from P. Site
object and morphism universes remain u+1 and u; no equality of these universes
is imposed. All universes and binder variables are explicit with autoImplicit false.

Searches for duplicates (2026-10-22):

- msearch.py leanfinder: “Finite external derived tensor products on relative
  fibre products canonically regroup under pullback and preserve bounded
  constructible finite Tor amplitude”: 8 hits, all scheme residue-field tensor
  constructions (Pullback.Triplet.tensorCongr and Spec tensor pullback results),
  none giving this derived finite-Tor assertion.
- msearch.py loogle: `CategoryTheory.MonoidalCategory, "tensor"`: 12 hits,
  the generic tensor, tensoring functors and left/right triple tensors. They
  supply generic categorical vocabulary but not the theorem.
- msearch.py grep: `externalProduct|externalPower|regroup`, AlgebraicGeometry:
  no hits.
- msearch.py leansearch: “Nonempty iterated relative external derived tensor
  products of constructible finite Tor complexes canonically regroup under
  pullback”: 8 hits, generic HomologicalComplex tensor and Tor and ordinary
  categorical/scheme pullback formulas; none match.
- rg in project Sheaf and WeilConjectures for externalPower, external_power,
  external.*regroup, RelativeExternal and relativeExternal: no existing match.
  Searching the item id under WeilConjectures returned no match. Searching the
  proposed namespace and theorem name in Mathlib and dag/lean_names_upstream.json
  returned no match. Broader finite-Tor/tensor/pullback searches found and reused
  the normalized operations described above, rather than making private copies.

Validation: required scompile.py compiled the sandbox and library module cleanly
(16.1 and 16.8 seconds respectively on the clean run). No diagnostic commands remain
in the delivery. Every definition has actual data; the sole theorem has `sorry`.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
