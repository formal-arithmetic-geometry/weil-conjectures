## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianModelDimensionLocusPullback` states
`AlgebraicGeometry.noetherianModel_localFibreDimension_locus_pullback`. Its only proof
is `sorry`; there are no definitions or additional theorems. Only the item's `lean`
field changes. No statement correction, new node, or dependency repair is needed.

The inherited BLOCKED ending concerns a stage-1 live-wins check. The present
`coord/brief-stage2.md` §0 explicitly says that an accepted stage-1 split is input to
stage 2, not a prohibition on recording Lean. The current item has no `lean` field
and is listed in `coord/queue.tsv` at stage 2. Its accepted split and review remain
unchanged. No repair note for this item was found in `coord/repair-notes`.

Source read: `literature/stacks-project/algebra.tex`,
`lemma-dimension-fibres-bounded-quasi-compact-open-upstairs` (00QJ), especially the
inverse-image paragraph and final Noetherian compactness sentence; and
`literature/stacks-project/morphisms.tex`,
`lemma-dimension-fibre-after-base-change` (02FY(1)) and
`lemma-openness-bounded-dimension-fibres` (02FZ). The abstract scheme-level
statement makes precisely the Noetherian-model and quasi-compact-projection
hypotheses used in that paragraph explicit. The main 00QJ theorem assumes finite
presentation to construct the model, but this auxiliary statement already supplies
that model and requires only local finite type, exactly as 02FY and 02FZ do.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The three schemes are `{X₀ S₀ S : Scheme.{u}}`, with arbitrary explicit universe
  `u`. The maps `h₀ : X₀ ⟶ S₀` and `g : S ⟶ S₀` are arbitrary scheme morphisms.
- Local finite type of `h₀` is `[LocallyOfFiniteType h₀]`.
- Local Noetherianity of `X₀` is `[IsLocallyNoetherian X₀]`. Its quasi-compactness
  is `[CompactSpace X₀]`, which has no Hausdorff condition.
- The specified fibre product is Mathlib's chosen `pullback h₀ g`. Its map `h` is
  `pullback.snd h₀ g` and its map `q` is `pullback.fst h₀ g`; there is no arbitrary
  comparison map or additional choice.
- Quasi-compactness of `q` is `[QuasiCompact (pullback.fst h₀ g)]`. This does not
  assume quasi-compactness of `g`, or impose any property on the pullback or base.
- Each nonnegative integer is `(n : ℕ)`; casting to `WithBot ℕ∞` gives the same
  finite nonnegative bound without excluding `n = 0`.
- `L₀,n` is the set
  `{x₀ : X₀ | topologicalKrullDimAt (h₀.asFiber x₀) ≤ (n : WithBot ℕ∞)}`.
  Mathlib's `h₀.asFiber x₀` is the distinguished point of the scheme-theoretic fibre
  `h₀.fiber (h₀ x₀)`, not the dimension of its local ring.
- `L_n` is the identical expression for `pullback.snd h₀ g` on
  `x : ↥(pullback h₀ g)`.
- The first conjunct equates this `L_n` with `(pullback.fst h₀ g) ⁻¹' L₀,n`.
- The next conjunction gives `IsOpen L₀,n` and `IsCompact L₀,n`.
- The final conjunction gives `IsOpen L_n` and `IsCompact L_n`.
  `IsCompact` of a subset is precisely quasi-compactness with its induced topology.
- No `LocallyOfFinitePresentation`, `IsLocallyNoetherian S`, or Noetherian
  hypothesis on `pullback h₀ g` is present. There is no hidden let, private notation,
  local instance, or auto-bound parameter in the signature.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (morphisms expressed with `⟶`).
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; its quasi-compact clause is
  `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, imported publicly by FiniteType.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (the equivalent every-affine-open form).
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, and `.snd`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, `fiberHomeo`, and `asFiber`.
  The source defines `asFiber` using the inverse fibre homeomorphism, so its
  projection is exactly the original point.
- `def-kun-topological-dimension-at-point`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`, the
  infimum of Krull dimensions of open neighbourhoods, exactly the node's notion.

Proof-plan dependencies are imported with plain `import` when not already statement
imports: `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
(`AlgebraicGeometry.fibre_dimension_after_base_change`) and
`Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen`
(`AlgebraicGeometry.isOpen_localFibreDimension_le`), plus
`Mathlib.Topology.NoetherianSpace`
(`TopologicalSpace.NoetherianSpace.isCompact`). The other proof dependencies use
`AlgebraicGeometry.noetherianSpace_of_isAffine` in the already public Noetherian
module, and `AlgebraicGeometry.Scheme.Hom.isCompact_preimage` in the already public
QuasiCompact module. The theorem docstring includes all four accepted proof steps,
including the finite affine cover argument and the empty-cover case.

Edge cases checked before writing:

- Empty `X₀`: its pullback and both loci are empty, hence open and compact; no
  `Nonempty` assumption excludes it. Empty `S` similarly gives an empty pullback.
- Identity base change: both loci identify and compactness is exactly compactness
  of the model's bounded-dimension open subset.
- `X₀ = S₀ = Spec k`, `S = Spec K` for an arbitrary field extension: fibre dimension
  is zero everywhere, so for `n = 0` both loci are whole schemes. Positive
  transcendence degree causes no local-ring-dimension confusion.
- `X₀ = A¹_k`, `S₀ = Spec k`, `S = Spec K`: local topological dimension of each
  nonempty fibre at each point, including the generic point, is one. For `n = 0`
  the loci are empty; for `n ≥ 1` they are whole spaces.
- Necessity of the projection hypothesis: with `X₀ = S₀ = Spec k` and `S` an
  infinite disjoint union of copies of `Spec k`, `L_0 = S` is not compact.
  Thus the projection hypothesis is substantive and must be retained.
- No characteristic or separatedness assumption is used. The common arbitrary
  scheme universe matches the dependency interfaces and does not restrict a
  family of test objects to an independent smaller universe.

Searches actually run with `msearch.py Q40
lem-trf-noetherian-model-dimension-locus-pullback`:

- LeanFinder: `Bounded local fibre dimension loci commute with base change and are
  quasi compact open when pulled back from a Noetherian scheme`. Eight hits:
  quasi-finite/finite-type/quasi-compact base-change stability,
  `quasiCompact_of_noetherianSpace_source`, and open-immersion compactness. No
  result states this locus equality together with both compact-open conclusions.
- Loogle: `AlgebraicGeometry.QuasiCompact, IsCompact`. Six hits:
  `quasiCompact_iff_forall_isAffineOpen`, `Scheme.Hom.isCompact_preimage`,
  `QuasiCompact.isCompact_preimage`, `QuasiCompact.mk`, `quasiCompact_iff`,
  and `Scheme.Hom.isCompact_preimage_singleton`. They supply compactness tools,
  not the fibre-dimension assertion.
- Mathlib grep: `(fiber|fibre).*(dimension|krullDim)|(dimension|krullDim).*(fiber|fibre)`
  in `AlgebraicGeometry`. One hit, a descriptive comment in
  `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:23`, not a match.
- LeanSearch: the same natural-language query as LeanFinder. Eight hits on
  morphism-property stability and `IsLocalAtTarget.of_isPullback`; none states
  the local-dimension locus conclusion.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `dimensionAt|dimAt|fiberDimension|fibreDimension|localFiberDimension|localFibreDimension`
  and the item id, followed by `topologicalKrullDimAt.*asFiber` and the reverse
  expression. Read the base-change and local-openness modules, and
  `RetrocompactBoundedFibreDimension.lean`. The latter assumes local finite
  presentation and states retrocompactness, so it is not this theorem.
- The item-id search of `lean/WeilConjectures` and `dag/lean_names_upstream.json`
  found no existing attachment. No exact declaration is duplicated.

No mathematical node fault or STATEMENT-DISPUTED issue was found. Validation uses
only the prescribed `scompile.py` and `deliver2.py` wrappers.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
