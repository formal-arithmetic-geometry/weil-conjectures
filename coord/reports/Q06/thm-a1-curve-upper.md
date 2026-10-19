## Worker report

Recorded an exact existing declaration, with no new Lean module:
`AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve`
in `WeilConjectures.DeligneLaumon.Reduction.OpenLine` (published upstream source).
The module is absent from the older local slopmaster2 snapshot. I read its current
complete source using `scompile.py --source WeilConjectures.DeligneLaumon.Reduction.OpenLine`.
Its theorem docstring explicitly names `thm-a1-curve-upper`. The node's `lean.statement`
is the literal signature from that source, including the inherited smoothness instance.
Only the node's `lean` field changes. There are no new definitions, proofs, dependency
modules, or statement corrections.

Source checked: main-20261015, sec-deligne-laumon-general/sk-l-dl-general-open-line,
`thm-a1-curve-upper.md` and `thm-a1-curve-upper.proof.md`. Their statement is the node's
statement and their proof specializes the middle-extension estimate to the identity.
The existing theorem does precisely that: it applies the upstream middle-extension
bound to `𝟙 C`, then uses `WeilSheaf.lowerStarIdIso` and the induced Frobenius-module
equivalence to identify compact-support cohomology. No new proof is supplied here.

Hypotheses and clauses, with all inherited ambient binders read from the source:

- The base is an arbitrary finite field: `{k₀ : Type u} [Field k₀] [Finite k₀]`.
  Its cardinality is `Nat.card k₀`, the chapter's `q`; no specific finite field is excluded.
  The coefficient prime is `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
  `PadicAlgCl l` supplies the chosen algebraic closure of the l-adic coefficient field.
- The curve over the finite field is `{C : Scheme.{u}} [C.Over (Spec (.of k₀))]`.
  `[IsSeparated (C ↘ Spec (.of k₀))]` and `[QuasiCompact (C ↘ Spec (.of k₀))]`
  are the separated finite-type curve convention of `d-real-setup`, not extra properness
  or affineness hypotheses. Local finite type follows from smoothness.
- Smoothness and pure dimension one are
  `[SmoothOfRelativeDimension 1 (C ↘ Spec (.of k₀))]`.
  Over a field, a smooth geometrically connected pure one-dimensional curve has this
  relative dimension. The upstream module uses the equivalence
  `smoothOfRelativeDimension_iff_topologicalKrullDim_eq` for a connected smooth scheme.
  Thus a point is excluded exactly as the source's curve convention requires.
- Geometric connectedness is
  `[GeometricallyConnected (C ↘ Spec (.of k₀))]`; it includes connectedness and
  nonemptiness after extension to an algebraic closure. The empty scheme is excluded
  by the source as well. No separate choice of geometric fibre is an extra assumption.
- The sheaf and its Weil structure are `(F : WeilSheaf k₀ l C)`; lissity is
  `(hF : F.IsLisse)`. I read `WeilSheaf.Category`: these are constructible adic sheaves
  on the geometric fibre with an isomorphism from geometric Frobenius pullback;
  `IsLisse` is `IsAdicLisseSheaf F.obj.carrier`. This theorem concerns sheaves in the
  heart, not arbitrary complexes or derived Ext morphisms between Weil objects.
- The coefficient embedding is the ambient `(ι : PadicAlgCl l →+* ℂ)`, an injective
  field homomorphism with no continuity condition, exactly the convention in
  `d-real-setup`. In particular it admits every field isomorphism in the punctual-weight
  node. No continuity or prescribed archimedean embedding is imposed.
- The arbitrary real weight is `{w : ℝ}`. Punctual purity is
  `(hw : F.IsPunctuallyPureOfWeight ι w)`. Its recorded definition quantifies over
  finite/closed points and tests each eigenvalue of local geometric Frobenius against
  the residue cardinality, with equality `‖ι α‖ = q_x ^ (w / 2)`.
- Every cohomological degree is `(r : ℤ)`, including negative degrees, not only natural
  degrees. The conclusion is
  `(F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r)`.
  This is precisely the weight bound `w+r` on geometric compact-support cohomology.
  The recorded `ordinaryCompactWeilSheafCohomology F r` is the pair
  `(F.cohomology r, F.compactlySupportedCohomology r)`, so its second component is
  definitionally the coefficient object used here, with its same Frobenius.
- `HasWeightsAtMostOver` means that each geometric Frobenius eigenvalue has complex
  norm at most `q ^ ((w+r)/2)`. For a finite-dimensional vector space over the
  algebraically closed coefficient field and invertible Frobenius, this also gives
  the filtration formulation of `def-weil-frobenius-module-weights`: triangularize
  Frobenius, use its stable flag, and give a nonzero eigenvalue α the real weight
  `2 log_q ‖ι α‖`. Since q > 1, the norm bound is exactly that each weight is at most
  `w+r`. Conversely a stable pure-quotient filtration gives the same eigenvalue bound.
  No semisimplicity is assumed or needed.
- The inherited `haveI := SmoothOfRelativeDimension.smooth 1 ...` in the existing
  signature just exposes the smoothness already assumed. It adds no mathematical
  hypothesis. This is a verbatim record of an existing signature, not a new statement
  using a hidden local binder.

Dependency declarations read and used in checking the match:

- `Sheaf.Paper.OrdinaryCompactWeilCohomology`,
  `AlgebraicGeometry.WeilSheaf.ordinaryCompactWeilSheafCohomology`: its second component
  is definitionally the compact-support Frobenius module of the existing theorem.
- `WeilConjectures.DeligneLaumon.Reduction.Weights`,
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight` (publicly imported there,
  defined in `WeilConjectures.WeilSheaf.Stalk`): exactly the hypothesis used.
- `Sheaf.Paper.RealSheavesSetup`, `RealSheaves.Setup` and `RealSheaves.Setup.IsCurve`:
  checked the finite-field, coefficient-embedding, separated finite-type, smooth,
  pure-dimension-one and geometrically connected conventions against the binders.
- `Sheaf.Paper.LisseAdicSheaves`, `AlgebraicGeometry.Scheme.LisseIntegralSheaf`,
  `LisseRationalSheaf`, and `LisseAlgebraicSheaf`: read the finite-level compatible
  system, rationalization and algebraically closed coefficient conventions. The
  existing theorem uses the upstream adic lissity interface, with no private copy.
- `Sheaf.Paper.SfWeilSheafComplex`, `WeilConjectures.sfWeilComplex`, `sfWeilSheaf`,
  `sfCommonStageWeilComplex` and `sfCommonStageWeilSheaf`: read the corrected fixed-pair
  versus derived-of-pairs distinction. This theorem uses only Weil sheaves, whose
  actual upstream definition is a category of fixed pairs of constructible sheaves;
  it makes no assertion about morphisms or a triangulated structure on Weil complexes.
- `Sheaf.LinearAlgebra.FrobeniusModuleWeights`,
  `FrobeniusModule.IsMixedOfWeightsAtMost`: checked the finite stable-filtration
  definition against the eigenvalue bound as described above. The actual existing
  conclusion uses `FrobeniusModule.HasWeightsAtMostOver`, defined in
  `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule`.
- The proof dependencies are `Sheaf.Paper.CurveWeilMiddleExtension`,
  `AlgebraicGeometry.WeilSheaf.curveWeilMiddleExtension` (ordinary `directImage`), and
  `Sheaf.Paper.CurveMiddleExtensionUpper`,
  `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_compactlySupportedCohomology_curveMiddleExtension`.
  Read their complete signatures and proof docstrings. They express the same
  identity-specialization route already implemented by the existing upstream theorem.
  Recording an existing theorem adds no imports or copies of these declarations.

Edge cases checked: the zero sheaf is allowed and its zero cohomology has no eigenvalues;
negative r and r > 2 remain included and give zero groups; degree zero is not dropped;
proper curves with empty boundary, affine curves and nonaffine nonproper curves are all
allowed. For the weight-zero constant sheaf on P¹ or A¹, H_c² has weight 2, agreeing
with w+r. No nonzero-rank, irreducibility, affineness, properness, ramification or
semisimplicity assumption occurs. The empty scheme and zero-dimensional schemes are
not curves in the source convention. There is no statement dispute.

Searches performed:

- `msearch.py ... leanfinder`, query: “Compactly supported cohomology of a smooth
  geometrically connected curve with a punctually pure lisse Weil sheaf of weight w
  has weights at most w plus the degree”. Eight hits concerned Lie weights and
  unrelated affine-section/limit facts; no theorem matching this statement.
- `msearch.py ... loogle`, query: `"HasWeightsAtMostOver", "compactlySupportedCohomology"`.
  Zero hits.
- `msearch.py ... grep`, query:
  `hasWeightsAtMost.*compact|compact.*[Ww]eight|IsPunctuallyPureOfWeight`.
  One unrelated weighted Holder inequality in Mathlib/Analysis/MeanInequalities.lean.
- `rg` on the local upstream and `lean/Sheaf`, query:
  `hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve|thm-a1-curve-upper|hasWeightsAtMost.*[Cc]urve`.
  The only local hit is the more general ordinary middle-extension proposition in
  `Sheaf.Paper.CurveMiddleExtensionUpper`. The node's audit nevertheless names the
  exact theorem in `WeilConjectures.DeligneLaumon.Reduction.OpenLine`; fetching its
  current published source with `scompile.py --source` found the exact statement and
  docstring. The absent older snapshot therefore does not justify restating it.

Validation: the prescribed `deliver2.py --no-push` compiles an existing-declaration
`#check @...` probe via scompile.py and runs the server preflight; results are recorded
by the delivery wrapper. No new Lean file requires compilation.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
