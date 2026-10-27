## Worker report

Module: `Sheaf.Paper.CompleteResidueLineInverse`.
Main declaration: `WeilConjectures.completeResidueLineInverse`.
The only postponed theorem is that declaration, with `sorry`; all helper definitions
have actual data. Its docstring carries all eight steps of the DAG proof. The node's
statement, dependencies and proof are unchanged. There are no new nodes or dependency
repairs and no STATEMENT-DISPUTED issue.

Hypothesis-by-hypothesis and clause-by-clause reading:

- The prime is `(l : ℕ) [Fact l.Prime]`; `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` is its finite coefficient extension.
  `Padic.coefficientExtensionRing l E (n + 1)` is precisely the quotient of its
  valuation ring by the (n+1)-st power of the chosen uniformizer. No alternate
  uniformizer or quotient presentation is introduced. Natural index zero denotes
  exponent one; every positive exponent appears.
- `(X : Scheme.{u}) [IsNoetherian X]` uses Mathlib's actual schemes and Noetherian
  condition. `isNoetherian_iff_of_finite_iSup_eq_top` identifies the latter with the
  finite affine Noetherian cover stipulated by the node, including the empty cover.
- `_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)` states invertibility of l on X.
- `M : IntegralOnSlice.D.{u,u} l E X none` is the ambient derived category of modules
  over the actual limit coefficient sheaf on X.ProEt. The site has object universe
  u+1 and morphism universe u; these have not been equated.
- `_hM : IntegralOnSlice.IsComplete.{u,u} l E X none M` is exactly the recorded
  augmented quotient-tower completeness condition, in its global branch.
- `(m : ℤ)` is unrestricted. `L` is an etale sheaf of modules over the canonical
  universe lift of the exponent-one quotient. `_hL` explicitly asks for an etale
  covering on which `L.over` is isomorphic to the constant rank-one module. The
  helper `completeResidueEtaleLine` merely packages this displayed clause; it does
  not replace a general local-constancy definition or add chosen trivializations.
- `_hres` is a nonempty isomorphism from the recorded derived scalar reduction of
  M at exponent one to the degree-zero intrinsic comparison pullback of L shifted
  by m. `completeResidueEtalePullback` uses the existing canonical comparison and
  intrinsic coefficient realization, with the actual finite quotient ring.
- `∃ T : IntegralOnSlice.Mod ...` and `T.IsFiniteLocallyFreeOfRank 1` express the
  asserted locally free completed-coefficient line. The next conjunct is exactly
  the isomorphism `M ≅ T[0][m]`, with no specified global basis.
- For every natural n, `Ln`, `completeResidueEtaleLine ... Ln`, and the underived
  scalar-extension isomorphism say that T tensor B_(n+1) is of etale origin and
  etale locally constant with free rank-one values. The constant value in that
  predicate is the rank-one quotient module itself, not an arbitrary finite module.
- `completeResidueDual` is the existing ambient internal Hom into the completed
  coefficient unit. It is not a completed Hom or an independently chosen inverse.
- The two `finiteTorConstructibleIntegral` conjuncts are exactly membership of M
  and its internal-Hom dual in the recorded D^b_ctf category. This includes their
  derived completeness, constructible reductions, and uniform boundedness.
- `completeResidueEvaluation` is the tensor-Hom counit with dual on the left;
  `completeResidueEvaluationReverse` is its composite with the recorded Koszul
  symmetry. Their two `IsIso` conjuncts assert that these particular maps are
  isomorphisms, not merely that some isomorphism exists.
- For every n the four support/Tor conjuncts use the recorded cohomological support
  and `HasProEtaleTorAmplitude`, with intervals `Set.Icc (-m) (-m)` and
  `Set.Icc m m`. They express both cohomological and Tor intervals exactly as in
  the node, uniformly over all positive reductions.
- Both ordinary tensors explicitly satisfy the recorded `IsComplete`. Both
  canonical `completionUnit` components are invertible. The existing definition
  of `IntegralOnSlice.completedTensor` is ordinary tensor followed by this
  normalized quotient-tower completion, including its global comparison with
  the strict two-finite-reduction tower.
- Finally `e` and `e'` are isomorphisms from these specified completed tensors to
  the coefficient unit. Their two equations say that composition with the
  canonical comparison is exactly the corresponding ordinary evaluation. Thus
  the final completed evaluation clause is explicit and canonically normalized.

Dependency declarations used (full signatures and source docstrings inspected):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian` and its finite-affine-cover
  characterization.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the existing completed
  coefficient ring and its canonical finite quotient cone, publicly reexported.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the intrinsic finite coefficient tensor
  and internal-Hom operations and canonical scalar realization infrastructure.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparison` and
  its module adjunction; `ProEtale.finiteCoefficientIntrinsicComparison` is its
  existing intrinsic realization, used in the pullback helper.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleIntegral` and the
  underlying `HasProEtaleTorAmplitude`; `Sheaf.Paper.SfIntegralConstructible`:
  `sfIntegralConstructible`, reexported in that predicate.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `Mod`, `D`, `rings`, `ring`,
  `hom`, `duality`, `completionUnit`, `completedTensor`, and their representative
  normalization. These give the ordinary ambient ringed-site tensor over the
  completed coefficient sheaf, as the item requests, and the canonical completed
  tensor comparison. The node's fixed-coefficient derived-tensor record has fixed
  ModuleCat endpoints; the owning integral-operation dependency already supplies
  its intrinsic completed-ring version, so no alternate tensor construction or
  new dependency record is required.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, applied to T.
- The recorded proof-dependency modules are imported non-publicly. They include
  ConstantCompletionEquivalence, AdicResidueLissePerfectLift,
  AdicPerfectModelCompleteReduction, PseudoCoherentBoundedFiniteFreeModel,
  MinimalFreeModel, SiteRestrictionExact, LineEvaluationInversePair, TensorClosed,
  OrdinaryModuleDerivedInternalHom, LineUnboundedDerivedTensor, ProEtaleLisseOrigin,
  IntegralLineTensorComparison, IntrinsicFiniteTorsionConstructibility, and
  ConstructibleTensorCompletion. The Noetherian quasi-separatedness declaration
  is supplied by the already public Mathlib Noetherian import.

Edge cases checked: the empty scheme is allowed throughout; all sheaves and derived
objects are then zero, local line conditions are vacuous, evaluations are isomorphisms,
and every displayed vanishing interval still works. For m=0 the intervals are both
[0,0]; positive and negative m use the usual cochain convention H^i(K[m])=H^(i+m)(K).
No nonempty base, selected geometric point, connectedness, chosen basis or unshifted
residue hypothesis is imposed. Each finite quotient is nonzero over a nonempty base;
the zero complex therefore cannot satisfy the residue-line hypothesis there.

Searches for an existing theorem or notion:

- `msearch.py ... leanfinder`: "A derived complete complex over the completed
  valuation ring whose residue is a shifted rank one local system is a shifted
  line with tensor inverse". Eight unrelated hits (BDeRhamPlus, BDeRham, generic
  shift linearity, adic completion, and single-degree derived objects); no match.
- `msearch.py ... loogle`: `"DerivedComplete", "Invertible"`: zero hits.
- `msearch.py ... grep`: `residueLine|completeResidue|DerivedComplete|derivedComplete`:
  zero Mathlib hits.
- `msearch.py ... leansearch`: "Derived complete complex whose residue is a shifted
  rank one local system is a shifted invertible sheaf": eight general derived
  category, shift and K-injective hits; none states this criterion.
- `rg` of those names and of residue-line terms in `lean/WeilConjectures` and
  `lean/Sheaf`, and search for this blueprint id in `lean/WeilConjectures`: no
  theorem match. Existing line, scalar reduction, duality and completion APIs were
  found and reused. CompleteResidueCohomologyBounds only asserts cohomology bounds.
- Read Bhatt--Scholze pp. 52--54 with pdftotext: Lemma 6.6.8 and the following
  stratified-perfect discussion give the local perfect lifting used in the DAG
  proof. The node already spells out its shifted-line specialization and all
  evaluation, completeness and finite-level consequences.

Validation: the required scompile.py wrapper compiles the single delivered module
in module mode; all variable/universe binders are explicit and autoImplicit is
false. The only theorem proof is sorry. Canonical fixed-universe sheafification
instances simply reuse IntegralOnSlice.abSheafify and abLocallyBijective; they
resolve ambiguous inference of max-universe variables and add no hypothesis.

## Second reading by O4

Performed a separate final pass with the node and Lean file both open, by this
same dispatched worker (the dispatcher explicitly forbids starting other agents).
The maintainer's independent delivery review remains separate.

Matched all hypotheses and every conclusion as listed above. This pass found that
invertibility of the two completion comparisons alone left the final completed
evaluation clause implicit. Added the two actual completed tensor isomorphisms
`e`, `e'` and their compatibility equations with ordinary evaluation. Confirmed
that the dual is the ambient RHom, the evaluations are the normalized counit and
symmetry composite, finite reductions use positive exponents, both amplitude
intervals have the right shift signs, and the empty scheme is not excluded.
No source or node correction is needed. No data definition contains sorry and no
additional theorem was introduced without a DAG node. No new nodes or dependency
modules are part of this delivery.
