## Worker report

The delivery states the affine compact-support upper bound, with a single postponed theorem
`AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology_affineCurve_upper`. No mathematical assertion is proved.
The node statement is unchanged. The current main-20261015 blueprint statement is identical
to the master statement named by the node's source.

Hypotheses and clauses, read against the node:

* `k₀ : Type u`, `[Field k₀]`, `[Finite k₀]` fix the finite base field; `l : ℕ`,
  `[Fact l.Prime]`, and `[Fact (ringChar k₀ ≠ l)]` impose precisely the coefficient-prime
  convention. `[Fact (Nat.Prime (ringChar k₀))]`, `a : ℕ`, `ha : 1 ≤ a`, and
  `hcard : Nat.card k₀ = ringChar k₀ ^ a` spell out p=char(k₀) and q=p^a of the
  standing setup; every finite field has exactly such a positive exponent. These
  parameters identify the q used in the existing filtration predicate with #k₀.
  `ι : PadicAlgCl l ≃+* ℂ` is the coefficient-field isomorphism fixed in
  `rem-dl-a1-conventions` of this chapter. This is an abstract field isomorphism, without
  continuity assumptions. The algebraic closures are the canonical existing models;
  the assertion is invariant under their field isomorphisms.
* `C₀ : Scheme.{u}` and `[C₀.Over (Spec (CommRingCat.of k₀))]` give the curve over the base.
  `[IsAffine C₀]` gives affineness. `[SmoothOfRelativeDimension 1 ...]` gives smoothness
  and dimension one. `[GeometricallyConnected ...]` gives connectedness after algebraic
  closure, including nonemptiness. The separated, locally-finite-type and quasi-compact
  structure-morphism instances spell out the standing curve convention in d-real-setup.
* `F : WeilSheaf k₀ l C₀` is a constructible Qlbar-Weil sheaf on the geometric curve;
  `hF : F.IsLisse` imposes lissity, and
  `hpure : F.IsPunctuallyPureOfWeight ι.toRingHom w` imposes punctual purity of real weight w.
* The first conjunct quantifies over every integer `i` and uses the recorded
  `FrobeniusModule.IsMixedOfWeightsAtMost (ringChar k₀) a l ha ...` on
  `F.compactlySupportedCohomology i`, with bound `w + i`. The coefficient closure
  proof is the existing algebraic-closure instance. Its prime inequality is the
  symmetry of the standing `[Fact (ringChar k₀ ≠ l)]`. This uses the finite stable
  pure-quotient filtration exactly as stated in def-weil-frobenius-module-weights.
  The cardinality is p^a=#k₀, not a residue cardinality. The zero module admits
  the allowed length-zero filtration, and no semisimplicity is imposed.
* The second conjunct is `Subsingleton (F.compactlySupportedCohomology 0).carrier`, the
  equality H_c^0=0 for its underlying vector space.
* The third conjunct uses `IsPureOfWeightOver k₀ ... (w + 2)` in degree two.
* The last conjunct is `∀ i : ℤ, i < 0 ∨ 2 < i → Subsingleton ...`, exactly the
  degrees outside {0,1,2}; it includes every negative degree.

Dependency interfaces read and imported:

* `Sheaf.Paper.RealSheavesSetup`: `RealSheaves.Setup`, its `IsCurve`, geometricCurve,
  field choices and Frobenius conventions. The signature spells out the corresponding
  geometric hypotheses, as the existing upstream compact-cohomology API requires them.
* `Sheaf.Paper.LisseAdicSheaves`: `Scheme.LisseIntegralSheaf`, `LisseRationalSheaf`, and
  `LisseAlgebraicSheaf`. The used predicate is the upstream `WeilSheaf.IsLisse`, on the
  underlying adic sheaf, which is pro-etale locally finite free; this is the same lisse
  notion, in the upstream adic realization rather than a newly defined sheaf category.
* `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilSheaf`, and their common-stage
  versions. Its repair distinguishes fixed pairs of constructible complexes from the
  derived category of Weil sheaves. The item only quantifies over Weil sheaves in the
  heart, represented by the existing `AlgebraicGeometry.WeilSheaf` on the pro-etale site;
  it makes no assertion identifying the two derived categories or their Ext groups.
* `Sheaf.Paper.OrdinaryCompactCohomology`: `qbarWeilSheafCohomology` computes coefficient
  cohomology after forgetting the Weil structure. The upstream
  `WeilSheaf.compactlySupportedCohomology` additionally retains the induced geometric
  Frobenius on that cohomology. It is used here because the conclusion concerns
  Frobenius weights; no arbitrary operator is supplied as a hypothesis.
* `WeilConjectures.DeligneLaumon.Reduction.Weights`: recorded
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`, defined in its transitive
  dependency `WeilConjectures.WeilSheaf.Stalk`, and `IsMixedOfWeightsAtMost`.
* `Sheaf.LinearAlgebra.FrobeniusModuleWeights`:
  `FrobeniusModule.IsMixedOfWeightsAtMost` is used literally for the upper bound.
  Its module identifies the upstream `FrobeniusModule.IsPureOfWeight` as the purity
  predicate; the degree-two clause uses its `IsPureOfWeightOver` specialization
  from `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule` at q=#k₀.

Edge cases checked: F=0 (all upper bounds and purity vacuous), H_c^2=0 (purity still
vacuous), constant sheaf on A^1 (degree two is Qlbar(-1), weight w+2), negative i,
and arbitrary real w. No positive rank is assumed. Empty and zero-dimensional schemes
are excluded by the geometrically connected smooth relative-dimension-one hypotheses,
not by any extra conclusion. No diagonalizability or semisimplicity is assumed.

Proof dependencies with recorded declarations are imported non-publicly, including
finite-map enlargement, the open-closed triangle, compact-support functoriality,
positive-degree finite-boundary vanishing, the boundary sequence, semicontinuity,
the affine-line bound, mixed subquotient and extension bounds, constant-extension
weight descent, characteristic-polynomial factorization, and invariant flags.
The long exact cohomology sequence is imported from the Mathlib leaf
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
Proof nodes without recorded statements are described in the proof docstring and
will be imported by the maintainer when their statement modules land.

Searches:

* msearch LeanSearch: "A smooth geometrically connected affine curve with a pure lisse
  Weil sheaf has compactly supported cohomology mixed of weights at most w plus the
  degree." returned eight unrelated affine Weierstrass-curve hits, no match.

* msearch LeanFinder: "affine smooth geometrically connected curve compactly supported
  cohomology weights at most" returned unrelated Mathlib height/weight and elliptic-curve
  hits, no existing compact-support theorem.
* msearch Loogle: "compactlySupportedCohomology, HasWeightsAtMostOver, IsPureOfWeightOver"
  returned zero hits (unknown Mathlib identifier compactlySupportedCohomology).
* msearch grep: "affineCurveUpper|compactlySupportedCohomology.*HasWeightsAtMost" returned
  zero hits. Direct rg over the upstream WeilConjectures tree and project lean/Sheaf found
  the curve endpoints, cohomological range and the affine-line/projective-line bounds,
  but no theorem containing the four clauses for an arbitrary smooth affine curve.
* `dag/lean_names_upstream.json` lists
  `AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine_of_isLisse`.
  (Corrected by the maintainer's reviewer: this declaration is present in the live published
  library, `WeilConjectures/DeligneLaumon/Reduction/AffineCurve.lean` line 217, tagged
  `(blueprint: thm-a1-affine-curve-upper)`; the earlier sentence calling it absent was wrong.)
  It is not used as an `existing` record because it does not state the node through the
  recorded dependency notions. Its first clause is the eigenvalue predicate
  `FrobeniusModule.HasWeightsAtMostOver`, whereas the node's "weights at most w+i" is
  def-weil-frobenius-module-weights, recorded as the finite stable-filtration predicate
  `FrobeniusModule.IsMixedOfWeightsAtMost`. The two agree over the algebraically closed
  coefficient field only after a triangularization argument, which is exactly the last
  proof step of the node (p-linear-triangular). The degree-zero, degree-two and range
  clauses coincide with the upstream ones, and the upstream theorem has weaker hypotheses
  (a ring map ι, no separated or quasi-compact instance). Stage 3 can therefore prove this
  statement from the upstream theorem plus the eigenvalue-to-filtration conversion.

No new nodes, dependency-record repair, or statement correction is made. The mathematical
statement is not disputed. Compilation is performed through the prescribed scompile.py
wrapper; the delivery dry run checks the exact packet again.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
