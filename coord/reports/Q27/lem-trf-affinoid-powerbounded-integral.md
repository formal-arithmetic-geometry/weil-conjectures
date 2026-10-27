## Worker report

The module `Sheaf.RingTheory.AffinoidPowerboundedIntegral` states
`RestrictedSeries.affinoid_powerbounded_integral`. Its single theorem has `sorry`
as its entire proof. There are no new definitions, dependency repairs, statement
corrections, or additional axioms. The item node changes only in `lean`.

I read Bosch, Lectures on Formal and Rigid Geometry (April 2008), Section 1.4,
Theorem 16, printed pp. 28–29, directly in the primary PDF:
https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf .
The equivalence of its spectral, integral-equation and bounded-powers conditions
and its normalization proof agree with the node. The proof uses the original
presentation, and imposes neither reducedness nor algebraic closedness. The
latest blueprint's `lem-trf-local-term-locality` is the contracting-correspondence
statement; this item is the historical analytic prerequisite recorded in the
node's `blueprint.from`, not a change to that blueprint unit.

The following is the hypothesis-by-hypothesis and clause-by-clause translation.

| Node text | Lean rendering |
| --- | --- |
| A field K with a nontrivial rank-one absolute value | `K : Type u` and `[NontriviallyNormedField K]`; the norm takes values in the real numbers, and the class supplies a scalar of norm greater than one. |
| Nonarchimedean and complete K | `[IsUltrametricDist K] [CompleteSpace K]`. |
| V is the valuation ring consisting of scalars of absolute value at most one | `V : ValuationSubring K` and `hV : ∀ a : K, a ∈ V ↔ ‖a‖ ≤ 1`; this identifies V uniquely, rather than allowing an arbitrary valuation ring. |
| Finitely many variables, including zero variables | `r : ℕ` with index type `Fin r`. |
| The Tate algebra is the ring of restricted series with coefficients tending to zero | `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))`, the Mathlib restricted-series subring at polyradius one. |
| A nonzero commutative affinoid K-algebra with its Banach topology | `C : Type v`, `[NormedCommRing C] [Nontrivial C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]`, together with the continuous surjective presentation below. These give a nonarchimedean Banach K-algebra; the quotient-norm topology theorem identifies its topology with the affinoid topology. |
| The presentation q is a K-algebra homomorphism | The ring homomorphism `q`, and `hscalar : q.comp (constants K r) = algebraMap K C`. |
| q is surjective | `hsurj : Function.Surjective q`. |
| q is continuous for the Tate-algebra topology | `hcont` is the epsilon-delta continuity criterion using the Gauss norm of `t.val - s.val` and the given norm of `q t - q s`. The coefficientwise topology on formal power series is not used. |
| An element c with bounded powers for all nonnegative integers m | `c : C` and `hbounded : ∃ M : ℝ, ∀ m : ℕ, ‖c ^ m‖ ≤ M`. This includes m = 0; in a normed space this is the boundedness of the set of powers. |
| c satisfies a monic polynomial of positive degree | `∃ p : Polynomial C, p.Monic ∧ 0 < p.natDegree ∧ p.eval c = 0 ∧ ...`. |
| The polynomial coefficients lie in D = q(V⟨T⟩) for this original q | For every `i : ℕ`, a restricted series `s` lifts `p.coeff i` through this same `q`, and `∀ ν : Fin r →₀ ℕ, MvPowerSeries.coeff ν s.val ∈ V`. |
| No reducedness or algebraic closedness is assumed | There are no `IsReduced C` or `IsAlgClosed K` assumptions. No characteristic or separability assumption is present. |

The conclusion presents the polynomial over D by its image in `Polynomial C`.
This is exactly the same data: every coefficient of p belongs to D by the displayed
lift condition; since D is a subring of C, each coefficient has a unique value as
an element of D. The finitely supported coefficient function therefore descends
to `Polynomial D`, retaining its leading coefficient one, degree, and vanishing.
Conversely, a monic vanishing polynomial over D maps to the displayed p, and its
coefficients have the displayed lifts by the definition of D. Coefficients beyond
its degree are zero and lift by the zero series, so the universal quantifier over
all i adds no restriction. Restricted K-series whose coefficients all lie in V
are precisely restricted V-series: the induced norm on V is the norm in K, and
restrictedness is coefficientwise convergence to zero in the cofinite filter.
Thus no extra helper definition or map is needed.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, supplied by
  `NontriviallyNormedField` through `NormedField`.
- `def-trf-valuation-ring`: `ValuationRing` and `ValuationRing.TFAE` in
  `Mathlib.RingTheory.Valuation.ValuationRing`. The concrete embedded ring uses
  `ValuationSubring` from `Mathlib.RingTheory.Valuation.ValuationSubring`; its
  subtype has the existing `ValuationRing` instance. Thus this is the recorded
  notion with its specified inclusion in K, not another definition.
- `def-trf-restricted-series-presentation`: public import
  `Sheaf.RingTheory.RestrictedSeriesPresentation`; its `RestrictedSeries.constants`
  supplies the canonical scalar map. I read its full declarations, including
  `IsTopologicallyFinitelyPresented`, `IsAffinoidQuotient`, and
  `HasBoundedTopologicallyGeneratedImage`. `IsAffinoidQuotient` requires equality
  of the particular norm with a quotient Gauss norm, whereas the item permits any
  affinoid Banach norm. The statement uses the underlying recorded restricted
  subring and constants, with explicit continuity, as the quotient-norm topology
  dependency itself does; it does not impose that stronger equality.
- The public Mathlib imports supply the existing valuation-subring, normed-algebra,
  polynomial monicity, degree, coefficient and evaluation constructions.

Proof dependencies:

- `lem-trf-affinoid-quotient-norm-topology`:
  `RestrictedSeries.affinoid_quotient_norm_topology` in
  `Sheaf.RingTheory.AffinoidQuotientNormTopology`, imported without `public`.
  Its full signature and docstring were read; the hypotheses use precisely the
  same Banach-algebra and Gauss-continuity encoding as this item.
- `lem-trf-tate-normalization-lift`:
  `RestrictedSeries.tate_normalization_lift` in
  `Sheaf.RingTheory.TateNormalizationLift`, imported without `public`.
  Its full signature and normalization proof docstring were read.
- `lem-trf-affinoid-supremum-seminorm-calculus` and
  `lem-trf-finite-affinoid-spectral-equation` currently have no Lean records or
  Mathlib matches in the read repository. They are proof dependencies only, so
  there are no recorded modules to import. Their uses and all five assembly steps
  are preserved in the theorem docstring. No missing statement dependency occurs.

Edge cases checked before writing:

- r = 0 is allowed. The only multi-index is zero, and restricted series are
  constants; a bounded-powers scalar has norm at most one and satisfies X − c.
- c = 0 satisfies X; c = 1 satisfies X − 1. Both have positive degree and
  coefficients lifting to the integral restricted series.
- For `C = K⟨T⟩/(T²)`, any scalar multiple of the nilpotent class is power-bounded
  (only finitely many nonzero powers), even if its Banach norm exceeds one.
  It satisfies X² = 0, and the statement allows this. Thus the conclusion is not
  silently replaced by a claim about the given norm of c.
- For `C = K × K`, an idempotent satisfies X² − X, and the statement does not force
  C to be a domain or a field.
- The zero algebra is excluded exactly by the node's C ≠ 0. No extra exclusion
  on the number of variables or the characteristic is made.
- Independent universes u and v are explicit; every variable and instance is
  explicitly bound, with both autoImplicit options disabled.
- The condition on hcont is at every source point, not just zero; it is exactly
  continuity in the Gauss metric. Bounded powers are a norm bound, not an
  unsupported arbitrary topological boundedness predicate.

Searches for an existing statement (all performed using the prescribed wrapper
and direct read-only searches; the exact wrapper metadata is in searches.jsonl):

- LeanFinder: “A power bounded element of an affinoid algebra is integral over
  the image of the unit ball of any Tate algebra presentation”. Eight hits,
  including `IsAlmostIntegral`, `PowerBasis.isIntegral_gen`,
  `PowerBasis.repr_pow_isIntegral`, `mem_completeIntegralClosure`, and
  `IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow`. None states
  the analytic affinoid result; almost integrality is a different condition.
- LeanSearch: “Power bounded elements of an affinoid algebra are integral over
  the image of the Tate algebra unit ball”. Eight hits, including `IsIntegral`,
  `IsIntegral.pow`, `IsIntegral.pow_iff`, `IsIntegral.of_pow`, and
  `completeIntegralClosure`; none derives integrality from bounded powers.
- Loogle: `IsIntegral, IsVonNBounded` returned zero hits with unknown identifier
  `IsVonNBounded`. Follow-up `"IsIntegral", "norm"` returned eleven hits on
  algebraic norms, normal extensions, quadratic algebras and scheme normalization;
  none matches the item.
- Mathlib grep: `power.?bounded|[Ii]ntegral.*[Uu]nit[Bb]all|affinoid` in Analysis
  returned no hits. The broader
  `power.?bounded|IsAlmostIntegral|IsIntegral.*(norm|Norm)|integral.*unit.ball`
  returned 25 hits, concerning algebraic norms, normalization, almost integrality,
  and field valuation rings, with no affinoid theorem.
- Read-only `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `power.?[Bb]ounded|affinoid.*integral|[Ii]ntegral.*[Uu]nit[Bb]all` found only
  the Grauert–Remmert theorem and its proof's reference to this still-missing
  item. That theorem is a finiteness result for reduced affinoids over
  algebraically closed K, not this integrality result for arbitrary affinoids.
- `grep -rn "lem-trf-affinoid-powerbounded-integral" lean/WeilConjectures`
  found no declaration. Searching both project roots and `dag/lean_names_upstream.json`
  for `affinoid_powerbounded_integral` found no existing declaration.

No STATEMENT-DISPUTED flag or node fault remains. No source statement was changed.

Validation: the delivered module was checked with the prescribed
`scompile.py Q27 lem-trf-affinoid-powerbounded-integral <module file>` against
published live dependencies. The wrapper returned exit code 0 without errors or
unexpected warnings. The initial compile waited for its server slot; the final
library-file compile itself took 6.2 seconds. All source lines are at most 100
characters. The Lean record signature was extracted verbatim from the module.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
