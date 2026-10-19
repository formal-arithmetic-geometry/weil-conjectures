## Worker report

The module `Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed` states
`FrobeniusModule.isMixedOfWeightsAtMost_of_forall_hasEigenvalue`, with its entire proof
postponed by `sorry`. It proves no auxiliary results and introduces no definitions.
The node is unchanged outside `lean`.

Clause-by-clause correspondence:

- The coefficient conventions inherited through “in the sense of
  def-weil-frobenius-module-weights” are explicit: `(p a ell : ℕ)`,
  `[Fact (Nat.Prime p)]`, `(ha : 1 ≤ a)`, `[Fact (Nat.Prime ell)]`, and
  `(hellp : ell ≠ p)`. The fixed cardinality `q` is exactly `p ^ a`.
- The algebraic closure of the ell-adic numbers is `(Qlb : Type v) [Field Qlb]
  [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)`.
  `(iota : Qlb ≃+* ℂ)` is a field isomorphism with no continuity condition.
- The finite-dimensional Frobenius module `(V,F)` is
  `(M : FrobeniusModule.{u, v} Qlb)`. Reading the upstream structure confirms that
  it bundles the carrier, additive group, scalar action, finite dimensionality, and
  a linear automorphism `M.frobenius`. The independent universes `u v` are declared.
- The real upper weight is `(w : ℝ)`, with no integrality or nonnegativity restriction.
- “Every eigenvalue alpha” is `∀ α : Qlb, M.frobeniusEnd.HasEigenvalue α → ...`.
  Mathlib's `Module.End.HasEigenvalue` means a nonzero eigenvector, as required by
  the dependency node. `frobeniusEnd` is the underlying linear endomorphism of F.
- The bound is exactly `‖iota α‖ ≤ ((p ^ a : ℕ) : ℝ) ^ (w / 2)`:
  the complex norm is complex absolute value, and the exponent is a real power.
- The entire conclusion is the recorded dependency predicate
  `IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w`.
  Its full source was read locally and again through `scompile.py --source`.
  It requires a finite increasing filtration with zero and whole endpoints,
  `Submodule.map M.frobenius.toLinearMap (V r) = V r`, and every successive
  quotient pure of some real weight at most `w`. The quotient automorphism must
  agree with F on quotient classes; it is not arbitrary. No semisimplicity is assumed.

Dependency declarations used:

- `Sheaf.LinearAlgebra.FrobeniusModuleWeights`,
  `FrobeniusModule.IsMixedOfWeightsAtMost` (the statement dependency's recorded declaration).
  The module is publicly imported.
- Via that module: `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule`,
  `FrobeniusModule`, `FrobeniusModule.frobeniusEnd`, and
  `FrobeniusModule.IsPureOfWeight`; Mathlib's `Module.End.HasEigenvalue`, padic
  numbers, `IsAlgClosure`, complex norm, and real power are reused.
- The proof dependency `lem-a1-spectrum-exact-sequence` has no Lean record or
  Mathlib match in the DAG read for this delivery, so no proof import is available.
  Its use is stated explicitly in the proof docstring. It is not a prerequisite
  for typing the present theorem, and no dependency statement is duplicated.

The full proof docstring follows the node's Jordan–Holder argument, explains why
simple quotients are lines, cites exact-sequence spectra, and uses nonvanishing
and `q > 1` to assign the logarithmic real weights. The current main-20261015
blueprint statement was compared with the recorded master statement: they agree.

Edge cases checked mathematically before writing:

- For the zero space the eigenvalue hypothesis is vacuous and the definition
  allows the length-zero filtration, so the conclusion still has its intended meaning.
- A one-dimensional scalar automorphism with eigenvalue c has c nonzero; its
  real weight is `2 * log ‖iota c‖ / log (p ^ a)`. The norm bound is equivalent
  to that weight being at most w, including equality at the boundary.
- A nonsemisimple Jordan block has a stable flag with one-dimensional quotients;
  no diagonalizability or stable complementary subspace is required.
- Distinct eigenvalue moduli can give different quotient weights; the conclusion
  permits this. Negative and arbitrary nonintegral w are retained.
- `p` prime and `a ≥ 1` give `p ^ a > 1`; the problematic cardinalities 0 and 1
  are excluded by the inherited coefficient definition, not by an extra hypothesis.
- Ell is prime and different from p, as in the dependency. Coefficient and carrier
  universes remain independent; no equality between them is imposed.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “finite dimensional Frobenius module eigenvalues
  norm bound implies mixed weights at most”: eight unrelated results (root systems,
  field norm bounds, Lie weights, generalized eigenvalues), no filtration theorem.
- `msearch.py loogle`, query `Module.End.HasEigenvalue`: twelve eigenvalue-definition
  and eigenvector results, including the exact eigenvalue predicate used, but no
  theorem concluding the mixed stable-filtration predicate.
- `msearch.py grep`, query `hasWeightsAtMost|FrobeniusModule`: zero Mathlib hits.
- Direct `rg` of the upstream project for the item id and the advertised
  `hasWeightsAtMost_of_forall_hasEigenvalue` gave no local result because the old
  checkout lacks the Exact module. `scompile.py --source
  WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact` supplied the full current
  module. Its same-blueprint-tagged theorem concludes `M.HasWeightsAtMost ι q w`,
  whose definition is exactly the original eigenvalue bound. It does not conclude
  `IsMixedOfWeightsAtMost` and therefore is not an exact existing match. The
  historical closed audit does not justify binding the node to that tautology.
- Direct `rg` of `WeilConjectures`, `lean/Sheaf`, and the upstream-name index for
  `IsMixedOfWeightsAtMost` / mixed-eigenvalue combinations found sheaf and complex
  mixedness interfaces and the existing module-weight definition, but no theorem
  concluding its finite stable-filtration predicate. A focused search under
  `ZetaLinearAlgebra` and `lean/Sheaf/LinearAlgebra` confirmed this distinction.
- The dependency module's full published source was retrieved with
  `scompile.py --source Sheaf.LinearAlgebra.FrobeniusModuleWeights`; it agrees
  with the source inspected locally. No duplicate notion or dependency repair is needed.

No statement correction, dispute, new node, or dependency module is required.
The module is checked using the prescribed `scompile.py` wrapper; delivery preflight
and its per-file compile are run through `deliver2.py`.

## Second reading by Q43

The delivered section contained only "No second reading by a worker". This section replaces it;
it was written by the maintainer's independent reviewer (cc review service, 2026-10-17) with the
node, the blueprint source and the Lean file open. Nothing in the Lean module or the node was changed.

Node statement (master order 2788; identical text in main-20261015 and main-20261017), item by item:

1. Coefficient data "in the sense of def-weil-frobenius-module-weights": p prime, a >= 1, q = p^a,
   ell prime with ell != p, Qlb an algebraic closure of Q_ell, iota : Qlb -> C a field isomorphism
   without continuity. Lean: `(p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a) [Fact (Nat.Prime ell)]
   (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb] [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
   (iota : Qlb ≃+* ℂ)`. Exactly the binders of `FrobeniusModule.IsMixedOfWeightsAtMost`; nothing extra. Correct.
2. A finite-dimensional Qlb-Frobenius module (V,F). Lean: `(M : FrobeniusModule.{u, v} Qlb)`; the upstream
   structure (WeilConjectures.ZetaLinearAlgebra.FrobeniusModule, line 58) bundles carrier, module structure,
   `FiniteDimensional` and a linear automorphism `frobenius`. Universes u (carrier) and v (field) are
   independent, as in the dependency. Correct.
3. The real number w. Lean: `(w : ℝ)`, unrestricted (negative and non-integral allowed). Correct.
4. Hypothesis: every eigenvalue alpha of F satisfies |iota(alpha)| <= q^{w/2}. Lean:
   `∀ α : Qlb, M.frobeniusEnd.HasEigenvalue α → ‖iota α‖ ≤ ((p ^ a : ℕ) : ℝ) ^ (w / 2)`. `frobeniusEnd` is
   `M.frobenius.toLinearMap`; `Module.End.HasEigenvalue` is the nonzero-eigenvector notion fixed in the
   dependency node; the complex norm is the absolute value and `^` is the real power of the positive real q,
   with q cast exactly as in `IsPureOfWeight`. Not stronger, not weaker. Correct.
5. Conclusion: (V,F) is iota-mixed of weights at most w. Lean: `IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ
   iota M w`, the recorded declaration of the statement dependency (Sheaf.LinearAlgebra.FrobeniusModuleWeights),
   with the same q = p^a. Correct.

Edge cases: V = 0 (hypothesis vacuous; the m = 0 filtration is allowed by the dependency definition);
one-dimensional scalar c (c != 0 since F is invertible; weight 2 log|iota c| / log q <= w, equality case
included); a non-semisimple Jordan block (stable flag, no semisimplicity required); distinct eigenvalue moduli
(different quotient weights permitted); q > 1 is guaranteed by p prime and a >= 1 without an extra hypothesis.
The statement is true as stated.

Searches: rg for `IsMixedOfWeightsAtMost`, `hasWeightsAtMost_of_forall` and `isMixed.*Eigenvalue` in the side
clone lean/, weil-newtargets/lean and slopmaster2: only the sheaf/complex-level `WeilSheaf.IsMixedOfWeightsAtMost`
API and `WeilGroup.hasWeightsAtMost_of_forall_mem_range`, neither about Frobenius modules. The upstream
`FrobeniusModule.hasWeightsAtMost_of_forall_hasEigenvalue` concludes `HasWeightsAtMost` (the eigenvalue bound
itself), not the filtration predicate, so it is not an existing match. One definition per notion holds.

Gates: no definitions introduced; the only declaration is the theorem with body `sorry`; module and theorem
docstrings carry the source place and `(blueprint: lem-a1-punctual-bound-module-mixed)`; the theorem docstring
follows the node's Jordan–Holder proof step by step and names lem-a1-spectrum-exact-sequence; `lean.statement`
in the node is verbatim the signature in the file; the node differs from the base only in `lean`; no pro-etale
notion is involved.

Compile: `nt_compile.py` (per-file, side overlay) on the delivered file: clean, no error and no warning,
2.6–2.8 s; a negative control with an appended false `example` was rejected with an error, so the clean
result is meaningful.

Mismatches found: none in the Lean or the node. Changed: only this section (delivery-errors H11).
