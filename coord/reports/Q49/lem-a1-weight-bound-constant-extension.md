## Worker report

This is an `existing: true` delivery. The existing declaration is
`FrobeniusModule.HasWeightsAtMost.of_powFrobenius` in
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact`, under the
`FrobeniusModule` namespace. Its docstring explicitly identifies
`lem-a1-weight-bound-constant-extension`. No Lean module is added, no proof is
written, and only the item's `lean` record is changed.

I read the item and its proof, the entire statement and Lean record of
`def-weil-frobenius-module-weights`, that dependency's current module through
`scompile.py --source Sheaf.LinearAlgebra.FrobeniusModuleWeights`, and the
current upstream Frobenius-module definitions and Exact module through the
same source wrapper. The Exact module is absent in the older slopmaster2
checkout but present in the shared source tree and in the live source returned
by the wrapper. These two available copies agree on the declaration's signature.
The immutable upstream-name index also associates this exact declaration with
the item. No repair note for the item was found in `coord/repair-notes`.

The blueprint source was checked in both snapshots: master, node order 2802,
and main-20261015, node order 3146 with its separate proof file. Their statements
and arguments agree. There is no statement correction or statement dispute.

### Hypotheses and clauses

- The coefficient field is the algebraic closure `Qlb` of `ℚ_[ell]` with the
  primes `p`, `ell`, `ell ≠ p`, and positive exponent `a` supplied by
  `def-weil-frobenius-module-weights`. The upstream theorem has the explicitly
  bound section parameter `{K : Type v} [Field K]`. Its instance here is
  `K := Qlb`; this preserves every coefficient field allowed by the node.
  The existing result is stated over any field, so it requires no additional
  property of this particular algebraic closure.
- The finite-dimensional vector space and its linear automorphism `(V,F)` are
  precisely `{M : FrobeniusModule.{u,v} K}`. The structure's `carrier`,
  `addCommGroup`, `module`, `finiteDimensional`, and `frobenius` fields give
  those data. The carrier and coefficient universes are separate; no universe
  equality or additional size restriction is imposed.
- The fixed field isomorphism `iota : Qlb ≃+* ℂ` is used as
  `(iota : Qlb →+* ℂ)` for the parameter `{ι : K →+* ℂ}`. This forgets no
  condition required for applying the theorem to the node's `iota` and imposes
  no continuity assumption.
- The prime power is the parameter `q := p ^ a`. The base fields
  `k₀ = F_q` and `k₀' = F_(q^m)` enter this linear-algebra statement solely by
  their cardinalities and the replacement of Frobenius by its `m`-th power.
  Both are represented literally by `q ^ m` and `M.powFrobenius m` in the
  hypothesis. No geometric comparison or field morphism is asserted by this
  node. The existing theorem is the numerical version of this very descent
  assertion; it also applies beyond the stated prime-power coefficient setup.
- The finite extension degree is `{m : ℕ}` with `(hm : m ≠ 0)`. A genuine
  finite field extension has positive degree, so this is already implicit in
  the source, including the degree-one identity extension.
- The real weight parameter is `{b : ℝ}`, with no integrality, sign, or
  rationality restriction.
- The hypothesis on every eigenvalue of `F^m` is
  `(h : (M.powFrobenius m).HasWeightsAtMost ι (q ^ m) b)`.
  The definition expands to
  `∀ λ, (M.powFrobenius m).frobeniusEnd.HasEigenvalue λ →
    ‖ι λ‖ ≤ ((q ^ m : ℕ) : ℝ) ^ (b / 2)`.
  `powFrobenius` has the original carrier and `frobenius := M.frobenius ^ m`;
  `powFrobenius_frobeniusEnd` identifies its endomorphism with `F^m`.
- The conclusion on every eigenvalue of `F` is `M.HasWeightsAtMost ι q b`,
  expanding to `∀ α, M.frobeniusEnd.HasEigenvalue α →
    ‖ι α‖ ≤ (q : ℝ) ^ (b / 2)`.

For the last two clauses the norm is nonnegative and the cardinality `r` is
positive (`r = q` or `q^m`). Thus
`(r ^ (b/2))^2 = r^b` and squaring is order-reflecting on nonnegative reals.
Consequently `‖ι α‖ ≤ r^(b/2)` is equivalent to the node's
`|ι(α)|^2 ≤ r^b`, for every real `b`, including negative and zero values.
This is exactly the normalization used in the existing theorem's docstring;
no mixedness claim is substituted for an eigenvalue bound.

### Dependency declarations and proof correspondence

The recorded dependency module is
`Sheaf.LinearAlgebra.FrobeniusModuleWeights`, with main declaration
`FrobeniusModule.IsMixedOfWeightsAtMost`. I read its entire definition. It
publicly imports `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule` and uses
its `FrobeniusModule.IsPureOfWeight` for the stable-filtration quotients.
The current item refers to the same coefficient setup and Frobenius-module
objects but assumes and concludes only eigenvalue inequalities; it does not
assume or conclude that mixed-filtration predicate. Accordingly its existing
upstream theorem uses `FrobeniusModule.HasWeightsAtMost` (the eigenvalue
predicate), not a replacement definition of mixedness. No dependency repair
or additional notion is needed. The common declarations actually involved are
`FrobeniusModule`, `FrobeniusModule.frobeniusEnd`, and
`FrobeniusModule.HasWeightsAtMost` from the upstream base module, together
with `powFrobenius` from the Exact module. Eigenvalues are Mathlib's
`Module.End.HasEigenvalue`, whose definition and nonzero-eigenvector
characterization were read in `Mathlib.LinearAlgebra.Eigenspace.Basic`.

The existing proof follows the node: `hasEigenvalue_powFrobenius` sends an
`F`-eigenvalue `α` to an `F^m`-eigenvalue `α^m`; the assumption bounds the
norm of this power; `map_pow` and `norm_pow` give the `m`-th power of the
original norm. The real-power identities exchange the two exponents, and
`pow_le_pow_iff_left₀` with `m ≠ 0` recovers the original bound. This is the
node's argument in the equivalent unsquared normalization. No existing proof
was changed or duplicated.

### Edge cases

- Zero-dimensional `V`: neither operator has an eigenvalue, so both universally
  quantified bounds are vacuous, as the source requires.
- `m = 1`: this includes the identity constant extension and the bound is
  unchanged.
- `m = 0`: excluded by genuine extension degree. The exclusion is necessary:
  `F^0 = 1` would satisfy the upper bound for every `b` because the base is
  `q^0 = 1`, while `F` could have an eigenvalue violating the proposed bound.
- `b = 0` or `b < 0`: the equivalence by squaring still holds since `q > 0`;
  no positivity of `b` is used.
- A nonsemisimple Jordan block: the theorem uses genuine eigenvectors and
  powers, not diagonalization; no semisimplicity assumption appears.
- A scalar module at the bound has equality before and after extension.
- `q = 0` and `q = 1` are outside the node's prime-power setup (`p` prime,
  `a ≥ 1`). Their availability in the general upstream theorem places no
  restriction on the source's cases; the squared-norm comparison above is
  used only at the source's positive `q`.

### Searches

The prescribed `msearch.py` searches were run for this group and item; their
raw outputs are retained in the sandbox's `searches.jsonl`.

- LeanFinder: `Frobenius module upper weight bound descends from a positive
  power of Frobenius and constant field extension` returned eight unrelated
  purely inseparable/Frobenius/isocrystal results, no matching weight theorem.
- Loogle: `FrobeniusModule.HasWeightsAtMost.of_powFrobenius` returned zero hits,
  reporting that the identifier is unknown to the Mathlib search index.
- Mathlib grep: `HasWeightsAtMost|powFrobenius|FrobeniusModule` returned zero hits.
- LeanSearch: `A bound on the absolute values of eigenvalues of the m-th power
  of an automorphism descends to a weight bound for the automorphism` returned
  eight hits, led by `Module.End.HasEigenvalue.pow`; that is a constituent
  eigenvalue result rather than the complete statement.
- Direct `rg` of the source repository for the item id and
  `HasWeightsAtMost.of_powFrobenius` found no match in the older checkout.
  Searching its Frobenius-module definitions found the eigenvalue weight
  predicate; searching `lean/Sheaf` found no duplicate descent theorem.
- `rg` of `dag/lean_names_upstream.json` found the exact theorem attached to
  this item. A direct `rg` of shared `lean/WeilConjectures` for
  `of_powFrobenius|powFrobenius` found the Exact module's construction,
  eigenvalue-power lemma, and descent theorem. The live source wrapper then
  confirmed their full signatures, definitions, docstrings and proof.

### Validation

The delivery wrapper checks the existing declaration by compiling an import
and `#check @FrobeniusModule.HasWeightsAtMost.of_powFrobenius` through
`scompile.py`. No new statement module requires compilation. The prescribed
dry run and push perform this check and the server preflight.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
