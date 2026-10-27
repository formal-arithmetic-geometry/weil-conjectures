## Worker report

The module `Sheaf.RingTheory.GradedNakayamaConnected` states
`GradedAlgebra.nakayama_connected`, with its sole proof `sorry`. It combines the two
clauses of `lem-sfb-graded-nakayama-connected` in the node's order. No definitions,
extra nodes, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/algebra.tex`, lines 13200–13228
(`section-graded`, grading conventions), and 13249–13285 (`lemma-graded-NAK`,
Tag 0EKB, statement and proof). The tags table identifies 0EKB at line 18231.
Parts (4) and (1) give respectively the node's clauses (1) and (2).
The module docstring reproduces the accepted node proof in its five steps,
including the induction on the number of homogeneous generators, the induced
grading on the quotient by their span, and application of clause (2) to that quotient.

Hypothesis and clause correspondence:

- The field `k` is `{k : Type u} [Field k]`.
- The commutative unital `k`-algebra is `{A : Type v} [CommRing A] [Algebra k A]`.
  The universes of `k`, `A`, and `M` are independent and explicitly bound.
- Its nonnegative internal grading by `k`-subspaces is
  `(𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]`. Mathlib's `GradedAlgebra`
  abbreviates `GradedRing`, combining `SetLike.GradedMonoid` (multiplication
  in degree sum and degree-zero identity) with `DirectSum.Decomposition`
  (the inverse to the canonical recomposition map). These are exactly the
  displayed internal direct-sum and multiplicative grading conditions.
- `A₀ = k·1` via the structure map is
  `(hzero : 𝒜 0 = LinearMap.range (Algebra.linearMap k A))`.
  `Algebra.linearMap` is precisely `algebraMap k A` as a linear map, so its
  range is the set of scalar multiples of the identity. No injectivity,
  nontriviality, finite type, or Noetherian condition on `A` is imposed.
- The positive ideal `I = A₊` is Mathlib's existing
  `(HomogeneousIdeal.irrelevant 𝒜).toIdeal`. Its documentation defines it as
  the positive components, equivalently elements with zero degree-zero component.
  `HomogeneousIdeal.irrelevant_eq_iSup` and `irrelevant_eq_span` explicitly
  identify this ideal with the positive components (read lines 563–625).
- The internally integer-graded `A`-module is `{M : Type w} [AddCommGroup M]
  [Module A M]`, `(ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)`.
  The index type is all integers, allowing negative module degrees. Using
  additive subgroups matches the source's internal grading convention.
- Its scalar compatibility is the explicitly bound `hsmul`: for every
  `a : ℕ`, `b : ℤ`, `f : A`, and `m : M`, membership in `𝒜 a` and `ℳ b`
  implies `f • m ∈ ℳ ((a : ℤ) + b)`.
- Finite generation as an ungraded module is `[Module.Finite A M]`.
- `[Module k M] [IsScalarTower k A M]` express the canonical restricted
  `k`-module structure used to take the vector-space span in `M/IM`.
  This is no added mathematical restriction: restricting an `A`-module
  along `algebraMap k A` always supplies it, and the tower forces the action
  to be `c • m = (algebraMap k A c) • m` by evaluation at `1 : A`.
  The quotient's `k`-module structure is Mathlib's induced quotient action.
- Clause (1) quantifies over `r : ℕ` and `x : Fin r → M`.
  `∀ i : Fin r, SetLike.IsHomogeneousElem ℳ (x i)` means each lift lies in
  some component, exactly homogeneity, with no nonzero assumption.
  The hypothesis `Submodule.span k (Set.range (fun i ↦ (I • ⊤).mkQ (x i))) = ⊤`
  is spanning the `k`-vector space `M/IM` by the canonical quotient images.
  The conclusion `Submodule.span A (Set.range x) = ⊤` is generation of `M`
  as an ungraded `A`-module.
- Clause (2) is `(I • (⊤ : Submodule A M) = ⊤ → Subsingleton M)`.
  Ideal multiplication by the full submodule is exactly `IM`.
  `Subsingleton M` expresses that the additive module is zero, including
  the zero module itself. Both clauses are returned as a conjunction;
  the quantified family belongs only to clause (1).

Recorded dependency declarations read and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, lines 169–180,
  including its full declaration and docstring; available through the public imports.
- `def-weil-finitely-generated-module`: `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`, lines 116–120, with its docstring.
  This module is imported publicly and is also the only proof dependency.

Additional API signatures and docstrings read: `GradedAlgebra` and `GradedRing`
in `Mathlib.RingTheory.GradedAlgebra.Basic`; `DirectSum.Decomposition` and
`DirectSum.IsInternal.chooseDecomposition` in
`Mathlib.Algebra.DirectSum.Decomposition`; `DirectSum.IsInternal` in
`Mathlib.Algebra.DirectSum.Basic`; `SetLike.IsHomogeneousElem` in
`Mathlib.Algebra.GradedMonoid`; `Algebra.linearMap` in
`Mathlib.Algebra.Algebra.Defs`; and `Submodule.mkQ` in
`Mathlib.LinearAlgebra.Quotient.Defs`.

Edge cases checked before writing and again on the final signature:

- `r = 0` is admitted. The homogeneity condition is empty; the spanning
  condition says the quotient is zero, and the conclusion says `M = 0`.
- `M = 0` is admitted by all binders and satisfies both clauses.
- Zero lifts are homogeneous and are not excluded.
- `A = k` with its degree-zero grading has `I = 0`; clause (1) becomes
  ordinary vector-space generation and clause (2) says `0 = M` implies `M = 0`.
- Negative module degrees are allowed without a bound assumption.
  Finite generation provides the degree bound in the proof, not in the statement.
- The zero algebra is not excluded; its unital modules are zero. The range
  equality for connectedness still makes sense, with no imposed injection.
- Neither infinitely generated connected algebras (e.g. a polynomial algebra
  in infinitely many variables) nor nonreduced ones (e.g. `k[t]/(t²)`) are
  excluded. No characteristic restriction is present.
- The non-finite graded module `k[t,t⁻¹]` over `k[t]`, where `tM=M` and
  `M≠0`, is correctly excluded by `[Module.Finite A M]`.

Searches actually run using `msearch.py Q125 lem-sfb-graded-nakayama-connected`:

- `leanfinder`: “A finitely generated integer graded module over a connected
  nonnegative graded algebra is zero if the positive ideal times the module
  equals the module; homogeneous lifts of residue generators generate”. Eight
  hits, including `HomogeneousIdeal.irrelevant`, `irrelevant_eq_span`,
  homogeneous localization generation, and finite-type algebra generators;
  no exact graded module Nakayama statement.
- `loogle`: `GradedSMul, DirectSum.IsInternal, HomogeneousIdeal.irrelevant`.
  Zero hits; the service reported unknown identifier `GradedSMul`. This query
  supplied no match; the grading is therefore rendered directly by `hsmul`.
- `grep`: `graded.*[Nn]akayama|[Nn]akayama.*graded|class GradedSMul|def irrelevant`.
  One hit, `HomogeneousIdeal.irrelevant`, in
  `Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.lean:575`.
- `leansearch`: “A finite graded module over a nonnegative graded algebra
  vanishes when the positive degree ideal times the module equals the module”.
  Eight hits, including `GradedAlgebra`, the irrelevant ideal API, and
  `SetLike.gmodule.congr_simp`; no exact Nakayama theorem.
- Direct `rg -n` on `lean/WeilConjectures` and `lean/Sheaf` for
  `graded.*[Nn]akayama|[Nn]akayama.*graded|lem-sfb-graded-nakayama-connected|GradedSMul|HomogeneousIdeal.irrelevant`
  found grading/irrelevant-ideal APIs and the upstream projective-line results.
  I opened `WeilConjectures.RingTheory.GradedNakayamaGeneration` and read
  `MvPolynomial.graded_nakayama_generation` and
  `MvPolynomial.subsingleton_of_graded_quotient_subsingleton`. They restrict
  the ring to `MvPolynomial (Fin 2) k` and cannot serve this node over arbitrary `A`.
  The standard-graded Hilbert function statement also imposes stronger hypotheses.
- Direct search for the node id in `lean/WeilConjectures` returned no matches.
  Name-clash searches for `nakayama_connected|graded_nakayama_connected` in
  `dag/lean_names_upstream.json`, Mathlib, `lean/Sheaf`, and `lean/WeilConjectures`
  returned no matches. No repair note for this item was present.

Validation: the prescribed `scompile.py` compiled the sandbox probe and the library
module successfully (8.9 seconds and 4.1 seconds respectively), without any error
or unexpected warning. `set_option autoImplicit false` enforces explicitly bound
variables. The only node field changed is `lean`; the signature is extracted
verbatim from the delivered module. No statement dispute or source fault was found.

## Second reading by Q125

This is the author's second reading under the direct-delivery protocol; the
maintainer supplies the independent review. I reopened the node statement,
its five proof steps, the two dependency records, the source's graded-ring and
graded-module conventions and parts (4)/(1) of Tag 0EKB, and the delivered signature.

I matched the field, commutative unital algebra, nonnegative algebra grading,
connected degree-zero piece, positive ideal, integer module grading, scalar
compatibility, and ungraded finite generation to the binders listed above.
I checked that the `k`-action is forced by the scalar tower rather than an
unrelated action. Homogeneity quantifies separately over every member of
`Fin r`; the quotient span is over `k`, whereas the conclusion span is over `A`.
The second conjunct has no dependence on a generating family or quotient-spanning
assumption. Its `Subsingleton` conclusion is zero as an additive module, and
`I • ⊤ = ⊤` expresses precisely `IM=M`. In particular `r=0`, `M=0`, negative
degrees and a zero algebra remain admitted. No Noetherian, finite-type,
standard-grading, characteristic, nontrivial-algebra or bounded-below assumption
has entered the signature. I found no mismatch and made no statement change.
The docstring gives the minimum-generator-degree induction first and applies
that result to the graded quotient second, so the proof plan is not circular.
