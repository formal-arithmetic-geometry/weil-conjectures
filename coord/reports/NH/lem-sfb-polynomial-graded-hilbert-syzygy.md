## Worker report

The module `Sheaf.RingTheory.PolynomialGradedHilbertSyzygy` states
`MvPolynomial.exists_graded_free_resolution_finite`, with `sorry` as its whole proof.
It states the node unchanged. There are no new definitions, new nodes, dependency repairs,
or statement corrections.

The previous worker ending concerned an unchanged stage-1 split. The current queue lists
this item at stage 2, its accepted split is reviewed by NK, and it has no Lean record.
This delivery adds its Lean statement and preserves the accepted split.

Source read: `literature/stacks-project/algebra.tex`,
`proposition-finite-gl-dim-polynomial-ring` (Tag 00OQ, lines 27722 onward), and
`lemma-graded-NAK` (Tag 0EKB, lines 13249 onward, including its proof).
The former gives global dimension m; the latter explicitly constructs the graded map
from a direct sum of S(-d_i). As the node correctly says, the finite graded-free
resolution is the extracted consequence, not a verbatim claim of 00OQ.
The declaration docstring carries all five steps of the accepted proof plan and
names the intermediate DAG lemmas. The current blueprint direct-image statement
and proof were also read in `literature/blueprint/latest/`, at
`sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.md` and its `.proof.md` sibling; part (3)
supplies the ambient direct-image context described by the accepted split.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; no characteristic assumption is imposed.
- The nonnegative integer number of variables is `(m : ℕ)`, including zero.
  The polynomial ring S is exactly `MvPolynomial (Fin m) k` throughout.
- The total-degree component S_n is `homogeneousSubmodule (Fin m) k n`, whose
  definition is Mathlib's submodule of homogeneous polynomials of degree n.
  Only n in ℕ is used for scalar compatibility. For negative degrees S_a=0,
  so the missing scalar conditions are automatic from zero scalar multiplication.
- An S-module is `{M : Type v} [AddCommGroup M] [Module S M]`, with u and v
  independent. Its finite generation is exactly `[Module.Finite S M]`.
- The integer-indexed internal decomposition is `(ℳ : ℤ → AddSubgroup M)` and
  `(hℳ : DirectSum.IsInternal ℳ)`. Mathlib defines internality as bijectivity of
  the canonical summation from the direct sum, so both decomposition and uniqueness
  are required. The grading compatibility is `hsmul`, for every homogeneous scalar
  of natural degree n and every element of ℳ_j. Components are k-subspaces as well:
  C(c) is homogeneous of degree zero, so `hsmul 0 j (C c)` closes each subgroup
  under the canonical k-action. No choice of a second k-module action is needed.
- The modules F_0 through F_m are the family `F : Fin (m + 1) → ModuleCat.{u} S`.
  Their gradings are `𝒢 i`, with internality and scalar compatibility stated for
  every i in the first two conjunctions of the conclusion. It is legitimate to
  take these finite free modules in the field's universe u: S and every finite
  power of S live there. This does not restrict the independent universe of M.
- Every finite set I_i is represented up to enumeration by `Fin (r i)` for
  `r : Fin (m + 1) → ℕ`. Empty finite sets are `r i = 0`.
- Every arbitrary integer shift is `d i a : ℤ`. The basis `b i` is an S-basis
  indexed by that finite set, and the third conjunction says its a-th vector lies
  in degree `-(d i a)`. This is exactly F_i = direct sum of S(d_i,a): the element
  1 of S(d) is in degree -d since S(d)_j = S_(d+j). Scalar compatibility and
  uniqueness of homogeneous decomposition imply that the basis identification
  from the shifted sum is graded in both directions. Conversely the standard
  bases of those shifted sums have precisely these degrees. Thus a finite
  homogeneous basis expresses the requested shifted-free objects, as in the
  existing upstream two-variable syzygy statement; it does not merely assert
  ungraded freeness or introduce a second shift construction.
- The degree-preserving S-linear maps F_(j+1) → F_j are `f j hj`, for every
  natural j with `hj : j < m`. Their sources and targets are indexed explicitly
  by `⟨j+1, Nat.succ_lt_succ hj⟩` and `⟨j, Nat.lt_succ_of_lt hj⟩`.
  The fourth conjunction states that every one of these maps preserves every
  integer degree. The augmentation is `q : F 0 →ₗ[S] M`, and the fifth
  conjunction states its preservation of every degree.
- Left-end injectivity for m>0 is
  `∀ j hj, j + 1 = m → Function.Injective (f j hj)`.
  For m=0 it is the separate clause `m = 0 → Function.Injective q`.
- Exactness at F_0 when m>0 is
  `∀ h : 0 < m, LinearMap.range (f 0 h) = LinearMap.ker q`.
  For every higher interior F_(j+1), the next clause is
  `LinearMap.range (f (j+1) hj) = LinearMap.ker (f j (Nat.lt_of_succ_lt hj))`,
  for `hj : j+1 < m`. This covers all remaining image-kernel equalities,
  including the one immediately to the right of F_m. No map is skipped.
- Exactness at M is `Function.Surjective q`, the last conjunction.
  When m=0 the other map-index types are empty; the two endpoint clauses say
  q is bijective, hence an S-linear isomorphism F_0 → M as required. Its inverse
  preserves degree by the internal decompositions and degree preservation of q.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, read in `Mathlib.Algebra.Field.Defs`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`, the recorded declaration. The recorded
  universal-property declarations `MvPolynomial.aeval` and
  `MvPolynomial.algHom_ext` were read in Eval and Basic respectively; the
  statement needs only the polynomial ring itself.
- `def-weil-finitely-generated-module`: `Module.Finite`, read and imported from
  `Mathlib.RingTheory.Finiteness.Defs`.
- Mathlib's `DirectSum.IsInternal` (Basic, publicly exported by Decomposition),
  `MvPolynomial.homogeneousSubmodule` (Homogeneous), `Module.Basis` (Basis.Defs),
  and `ModuleCat` (ModuleCat.Basic) express the internal grading and finite
  homogeneous free modules, following the upstream syzygy theorem's interface.
- Proof dependencies with a usable declaration are imported privately:
  `MvPolynomial.isRegularRing_of_isRegularRing` from
  `Mathlib.RingTheory.RegularLocalRing.Polynomial`, `Submodule.FG.of_le` from
  `Mathlib.RingTheory.Noetherian.Basic`, `Module.Projective` from
  `Mathlib.Algebra.Module.Projective`, and the recorded
  `ModuleCat.projective_kernel_of_partial_projective_resolution`,
  `ModuleCat.projective_of_exact_partial_projective_resolution`, and
  `ModuleCat.projective_of_projective_resolution_length_zero` from
  `WeilConjectures.RingTheory.ProjectiveResolutionKernelProjective`.
- At inspection, proof-only nodes `lem-sfb-polynomial-projective-dimension-bound`
  and `lem-sfb-connected-graded-projective-free` have neither Lean nor Mathlib
  declarations. They are not needed to type this statement. Their future modules
  can be inserted as private proof imports when stated, under the stage-2 rule;
  this delivery does not replace them by additional hypotheses.

Edge cases checked mathematically before writing:

- m=0: no differential f exists, no interior exactness is imposed, and q is
  both injective and surjective. A finite graded vector space has a finite
  homogeneous basis, so this covers arbitrary grading degrees over S=k.
- M=0 and all r_i=0: every F_i is zero and every endpoint and exactness clause
  holds, for every m including zero. There is no Nonempty constraint on a basis.
- m=1, M=k concentrated in degree zero: the familiar sequence
  0 → S(-1) → S → k → 0 has its left map multiplication by x; the basis
  in S(-1) has degree 1. This tests the shift sign and the final exactness clause.
- M=S(3): its basis has degree -3, so d=3. Positive shifts and negative generator
  degrees are retained. The analogous check with a negative shift also works.
- m=2: the indices yield f_1:F_2→F_1, f_0:F_1→F_0, q:F_0→M;
  the conjunctions are precisely injectivity of f_1, range f_1=ker f_0,
  range f_0=ker q and surjectivity of q, matching the existing two-variable API.
- A zero intermediate kernel allows all subsequent ranks to be zero; length
  less than m is allowed by this zero padding, exactly as in the node.

Searches actually run:

- `msearch.py ... leanfinder` with query
  "A finite graded module over a polynomial ring in m variables over a field has
  a finite graded free resolution of length at most m": eight hits, including
  `MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite`, the
  corresponding restricted-degree finite instance, a finite-field polynomial
  finite-dimensionality instance, `Ideal.is_fg_degreeLE`,
  `HomogeneousLocalization.Away.finiteType`, `instFinitePresentationForall`,
  `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`, and
  `HomogeneousLocalization.Away.span_mk_prod_pow_eq_top`. None states a resolution.
- `msearch.py ... loogle 'MvPolynomial, "resolution"'`: OK, zero hits.
- `msearch.py ... grep 'Hilbert.syzygy|graded.*free.*resolution|graded.*projective.*free'`:
  OK, zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for graded resolutions and
  Hilbert syzygy found `WeilConjectures.RingTheory.GradedSyzygy`, whose
  `MvPolynomial.exists_graded_free_resolution_two` is restricted to Fin 2.
  Its complete statement and proof were read, together with GradedFreeCover
  and GradedKernelInternal. They are not the arbitrary-m assertion of this item.
  The projective-space resolution files concern sheaf resolutions instead.
- The prescribed upstream grep for the item's exact DAG id returned no hit.
  A declaration-name search for `exists_graded_free_resolution_finite` across
  Mathlib, upstream and Sheaf returned no hit before writing this module.
  The upstream names index was also searched for graded-free-resolution names.

There are no disputed statements or discovered node faults. All variables and
universes are explicitly bound; no auto-bound implicit is relied on.

Validation: `scompile.py NH lem-sfb-polynomial-graded-hilbert-syzygy` compiled the
module on the server against the published live build, in sandbox mode and at
its library module path, with no errors or unexpected warnings (8.7 s and 7.4 s).
The required `deliver2.py --no-push` dry run passed server preflight and compilation
(commit eae97a42b38, nothing pushed). A local read-only comparison confirms that
the node changes only in `lean`; the file has one theorem and one `sorry`, with
no Lean line exceeding 100 characters.
The independent mathematical review is the maintainer's; no second worker was
started, in accordance with this dispatch's instructions.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
