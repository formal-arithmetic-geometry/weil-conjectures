## Worker report

The module states `AlgebraicGeometry.effective_cartier_affine_dimension_drop`. The field `k`,
`[Field k]`, renders the field hypothesis; `A`, `[CommRing A]`, and `[Algebra k A]` render the
commutative `k`-algebra; `[Algebra.FiniteType k A]` renders finite generation; `hA : IsDomain A`
renders integrality of the affine scheme; `f : A`, `hf0 : f ≠ 0`, and `hfu : ¬ IsUnit f` render the
principal nonzero nonunit. The quotient is `A ⧸ Ideal.span ({f} : Set A)`, and the conclusion is
the well-typed successor equation
`topologicalKrullDim (Spec (A ⧸ (f))) + 1 = topologicalKrullDim (Spec A)`.
This is equivalent to the stated dimension drop, while subtraction is unavailable on
`WithBot ℕ∞`, the codomain of Mathlib's `topologicalKrullDim`.

The statement uses Mathlib declarations `AlgebraicGeometry.Spec`, `Algebra.FiniteType`,
`IsDomain`, `Ideal.span`, `Ideal.Quotient`, and `topologicalKrullDim`.
The dependency nodes are Mathlib leaves: `Field`, `AlgebraicGeometry.Spec`,
`AlgebraicGeometry.IsIntegral`, `AlgebraicGeometry.LocallyOfFiniteType`/`QuasiCompact`,
`AlgebraicGeometry.Scheme`, and `topologicalKrullDim`.

Edge cases checked: `f ≠ 0` and nonunit exclude the zero and whole ideals; `A` is a domain and
finite type over a field; the empty quotient is excluded by nonunit. Universes are explicit.
Searches made: `msearch.py leanfinder` for finite-type affine dimension drop (no match),
`msearch.py loogle` for `ringKrullDim quotient nonZeroDivisor` (no hit), grep of Mathlib
Krull-dimension files (only local/nonzero-divisor lemmas), and `rg` over WeilConjectures and
Sheaf (no existing project declaration). The source node's recorded Mathlib matches were read.

## Earlier second reading (a previous round; superseded)

Read the corrected node and module. Every original hypothesis is represented by an explicit
binder or typeclass. The quotient and both affine spectra are the same objects as in the node.
The original `-1` conclusion could not elaborate because `WithBot ℕ∞` has no subtraction; the
successor equality is mathematically equivalent and follows the source's codimension-one claim.

## Statement corrected

The old statement asserted `dim(Spec(A/(f))) = dim(Spec(A)) - 1`, which is ill-typed with
Mathlib's `topologicalKrullDim : WithBot ℕ∞`. Following Tags 00KV, 00KW, and 02FX, it was
corrected to `dim(Spec(A/(f))) + 1 = dim(Spec(A))`. Citer `lem-sc-effective-cartier-dimension-drop`
continues to hold because it uses the same dimension-one-drop fact.

## Second reading by H1

I independently opened the sandbox node and module, all six statement-dependency
nodes, their Mathlib declarations, and the only direct citer. No new definition
nodes or dependency modules are present in this delivery.

Object/hypothesis/conclusion checklist (each verdict: exact):

- The field k [def-weil-field] is `(k : Type u) [Field k]`. Mathlib's
  `Field` extends a commutative ring and a division ring, including nontriviality.
- The commutative k-algebra A is `(A : Type v) [CommRing A] [Algebra k A]`.
  The algebra structure chooses the same structure map as the node's k-algebra.
- Nonzero A and integral Spec(A) [def-pc-integral-scheme] are `hA : IsDomain A`.
  `IsDomain` includes `Nontrivial`; Mathlib/AlgebraicGeometry/Properties.lean:334
  states `affine_isIntegral_iff (R : CommRingCat) : IsIntegral (Spec R) ↔ IsDomain R`.
  Thus this algebraic hypothesis neither strengthens nor weakens integrality.
- Finite generation and finite type over k [def-weil-finite-type-morphism] are
  `[Algebra.FiniteType k A]`. FiniteType.lean:39 defines this as finite generation
  of the top subalgebra. The dependency's `LocallyOfFiniteType` is the affine
  finite-type ring-map condition and `QuasiCompact` adds quasi-compactness; an
  affine spectrum is quasi-compact, so no additional scheme hypothesis is lost.
- The element and its two conditions are `(f : A) (hf0 : f ≠ 0)` and
  `(hfu : ¬ IsUnit f)`, in the node's quantifier order.
- The principal ideal (f) is `Ideal.span ({f} : Set A)`; the quotient is
  `A ⧸ Ideal.span ({f} : Set A)`. No primality of this ideal or integrality of
  the quotient is assumed.
- Both affine schemes [def-weil-affine-spectrum, def-pc-scheme] are Mathlib's
  `AlgebraicGeometry.Spec (CommRingCat.of ...)`. Scheme.lean:470 constructs the
  spectrum as a scheme from the prime-spectrum locally ringed space.
- The complete conclusion is `topologicalKrullDim (Spec (A ⧸ (f))) + 1 =
  topologicalKrullDim (Spec A)`, rendered by the signature verbatim recorded
  in `lean.statement`. `topologicalKrullDim` (Topology/KrullDimension.lean:39)
  is the supremum of irreducible-closed-chain lengths in `WithBot ℕ∞`, exactly
  [def-kun-topological-krull-dimension], on the scheme's underlying space.

Source and correction review: the repository lacks its literature checkout, so
I read the local Stacks checkout `/home/ubuntu/c1-stacks-review`: tags/tags maps
00KV to algebra-lemma-minimal-over-1, 00KW to algebra-lemma-one-equation, 00OS
to algebra-lemma-dimension-spell-it-out, 00P0 to
algebra-lemma-dimension-prime-polynomial-ring, and 02FX to
morphisms-lemma-dimension-fibre-at-a-point. The corrected successor formulation
is precisely the equality in 00KW. Its Noetherian local hypotheses apply only
after localizing; finite generation over any field supplies Noetherianity.
00OS/00P0 give the identical finite dimensions at every maximal ideal of the
finite-type domain. No algebraically closed field, separatedness, or extra
Noetherian hypothesis is required. 02FX is a fibre-dimension formula in
morphisms.tex, not by itself the global affine formula; I corrected the module
and theorem source descriptions and named the actual 00OS/00P0 inputs.

The original subtraction phrasing denotes the same numerical dimension drop:
both spectra are nonempty, their dimensions are finite, and a nonzero nonunit
cannot occur in a zero-dimensional finite-type domain (a field). The successor
equation therefore does not admit an additional infinite or negative case.
I checked all DAG stmt_deps/proof_deps for citers; there is exactly one,
`lem-sc-effective-cartier-dimension-drop`, so a second direct citer does not
exist. Its step 2 uses this result on affine charts meeting the divisor;
step 1 supplies dimension d, and the equality gives the required d-1. Its
`holds: true` verdict is correct. Neither its statement nor the unit changes.

Edge cases: the zero ring and empty Spec(A) are excluded exactly by integrality;
f=0 is excluded by hf0 and units by hfu. Nonunit makes the quotient nonzero,
so its spectrum is nonempty, although it may be reducible or nonreduced.
Dimension zero is impossible under the element hypotheses, rather than excluded
by an extra binder. There is no index set or n parameter. The field may have
any characteristic, and independent explicit universes u and v impose no
equality or small-universe restriction. No implicit variable is unbound.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "Dimension of a hypersurface in an affine variety
  over any field equals dimension minus one"`: eight unrelated affine-linear
  or smooth-algebra hits; none states the result.
- `msearch.py ... loogle "Algebra.FiniteType, ringKrullDim"`: zero hits.
- `msearch.py ... leansearch "Krull dimension principal ideal quotient finitely
  generated domain over a field"`: service unavailable (Internal Server Error);
  recorded as unavailable, not as evidence of absence.
- `rg` with quotient/succ, dimension/principal, hypersurface, and
  topologicalKrullDim/Spec terms over Mathlib KrullDimension and
  AlgebraicGeometry, the source WeilConjectures, repository lean/Sheaf, and
  dag/lean_names_upstream.json: no exact existing declaration or name collision.
  I opened Mathlib's singleton quotient equalities in Regular.lean: the general
  form needs membership in the Jacobson radical, the 00KW form is local, and
  `ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors` needs a prime of maximal
  height. These are not this finite-type affine statement. The source
  Polynomial.lean only gives strict dimension decrease for an arbitrary
  nonzero ideal, and NonZeroDivisors.lean only an inequality, not this equality.

Repairs: no mathematical signature mismatch was found, and the statement and
lean.statement are unchanged. The docstring had only a summary referring the
reader back to the node, not its complete proof. I expanded all three steps,
with the named dependency nodes, nonemptiness and maximal-localization argument.
I added the required copyright/license/authorship header, placed the module
docstring immediately after imports, corrected the source descriptions noted
above, and removed unused Properties and Prime.Topology imports and unnecessary
open commands. There are no definitions or auxiliary theorems and the only
proof remains sorry, as stage 2 requires.

Validation: `scompile.py H1 lem-sc-effective-cartier-affine-dimension-drop`
compiled the final module on the server in 1.5 seconds with no warnings or
errors. I checked the recorded signature against the file byte for byte and
all Lean lines are within 100 characters.
