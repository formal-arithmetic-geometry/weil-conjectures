## Worker report

The module `Sheaf.RingTheory.GradedQuotientGenericRanks` states
`Module.graded_quotient_generic_ranks`, with its sole proof `sorry`. No definitions,
new nodes, dependency repairs, or statement corrections are needed. The existing
node is changed only in `lean`.

The source was read at Stacks `algebra.tex`, Tag 051R,
`lemma-generic-flatness-Noetherian` (lines 28458ff), and Tag 00NX,
`lemma-finite-projective` (lines 19027ff), especially clauses (3) and (8).
The seven explicit adaptation steps in the node are reproduced in the theorem
docstring. The latest blueprint direct-images statement and proof in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
were also read: this commutative-algebra prerequisite does not change that unit.

Hypothesis and clause audit:

- A commutative Noetherian base is `{A : Type u} [CommRing A]
  [IsNoetherianRing A]`.
- The commutative A-algebra is `{C : Type v} [CommRing C] [Algebra A C]`.
  `hfiniteType : (algebraMap A C).FiniteType` uses the dependency's recorded
  `RingHom.FiniteType` directly, without a stronger module-finiteness assumption.
- The graded algebra is `𝒞 : ℕ → Submodule A C`, with `[GradedAlgebra 𝒞]`:
  its underlying decomposition is internal and multiplication adds degrees.
- `C₀=A` is expressed by `hA`, injectivity of the structural map, and `hzero`,
  equality of the zero piece with its image `LinearMap.range
  (Algebra.linearMap A C)`. Together these say exactly that the structural map
  identifies A with C₀, including nonfield and zero-ring cases. Merely requiring
  the image equality would allow a noninjective structural map and lose `C₀=A`.
- The C-module, restricted A-action and their compatibility are `[AddCommGroup M]
  [Module C M] [Module A M] [IsScalarTower A C M]`.
- `ℳ : ℕ → Submodule A M`, `[DirectSum.Decomposition ℳ]`, and
  `[SetLike.GradedSMul 𝒞 ℳ]` give the internal homogeneous decomposition and
  the exact rule `C_d M_e ⊆ M_{d+e}`. `[Module.Finite C M]` and
  `[∀ d : ℕ, Module.Finite A (ℳ d)]` are the two stated finiteness hypotheses.
- Every prime quotient is covered by `(I : Ideal A) [I.IsPrime]`. There is no
  extra assumption that A itself is a domain. `A ⧸ I` is precisely R.
- Scalar extensions are written `R ⊗[A] M` and `R ⊗[A] (ℳ d)`; these are N
  and N_d under the canonical commutativity isomorphisms from the node's
  `M ⊗[A] R` convention. No arbitrary substitute modules occur. The auxiliary
  D is `R ⊗[A] C`, used in the proof plan and not separately quantified as
  extra data because the conclusions concern N and its pieces.
- The first conjunct is the R-linear grading decomposition. Its inverse on
  `DirectSum.lof ... d (t ⊗ₜ m)` is required to be `t ⊗ₜ (m : M)`.
  Thus it identifies precisely the given base-changed homogeneous summands,
  not some arbitrary decomposition isomorphic to the total module.
- `∃ a : A ⧸ I, a ≠ 0 ∧ ∃ r : ℕ → ℕ` occurs before every degree/prime
  quantifier. The same element works for the entire function r.
- `Module.Free (Localization.Away a)
  (LocalizedModule.Away a (R ⊗[A] M))` is freeness of N_a with no finite-rank
  hypothesis. All localizations use the dependencies' actual constructions.
- For every d, the explicit maps i into `Fin n → Localization.Away a` and p
  back with `p.comp i = LinearMap.id` express direct summand of a finite free
  module, permitting n=0. `Module.Finite` and `Module.Projective` state the
  indicated finite projectivity consequence as well.
- For every `q : PrimeSpectrum (Localization.Away a)`, the next equality is
  exactly `Module.finrank q.asIdeal.ResidueField
  (q.asIdeal.ResidueField ⊗[Localization.Away a] P_d) = r d`.
  `Ideal.ResidueField` is the quotient of the local ring by its maximal ideal,
  and Mathlib supplies its fraction-field interpretation; it is not an
  independently selected field. Finiteness of P_d ensures these natural-number
  dimensions are actual finite dimensions, rather than an infinite-dimensional
  case in which `finrank` would return zero.
- The final universal prime p is restricted by `I ≤ p.asIdeal` and
  `a ∉ Ideal.map (Ideal.Quotient.mk I) p.asIdeal`, exactly the indicated open
  inside V(I). The existential q contracts along `algebraMap A R_a` to p.
- The field equivalence e is constrained by equality to
  `Ideal.ResidueField.map ... hq`. It is the canonical comparison, not just
  an unconstrained field isomorphism.
- The fibre comparison E is an additive equivalence together with
  `E (k • x) = e k • E x`, exactly a linear equivalence after transporting
  scalars along e. Its pure-tensor formula is the canonical map
  `k ⊗ m ↦ e(k) ⊗ ((1 ⊗ m)/1)`. This presentation avoids needing a file-local
  `RingHomInvPair` instance for semilinear-equivalence notation; no hypothesis
  or mathematical content is changed.
- Finally `Module.finrank p.asIdeal.ResidueField
  (p.asIdeal.ResidueField ⊗[A] (ℳ d)) = r d` gives simultaneous constancy of
  the entire original fibre-dimension function on that one principal open.

Dependency declarations used/read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and its equivalent
  `Algebra.FiniteType` formulation.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, with
  `Mathlib.RingTheory.Localization.Away.Basic` supplying the ring API.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away` and
  `LocalizedModule.mkLinearMap` (also read the universal-property interface).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`; the theorem
  uses its underlying `PrimeSpectrum` with the literal prime ideals and their
  local-ring residue fields, since no sheaf or scheme morphism is required.
- Proof-only import `Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness`:
  `Module.noetherian_algebra_module_generic_freeness`; its complete signature
  and proof docstring were read.
- Proof-only import `Mathlib.RingTheory.Spectrum.Prime.FreeLocus`:
  `Module.isLocallyConstant_rankAtStalk`, the declaration supplied by the
  corresponding dependency's `mathlib_match`. Its signature was read along
  with finite-projective clause (8) in Stacks. That node has no lean record
  and needs no repair.

Additional established Mathlib interfaces used directly include `GradedAlgebra`,
`DirectSum.Decomposition`, `SetLike.GradedSMul`, `TensorProduct`, `DirectSum.lof`,
`PrimeSpectrum`, `Ideal.ResidueField`, and `Ideal.ResidueField.map`. Their source
signatures and documentation were read; no notion was copied or redefined.

Edge cases checked before writing: M=0 permits n=0, a=1 and r identically zero;
missing homogeneous degrees likewise have rank zero. No nonzero or positive
rank hypothesis occurs. The zero base ring has no prime I and is harmless.
A=C with all grading in degree zero is allowed. Infinite total rank is essential:
C=A[x], M=C has finite pieces but the localized total module need not be finite.
For C=Z[x], M=C/(2x), I=(0) one can take a=2, giving r(0)=1 and r(d)=0 for d>0;
for I=(2), a=1 gives r(d)=1 for every d. Thus one cannot omit the prime quotient
or replace the common element by degree-dependent elements. Universes u,v,w
are independent, explicitly bound, and no restriction to rational primes,
maximal ideals, fields, standard gradings, or degree-zero module generators
has been imposed. There is no disputed statement or detected node fault.

Searches for existing statements:

- `msearch.py ... leanfinder` with the query "A finite graded module over a
  finite type algebra over a Noetherian ring has after every prime quotient
  one generic localization with all homogeneous pieces of constant finite
  projective fibre rank": eight results, including homogeneous localization
  finite type and finite module local-properties lemmas; no exact statement.
- `msearch.py ... leansearch` with "Simultaneous generic ranks of all graded
  pieces after a prime quotient of a finite graded module": eight results
  on quotient finranks and ramification; none is this simultaneous theorem.
- `msearch.py ... loogle` with
  `GradedAlgebra, DirectSum.IsInternal, SetLike.GradedSMul`: no results.
- `msearch.py ... grep` with `generic.*[Ff]ree|[Gg]raded.*[Rr]ank` in
  `RingTheory`: one unrelated generic polynomial result. Existing node searches
  additionally identify generic freeness and locally constant rank as separate
  ingredients, not the combined statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `GradedSMul`, graded
  fibre/rank words, the exact item id and the chosen declaration/module names:
  the existing standard-graded Hilbert-function theorem has a field base and
  standard-generation hypothesis; the graded-fibre and graded-tail modules are
  different scheme-level consumer statements. No duplicate of this item.
  The exact item-id and exact declaration searches returned no matches upstream.
- `dag/lean_names_upstream.json` exact declaration/module search: no match.

Validation: compilation uses only the prescribed `scompile.py` wrapper, in
module mode with `autoImplicit false`. The first probe diagnosed the missing
`RingHomInvPair` instance in semilinear notation; the equivalent explicit
additive-plus-scalar formulation above compiles without it. No diagnostic
commands, auxiliary axioms, proved theorems, private definitions, local notation,
or file-local instances remain in the delivery.

## Second reading by NX

A separate clause-by-clause pass by this worker compared the final file against
all hypotheses and conclusions of the unchanged JSON node; this is not a claim
that a second agent was started. The brief forbids starting agents and provides
an independent maintainer review of the delivery. That audit found the initial
finite-type binder used the equivalent `Algebra.FiniteType`; it was changed to
`(algebraMap A C).FiniteType` to use the dependency's recorded declaration
literally. Tensor-factor orientation is the canonical symmetry, not a different
base change. The explicit inverse on summands, canonical residue-map constraint,
scalar compatibility and pure-tensor formula were each checked. In particular,
the zero piece identification includes both injectivity and image equality;
there are no independent generic elements per degree, no finite-total-rank
assumption, and no arbitrary comparison fields/maps. No mathematical mismatch
or statement correction was found.
