## Worker report

The module `Sheaf.LinearAlgebra.CoefficientEndomorphismIndependence` states
`Finsupp.linearIndependent_mapRange_ringHom`, with its entire proof postponed by
`sorry`. No definition, dependency module, new node, or statement correction is needed.
Only the item's `lean` field changes. No statement dispute was found.

Clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`, exactly `def-weil-field`'s Mathlib match.
- The injective unital ring endomorphism is `(σ : k →+* k)` with
  `(hσ : Function.Injective σ)`. A `RingHom` preserves one, zero, addition and
  multiplication. No surjectivity or perfectness assumption occurs.
- Any coordinate set I is `{I : Type v}`. Its universe is independent of k's;
  there is no finite, decidable-equality, or nonempty hypothesis.
- The vector space of finitely supported functions is Mathlib's `I →₀ k`, with
  its standard pointwise addition and scalar action, not a separate definition.
- The map T_sigma is `Finsupp.mapRange σ σ.map_zero`. Its defining equation is
  `Finsupp.mapRange_apply`: evaluation at i is definitionally `σ (w j i)`.
  The existing construction uses the input's finite support and preservation of zero.
- The nonnegative integer m and the ordered m vectors are `(m : ℕ)` and
  `(w : Fin m → I →₀ k)`. Indexing from zero instead of one just renames indices.
- The assumption about all k-coefficient relations is `(hw : LinearIndependent k w)`.
  `Fintype.linearIndependent_iff` says exactly that for every `c : Fin m → k`,
  `∑ j, c j • w j = 0` implies `∀ j, c j = 0`.
- The conclusion is `LinearIndependent k (fun j : Fin m =>
  Finsupp.mapRange σ σ.map_zero (w j))`. The scalar ring remains k, not σ(k).
  The same finite-family equivalence therefore gives exactly the conclusion about
  every relation with arbitrary coefficients in k.
- Both empty cases are allowed: `m = 0` and arbitrary empty I are well-typed.

Dependencies and source declarations read:

- Statement dependency `def-weil-field`: `Field`,
  `Mathlib.Algebra.Field.Defs`, including its full class signature and docstring.
- Proof dependency `def-pc-field-extension`: `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`. The field inclusion in the proof plan is an
  algebra structure on fields; no custom field-extension structure is introduced.
- Proof dependency `lem-weil-linear-independence-field-extension`:
  `linearIndependent_algebraMap_comp_iff`,
  `Mathlib.LinearAlgebra.LinearIndependent.BaseChange`. Its coordinate type is
  finite, as required after restriction to the common finite support.
- `Finsupp.mapRange` and `Finsupp.mapRange_apply`,
  `Mathlib.Data.Finsupp.Defs`, used through `Mathlib.LinearAlgebra.Finsupp.Defs`.
- `LinearIndependent` and `Fintype.linearIndependent_iff`,
  `Mathlib.LinearAlgebra.LinearIndependent.Defs`.

The module publicly imports the statement APIs and privately imports the recorded
proof-dependency modules. Its docstring gives all four DAG proof steps: restriction
to the union of supports, coefficient lifting only inside the image subfield,
finite-coordinate scalar extension, and restriction of a target relation. The
source attribution retains the node's distinction: an agent refinement supporting
Milne, Algebraic Groups (2017), Proposition 14.50, printed p.296; this lemma is not
claimed to be stated in Milne.

Edge cases checked mathematically before writing:

- m = 0: both independence predicates assert absence of a nontrivial relation
  on an empty family and hold, regardless of I.
- I empty and m positive: the hypothesis fails, since every vector is zero and
  the coefficient 1 at one index gives a nontrivial relation. No case is excluded.
- Zero vector in a nonempty family: again the original hypothesis fails.
- Infinite I: the finite union of the m finite supports still suffices.
- Imperfect k: for k = F_p(t) with σ(t) = t^p, σ is injective but not surjective.
  The image-subfield argument works without lifting arbitrary elements of k.
- Identity σ: mapRange acts as identity, so the conclusion matches the hypothesis.
- No characteristic restriction enters the statement or the argument.

Searches for an existing full statement (2026-10-24):

1. `msearch.py Q50 <item> leanfinder` with query
   "Applying an injective field homomorphism coefficientwise to finitely supported
   vectors preserves linear independence over the target field": eight hits,
   including `LinearIndependent.map_of_injective_injective`, its semiring variant,
   `LinearIndependent.comp`, `LinearIndependent.map_injOn`, and `LinearIndependent.map'`.
   Read the full candidate signatures and docstrings in
   `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`: the injective/injective
   lemma takes a coefficient map in the reverse direction with compatibility
   `j (i r • x) = r • j x`. The forward variant requires surjectivity. Neither
   states this lemma for a possibly nonsurjective coefficient endomorphism.
2. `msearch.py ... loogle 'LinearIndependent, Finsupp'`: twelve hits about
   `repr`, `finsuppLinearCombination_injective`, the kernel characterization,
   and related general definitions, no coefficient-endomorphism theorem.
3. `msearch.py ... grep
   'linearIndependent.*map|map.*linearIndependent|map.*LinearIndependent'
   LinearAlgebra/Finsupp`: two hits, both in `VectorSpace.lean`, about single
   vectors and reindexing rather than coefficient field embeddings.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `mapRange` and
   coefficient/endomorphism independence found unrelated module, site and
   coefficient-transport constructions; no full statement. The prescribed
   `grep -rn` for the node id in `lean/WeilConjectures` returned no match.
5. Exact-name `rg` for `linearIndependent_mapRange_ringHom` over Mathlib,
   `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   returned no match.

Validation: prescribed `scompile.py Q50 <item> <module file>` completed with exit 0.
The local compiler reported OSError 28 (disk full), after which the wrapper's
server confirmation compiled the delivered file in 1.5 seconds without errors
or unexpected warnings. No direct build or live source edit was performed.

## Second reading by Q50

An in-thread consistency reading reopened the node and delivered signature:
field, ring endomorphism, injectivity, unrestricted I, finite-support vector
space, coefficientwise map, m ≥ 0, original independence, target independence
over k, absence of surjectivity, and both empty cases correspond exactly as
listed above. No mismatch or correction was found. The signature binds both
universes explicitly and introduces no arbitrary map or additional assumption.
The original DAG proof remains unchanged and the theorem's docstring includes
its entire natural-language plan. Per the dispatcher's explicit instruction,
no other agent was started; the maintainer's independent delivery review is
still required, and this consistency pass is not represented as an independent
worker review.
