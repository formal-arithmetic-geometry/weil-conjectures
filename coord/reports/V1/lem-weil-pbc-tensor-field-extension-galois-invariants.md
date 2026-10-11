## Worker report

The module `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants` states
`TensorProduct.injective_and_range_eq_invariants` and the parenthetical algebra consequence
`Algebra.TensorProduct.range_eq_invariants_and_equiv`. Both proofs are `by sorry`.
No definition is introduced, no dependency record is replaced, and the node statement is unchanged.

Hypothesis and clause correspondence:

- The field extension `k ⊆ M` is `{k : Type u} {M : Type v} [Field k] [Field M]
  [Algebra k M]`, using the Mathlib convention recorded by `def-pc-field-extension`.
  The image of the base field is `Set.range (algebraMap k M)`.
- A group of `k`-algebra automorphisms is `G : Subgroup (M ≃ₐ[k] M)`.
  This is literally a group of automorphisms, with its inherited group structure;
  `τ : G` quantifies over its elements. No finiteness, separability, normality,
  algebraicity, or assumption that G is the full automorphism group is imposed.
- Its fixed field being `k` is the equality `hfixed` between the set of `y : M`
  satisfying `∀ τ : G, (τ : M ≃ₐ[k] M) y = y` and `Set.range (algebraMap k M)`.
  Identifying k with its injective image is precisely the dependency's convention.
- The vector space is `(A : Type w) [AddCommGroup A] [Module k A]`.
  All three universes are explicitly bound and independent.
- The tensor product is Mathlib `A ⊗[k] M`, with the factors in the node's order.
- The `k`-linear map `id_A ⊗ τ` is
  `LinearMap.lTensor A (τ : M ≃ₐ[k] M).toLinearEquiv.toLinearMap`.
  Mathlib's `LinearMap.lTensor_tmul` gives exactly `a ⊗ y ↦ a ⊗ τ(y)`.
- The map iota is the linear map `(TensorProduct.mk k A M).flip (1 : M)`.
  By the definition of `mk` and `flip`, it sends `a` to `a ⊗ 1`.
  Its linearity is part of its type, with no auxiliary hypothesis.
- Injectivity is the first conjunct `Function.Injective` of this map.
- The image being exactly the invariants is the second conjunct: `Set.range` of
  this same map equals the set of tensors fixed by every `τ : G` under the displayed
  `lTensor` action. Both containments are encoded by equality, rather than just one.
- The parenthetical algebra clause is stated separately for `(A : Type w) [Ring A]
  [Algebra k A]`, with the same extension, subgroup, and fixed-field hypothesis.
  These are the algebra specialization's hypotheses, not restrictions on the first theorem.
  It equates the carrier of `(Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] M).range`
  with the same invariant set. This image subalgebra is the node's `A ⊗ 1`.
  The second conjunct supplies an algebra equivalence from `A` to that range, with
  `∀ a, (e a : A ⊗[k] M) = a ⊗ₜ[k] 1`. Thus the isomorphism is the canonical one
  specified by iota; it is not an unspecified equivalence of underlying sets.
  Commutative k-algebras, including the source's algebra A, are included; the
  vector-space argument also covers associative noncommutative k-algebras.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, module `Mathlib.Algebra.Algebra.Defs`.
  Read its full class signature and docstring: the ring homomorphism is `algebraMap`.
  The class is available through `Mathlib.Algebra.Algebra.Equiv`; no private copy.
- Mathlib tensor notions: `TensorProduct.mk` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `LinearMap.lTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.Map`, and `AlgEquiv.toLinearEquiv` in
  `Mathlib.Algebra.Algebra.Equiv`. Read their signatures and docstrings.
- The algebra consequence uses `Algebra.TensorProduct.includeLeft` from
  `Mathlib.RingTheory.TensorProduct.Basic`, whose docstring and full signature
  identify it as the algebra map `a ↦ a ⊗ 1`; its `AlgHom.range` is Mathlib's
  image subalgebra. No separate invariant-ring definition is necessary.

Source checked: the local Stacks checkout is absent on this machine. Read the
published proof of Stacks Tag 038B at https://stacks.math.columbia.edu/tag/038B.
The displayed invariant polynomial coefficient computation agrees with the node's
source. The six-step basis argument is the node's explicitly recorded agent proof;
all six steps, including injectivity and the algebra specialization, are retained
in the declaration docstrings.

Edge cases checked mathematically before writing:

- The zero vector space (and an empty basis) gives a singleton tensor space; the
  inclusion is injective and all tensors lie in its image. No nonzero condition on A.
- A zero algebra is allowed: there is no `[Nontrivial A]` binder; its tensor product
  and image subalgebra are also zero, so the algebra equivalence is meaningful.
- For `M = k` and the trivial subgroup, all tensors are invariant and the inclusion
  is the usual isomorphism. For a proper extension with trivial subgroup, hfixed
  fails, correctly preventing a false application.
- An infinite subgroup, infinite field extension, and infinite-dimensional A are
  allowed: each individual tensor still has finite basis support. No finite-product
  argument or finite-dimensionality hypothesis is used.
- No characteristic restriction is present. Universes impose no smallness restriction
  on A or M. A subgroup is nonempty by definition, as a group should be.

Searches made with the prescribed remote tools (logged in `searches.jsonl`):

- LeanSearch: `invariants of tensor product V tensor M under field automorphisms equal
  V tensor 1`. The service returned Internal Server Error; recorded unavailable.
- LeanFinder: `invariants of tensor product V tensor M under automorphisms with fixed
  field k are V tensor 1`. Eight hits concerned representation tensor products and
  coinvariants, including `Representation.repOfTprodIso_apply` and
  `Representation.Coinvariants.mk_inv_tmul`; none states this node.
- Loogle: `LinearMap.lTensor, AlgEquiv, Set.range`. Zero hits.
- Mathlib grep: `tensor.*(fixed|invariant)|(fixed|invariant).*tensor`. Hits concerned
  representation coinvariants and induced representations, not this statement.
- Source repository and `lean/Sheaf` rg with that same expression plus
  `tensor_fieldExtension`: no exact statement. Source `AlgHom.tensorFixedPointsEquiv`
  in `WeilConjectures.Mathlib.RingTheory.TotallySplit` was inspected in full: it
  requires a finite family and commutative algebras and gives base change of a fixed
  subalgebra, so it does not state this arbitrary-group vector-space theorem.
- Source grep of the exact node id: no hit. The existing sheaf module
  `GaloisInvariantClosedSubsetDescends` only mentions this node in its proof docstring.
- Searched the proposed theorem names across Mathlib, the source repository, and
  `lean/Sheaf`: no collisions.

Validation: `scompile.py V1 lem-weil-pbc-tensor-field-extension-galois-invariants`
compiled this module on the server in 1.2 seconds, with no errors or warnings.
No statement dispute or correction was needed. The independent second reading is
left to the second worker, as required by the dispatcher brief.


## Second reading by V1

Independent second reader: I opened the item node, both theorem signatures and their
proof docstrings, and the sole statement dependency def-pc-field-extension with its
recorded Mathlib declaration. Verdict: the Lean states every clause of the node;
no mathematical repair is needed. I left the module and node copy unchanged.

Source reading: this machine has no local Stacks checkout. I read the original TeX
at https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
chapter Notation and the lemma labelled lemma-closed-fixed-by-Galois, and checked
https://stacks.math.columbia.edu/tag/038B. The current TeX puts the coefficient
computation at lines 840-841 rather than the older node's lines 924-925; the label
and computation agree. The chapter assumes k is a field. The surrounding descent
lemma assumes a possibly infinite Galois extension and an arbitrary k-scheme; its
affine reduction uses a commutative k-algebra and a finite Galois subextension.
The present node explicitly extracts the vector-space basis argument with the
weaker, sufficient fixed-field hypothesis. That argument is valid for an arbitrary
automorphism subgroup and arbitrary-dimensional vector space. There is no hidden
finite type, reducedness, nonzero-algebra, or characteristic assumption to inherit.

Object, hypothesis, and conclusion checklist (node order):

1. Fields k and M, and the extension k contained in M: `{k : Type u} {M : Type v}`,
   `[Field k] [Field M] [Algebra k M]`. PASS. def-pc-field-extension records precisely
   this convention. I read `Algebra` in Mathlib.Algebra.Algebra.Defs: its ring map
   is `algebraMap k M`, and its scalar action is multiplication by that map.
   The field map is injective, so using its image instead of a literal subset k
   changes nothing. Neither field is restricted in size or characteristic.
2. G a group of k-algebra automorphisms of M: `G : Subgroup (M ≃ₐ[k] M)` and
   `τ : G`. PASS. This expresses an actual group of such automorphisms, with the
   inherited composition law; it does not require the full automorphism group.
   A separately indexed action would give the same invariant set after taking its
   image subgroup, so the subtype encoding loses no group-of-automorphisms case.
3. Fixed field of G exactly k: `hfixed : {y : M | ∀ τ : G,
   (τ : M ≃ₐ[k] M) y = y} = Set.range (algebraMap k M)`. PASS. It is exactly the
   fixed-element condition, in both directions, rather than an IsGalois instance
   or a separability, algebraicity, normality, or finite-dimensionality assumption.
4. A an arbitrary k-vector space: `(A : Type w) [AddCommGroup A] [Module k A]`.
   PASS. There is no finite-dimensionality or nontriviality requirement.
5. Tensor product in the stated order: `A ⊗[k] M`. PASS. This uses Mathlib's
   tensor product of modules, not a field compositum or a different scalar base.
6. The k-linear map id_A tensor τ: `LinearMap.lTensor A
   (τ : M ≃ₐ[k] M).toLinearEquiv.toLinearMap`. PASS. I read AlgEquiv.toLinearEquiv
   and LinearMap.lTensor: the latter is TensorProduct.map LinearMap.id f, and its
   tmul formula is a tensor y mapped to a tensor τ(y).
7. The k-linear inclusion iota(a) = a tensor 1: `(TensorProduct.mk k A M).flip
   (1 : M)`. PASS. I read TensorProduct.mk and its application formula; flipping
   and evaluating at one gives exactly that linear map, without extra hypotheses.
8. Iota is injective: `Function.Injective` of this same linear map, the first
   conjunct of TensorProduct.injective_and_range_eq_invariants. PASS.
9. Its image equals all invariants: the second conjunct equates `Set.range` of
   iota with `{z : A ⊗[k] M | ∀ τ : G, LinearMap.lTensor ... z = z}`. PASS.
   The universal quantifiers and both containments are exactly those of the node.
10. Algebra specialization, invariants = A tensor 1 isomorphic to A: the separate
    theorem Algebra.TensorProduct.range_eq_invariants_and_equiv has `[Ring A]
    `[Algebra k A]`, identifies the carrier of `includeLeft.range` with the same
    invariant set, and gives `∃ e : A ≃ₐ[k] includeLeft.range` with
    `∀ a, (e a : A ⊗[k] M) = a ⊗ₜ[k] 1`. PASS. I read includeLeft and its tmul
    formula in Mathlib.RingTheory.TensorProduct.Basic. Its range is the image
    subalgebra A tensor 1; the final formula forces the canonical equivalence.
    This covers commutative algebras in the source, and the usual associative
    unital k-algebra notion too. Algebra assumptions affect only this consequence,
    not the vector-space theorem. No separate invariant-algebra definition is made.

Edge cases: the zero vector space and empty basis are allowed; both image and
invariants are the singleton zero tensor space. The zero algebra is allowed,
including the affine ring of the empty scheme. Neither theorem assumes
Nontrivial A. M = k with the trivial subgroup gives the standard tensor-unit
isomorphism; a trivial subgroup of a proper extension cannot satisfy hfixed.
There is no empty group (groups contain the identity), and no other index set in
the signature. Infinite groups, infinite extensions, and infinite-dimensional A
are included; each tensor has only finitely many basis coordinates. No natural
number n is introduced, so n = 0 has no separate restriction. Characteristics
zero and positive are included. Universes u, v, w are independently bound;
G's subtype universe is inherited from the automorphism type and imposes no
additional bound on A or M. Every variable in both signatures is explicitly bound.

Independent H4 searches, using different wording from the first worker and logged
by msearch.py in searches.jsonl:

- LeanSearch: `scalar extension of a vector space fixed by automorphisms descends
  to the base field`. Service unavailable (Internal Server Error); no verdict
  inferred from that failure.
- Loogle: `"lTensor", "fixed"`. Zero hits.
- LeanFinder: `For a field extension L over K and any subgroup of algebra
  automorphisms with fixed field K, the common fixed vectors after extending
  scalars from V to L are exactly v tensor one`. Eight hits about field fixed
  points, including IntermediateField.fixedField and
  IsGalois.mem_range_algebraMap_iff_fixed; none concerns an arbitrary vector space.
- Mathlib grep: `tensorFixed|fixed.*[tT]ensor|[tT]ensor.*fixed|lTensor.*invariant`.
  Three unrelated hits about fixed maps or fixed objects, no exact theorem.
- Project/source rg: `tensorFixed|fixedPoints.*tensor|tensor.*fixedPoints|
  scalar.*descent|descent.*scalar|injective_and_range_eq_invariants|
  range_eq_invariants_and_equiv` in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json. No exact theorem or name collision. I opened
  AlgHom.tensorFixedPointsEquiv in WeilConjectures.Mathlib.RingTheory.TotallySplit:
  it assumes a finite family of endomorphisms and commutative algebras, and gives
  a tensor product with their fixed subalgebra. It does not state this arbitrary
  subgroup/vector-space result. FinitePurelyInseparableScalarDescent concerns
  purely inseparable extensions, not automorphism invariants.

H5-H9 and delivery dependencies: there are no definitions, hollow data, new nodes,
or dependency modules to repair. Both theorem proofs are exactly `by sorry`.
The module and both declarations identify Stacks 038B and the blueprint id. The
main docstring records all six node proof steps, including finite support,
coordinate uniqueness, the fixed-field condition and injectivity; the second
explicitly applies those steps to the algebra consequence. Imports provide the
algebra equivalences, tensor maps and algebra tensor structure used in signatures.
Namespaces have no Sheaf prefix; all lines meet the 100-character bound. I checked
by direct string comparison that lean.statement is verbatim the first theorem's
signature (up to the proof delimiter).

Mismatches and changes: none in the statement, dependency, or Lean. I added this
independent reading and its search records only. No statement correction or
STATEMENT-DISPUTED marker is warranted.

Validation: scompile.py with the absolute sandbox module path compiled the module
on the server in 1.3 seconds, exit code 0, with no errors or warnings. An initial
relative-path invocation could not locate the sandbox file; using its absolute
path resolved that invocation error without any source change.
