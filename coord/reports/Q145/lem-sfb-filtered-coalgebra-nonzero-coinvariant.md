## Worker report

The module `Sheaf.RingTheory.FilteredCoalgebraNonzeroCoinvariant` states
`Coalgebra.exists_nonzero_coinvariant_of_filtration`, with `sorry` as its sole
proof. It introduces no definition and changes only the item's `lean` record.

Read Milne, Algebraic Groups (2017), Definition 14.4, equation (91), printed
p.281, and Theorem 14.5(c) implies (a), printed pp.281–282, in the local PDF.
The coalgebra-only generalization in the node is faithful: the source's proof
uses coassociativity, the counit, and the filtration, without multiplication or
an antipode. The module docstring records all five DAG proof steps, including
the tensor quotient kernel, the injectivity of both maps, and the last counit
calculation. No node fault or statement correction was needed.

Clause-by-clause correspondence:

- A field k is `{k : Type u} [Field k]`.
- A k-vector space C is `{C : Type v} [AddCommGroup C] [Module k C]`.
- The linear Delta and epsilon, coassociativity, and BOTH counit identities are
  `[Coalgebra k C]`. Read the complete class in
  `Mathlib.RingTheory.Coalgebra.Basic`: its `comul` and `counit` are linear maps;
  `coassoc` includes the canonical tensor associator, and
  `rTensor_counit_comp_comul` and `lTensor_counit_comp_comul` state the two unit
  identities, with the inverses of the canonical unitors on the right.
- The distinguished element is `(g : C)`. Its two equalities are
  `(hg : IsGroupLikeElem k g)`, whose fields are `counit_eq_one` and
  `comul_eq_tmul_self` in `Mathlib.RingTheory.Coalgebra.GroupLike`.
- The nonnegative integer indexed linear subspaces are
  `(F : ℕ → Submodule k C)`; they are increasing by `hmono : Monotone F`.
- The degree-zero equality is `hzero : F 0 = Submodule.span k {g}`. The span
  of the singleton is exactly k g.
- The union condition is `hexhaustive : ∀ x : C, ∃ r : ℕ, x ∈ F r`.
- For each r, `hcomul` says that `Submodule.map Coalgebra.comul (F r)` is
  contained in `⨆ i ≤ r, LinearMap.range
  (TensorProduct.map (F i).subtype (F (r - i)).subtype)`.
  The map on the left gives Delta(F_r). Each range on the right is exactly
  the image of F_i tensor F_(r-i) in C tensor C, rather than an abstract tensor
  space. The bounded supremum is the sum of those subspaces for i=0,...,r.
- An arbitrary nonzero vector space is `{V : Type w} [AddCommGroup V]
  [Module k V] [Nontrivial V]`. For an additive group, Nontrivial is equivalent
  to existence of a nonzero vector. No finite-dimensional instance is used.
- The right coaction is `(c : V →ₗ[k] V ⊗[k] C)`.
- `hcoassoc` is `(assoc k V C C).toLinearMap ∘ₗ c.rTensor C ∘ₗ c =
  Coalgebra.comul.lTensor V ∘ₗ c`, namely (c tensor 1)c=(1 tensor Delta)c
  under the canonical associator.
- `hcounit` composes `(Coalgebra.counit).lTensor V ∘ₗ c` with the canonical
  `TensorProduct.rid k V`, giving `LinearMap.id`. This is (1 tensor epsilon)c=1.
- The whole conclusion is `∃ x : V, x ≠ 0 ∧ c x = x ⊗ₜ[k] g`.
- There is no algebra, Hopf, cocommutativity, or dimension assumption on C,
  and no dimension assumption on V. Universes u, v, w are bound independently.

Dependency declarations used:

- `def-weil-field`: Mathlib `Field`, read in `Mathlib.Algebra.Field.Defs`;
  imported publicly.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.map`, `LinearMap.rTensor`, and `LinearMap.lTensor`; read their
  interfaces in `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`.
  The statement's public coalgebra import exposes them; `assoc` and `rid` are
  the standard equivalences in `.Associator`.
- Proof dependency `lem-weil-pbc-tensor-right-exact`: `LinearMap.lTensor_exact`
  and `LinearMap.rTensor_exact` in
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`, imported privately.
- Proof dependency `lem-sfb-vector-space-tensor-family-zero-detection`:
  `TensorProduct.eq_zero_of_forall_rTensor_eq_zero` in
  `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis`, imported privately.
  Read its full signature and proof: it handles an arbitrary family and a free
  right tensor factor; vector spaces supply freeness. The module is named in
  the dependency's closed upstream audit record.

Edge cases checked before drafting:

- r=0 gives exactly the image of F_0 tensor F_0; the bounded supremum includes
  i=0 and has no negative-degree term. For i<=r, natural subtraction is r-i.
- An element has only finitely many tensor coefficients, even for infinite
  dimensional C or V; an empty tensor sum uses degree zero in the proof.
- The zero vector space V is excluded precisely by the node's nonzero premise.
  The zero C or g=0 cannot satisfy epsilon(g)=1 over a field, so their exclusion
  follows from the existing hypotheses rather than an extra assumption.
- Constant filtration F_r=k g with C=k g and the trivial coaction is included.
- Arbitrary characteristic and independent field, C, V universes remain allowed.
- At induction index r=0, the terms i=0 and i=1 in degree r+1 are each killed
  by one quotient factor, as in the source proof.

Searches performed using the prescribed search wrapper:

- LeanFinder: "Every nonzero comodule over a connected exhaustive filtered
  coalgebra has a nonzero vector v with coaction v tensor g". Eight hits:
  `Coalgebra.Repr.arbitrary`, representation projection declarations,
  `IsGroupLikeElem.ne_zero`, and categorical coalgebra packaging. None states
  the filtered-comodule existence assertion.
- Loogle: "Coalgebra, IsGroupLikeElem". Twelve hits on the group-like
  predicate and its API. Used `IsGroupLikeElem` rather than repeating it.
- LeanSearch: "A nonzero comodule over a connected filtered coalgebra has a
  group like coinvariant". Eight hits on group-like elements and abstract group
  representation coinvariant quotients; no match for the theorem.
- Mathlib grep wrapper: `filtered.*[Cc]oalgebra|[Cc]omodule|coinvariant|[Cc]oconnected`
  in RingTheory/Coalgebra: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for filtered coalgebras,
  comodules, coinvariants, and group-like elements found finite-subcomodule and
  finite-coefficient-coalgebra results and unrelated group coinvariant results.
  Read `Sheaf.RingTheory.FiniteSubcomodule`: its coaction equations use the same
  Mathlib associator and unitor, but its conclusion is different.
- The exact item id has no match in `lean/WeilConjectures`. The chosen full
  declaration name has no match in Mathlib, WeilConjectures, or Sheaf; searches
  of `dag/lean_names_upstream.json` found no matching theorem.

Validation: the prescribed `scompile.py` compiled the file in sandbox and
library module modes, each in 1.6 seconds, with no errors or warnings. All
variables and universes are explicitly bound, and every line is at most 100
characters. The node's signature is copied verbatim from the theorem header.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
