## Worker report

The module `Sheaf.RingTheory.InvariantCoefficientsReconstruction` states
`RingHom.invariantCoefficients_reconstruction`. Its only postponed proof is that
named theorem, whose docstring contains all four steps of the node's proof.
No definitions, dependency repairs, or statement corrections are needed. The node
copy changes only `lean`.

Hypothesis and conclusion correspondence:

- The commutative rings are `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`.
  Their universes are independent and explicitly declared.
- The three unital ring homomorphisms are `(σ τ : A →+* B) (ε : B →+* A)`.
  `hεσ : ε.comp σ = RingHom.id A` and `hετ : ε.comp τ = RingHom.id A`
  express both common-retraction identities.
- The subring C is Mathlib's `σ.eqLocus τ`, literally the subring of elements
  on which the two maps agree. `Algebra.ofSubsemiring` gives its canonical
  scalar action on A; `Algebra.algebraMap_ofSubring` identifies its structure
  map with the inclusion. No independently chosen algebra structure occurs.
- `(r : ℕ) (hr : 1 ≤ r) (x : Fin r → A)` is the given finite positive family.
  Reindexing the paper's 1,...,r by `Fin r` changes no mathematical datum.
- `hexp` states, for every b in B, existence of exactly one coefficient tuple
  `c : Fin r → A` satisfying `∑ j, σ (c j) * τ (x j) = b`.
  This writes the node's unique expansion directly without requiring a chosen
  A-algebra structure on B or introducing a second definition of basis.
- `hinv` states that every tuple expanding `τ a` has every coefficient in
  `σ.eqLocus τ`. In the presence of `hexp` this is exactly the stated condition
  on the uniquely determined expansion; it is neither a stronger assumption
  nor an existential statement permitting a different tuple.
- `∃ b : Module.Basis (Fin r) (σ.eqLocus τ) A, (∀ j, b j = x j) ∧ ...`
  says that the specified x family, not merely some family, is a C-basis.
- The witness `φ : (A ⊗[σ.eqLocus τ] A) ≃+* B` is a unital ring isomorphism;
  `∀ a a₂ : A, φ (a ⊗ₜ[σ.eqLocus τ] a₂) = σ a * τ a₂` specifies its full
  pure-tensor formula. This is the tensor map of the node, since pure tensors
  generate the tensor product additively and hence determine a ring map.
  It does not replace that map by an arbitrary unspecified isomorphism.
- `∃ e : Module.Basis (Fin r) A (A ⊗[σ.eqLocus τ] A), ...` together with
  `∀ j, e j = (1 : A) ⊗ₜ[σ.eqLocus τ] x j` states the specified tensor basis.
  Mathlib's default tensor-product A-action acts on the first A factor;
  its right-factor algebra structure is explicitly not a global instance.
- The final `∀ j, φ ((1 : A) ⊗ₜ[σ.eqLocus τ] x j) = τ (x j)` records every
  requested basis image, even though it follows from the pure-tensor formula.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`,
  `Module.Free`, defined by existence of `Module.Basis`. The conclusion uses
  the latter's actual basis data, whose signature and docstring were also read
  in `Mathlib.LinearAlgebra.Basis.Defs`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and its canonical
  `TensorProduct.tmul`, from `Mathlib.LinearAlgebra.TensorProduct.Defs`;
  the universal-property `TensorProduct.lift` and `TensorProduct.ext'` were
  read in `Mathlib.LinearAlgebra.TensorProduct.Basic`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the recorded
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, and `ext` in `Mathlib.RingTheory.TensorProduct.Basic`, and
  `Algebra.TensorProduct.productMap`, `productMap_apply_tmul`, `productMap_left`,
  `productMap_right` in `Mathlib.RingTheory.TensorProduct.Maps`. Their ring
  structure supplies the tensor ring in the signature; their pushout interface
  constructs the isomorphism's underlying map in proof step 3.
- Proof dependency `lem-weil-pbc-free-module-base-change-free`:
  `Module.Basis.baseChange` and `Module.Basis.baseChange_apply` in
  `Mathlib.LinearAlgebra.TensorProduct.Basis`, imported without `public`.
- `RingHom.eqLocus` and `RingHom.mem_eqLocus` from
  `Mathlib.Algebra.Ring.Subring.Basic` give precisely the specified subring.
  `Mathlib.Algebra.Algebra.Basic` supplies its canonical algebra action.

Edge cases checked before writing:

- Zero rings are allowed: a retraction from the zero ring forces A to be zero,
  and all coefficient tuples then coincide. A zero module over a zero ring has
  the requested `Fin r`-indexed basis. No `[Nontrivial A]` or `[Nontrivial B]`
  has been added; tensor and basis definitions apply without it.
- Rank one with `σ = τ = ε = id` and x equal to a unit satisfies both input
  conditions and returns the usual rank-one basis and multiplication tensor
  isomorphism. For equal maps generally, `σ.eqLocus τ` is the full subring,
  which the statement retains as its own carrier with canonical inclusion.
- The pair groupoid for A = k × k, B = A ⊗[k] A, σ(a) = a ⊗ 1,
  τ(a) = 1 ⊗ a, and multiplication ε has equalizer the diagonal k and the
  two standard idempotents as x. Thus the formulation includes positive
  ranks beyond one and the intended tensor orientation.
- Rank zero is excluded exactly by the node's `r ≥ 1`; no empty-family case
  covered by the node is lost. No field, flatness, or characteristic constraint
  appears. Both ring universes remain unrestricted.

Searches made using the prescribed msearch.py wrapper (2026-10-24):

- LeanFinder, query: "Two ring maps with a common retraction and invariant basis
  coefficients give a basis over their equalizer and an isomorphism from the
  tensor product". Eight results: presentation base-change constructions,
  `IsBaseChange.basis`, a local-ring basis descent theorem, and pushout results.
  None gives the node's reconstruction hypotheses and conclusions.
- Loogle, query: `RingHom.eqLocus, TensorProduct`. One result,
  `Algebra.IsEffective.eqLocus_includeLeft_includeRight`, which identifies the
  equalizer of the two tensor inclusions for an effective algebra; it does not
  reconstruct this ring from the given coefficient data.
- Grep, query: `eqLocus|basis.*[Ii]sBaseChange|[Ii]sBaseChange.*basis`, directory
  `RingTheory/TensorProduct`. Eight hits in `IsBaseChangeFree.lean` and
  `IncludeLeftSubRight.lean`; these are base-change bases and tensor-inclusion
  equalizers, not this statement.
- LeanSearch, query: "Descent of a basis over the equalizer of two ring
  homomorphisms with a common retraction and invariant coefficients".
  Eight results include `Module.Basis.ofSplitExact`, coefficient transport,
  `AlgHom.equalizer`, `RingHom.mem_eqLocus`, and `AlgHom.tensorEqualizer`.
  They supply existing notions or different equalizer comparisons, not a match.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf`, query
  `invariant.*[Cc]oeff|[Cc]oeff.*[Rr]econstruction|eqLocus`, found unrelated
  representation invariants, group-scheme differential operators and affine
  groupoid invariant-ring statements. No existing reconstruction theorem.
- Direct grep of the item id in `lean/WeilConjectures` found no declaration.
  Exact-name rg for `invariantCoefficients_reconstruction` in Mathlib,
  `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf`
  found no collision.

Read the full source lemma and proof in `literature/stacks-project/groupoids.tex`,
Tag 03C8 (`lemma-basis`), including its final comparison diagram. The DAG explicitly
abstracts its invariant-coefficient step and common retraction as hypotheses;
this module states that abstraction exactly. No node fault or disputed statement
was found. Compilation and delivery validation are recorded below.

## Second reading by Q63

The dispatcher requires this worker to work alone; this is a second reading by
that same worker, with independent maintainer review reserved for the delivery.
I reread the node and the completed Lean signature together. Both retraction
identities are present; C is the actual equalizer; `hexp` quantifies over all of
B and determines every coordinate; `hinv` concerns the coordinates of τ(a),
not those of σ(a). The first basis is over C on A; the second is over A on the
first tensor factor. Both specified vector equalities and every basis image are
present. The isomorphism's formula uses σ on the first factor and τ on the
second. No extra scalar structure or nonzero-ring condition was inserted.
There was no mismatch requiring a signature or node correction.
