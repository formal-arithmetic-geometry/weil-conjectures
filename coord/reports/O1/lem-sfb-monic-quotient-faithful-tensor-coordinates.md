## Worker report

The module `Sheaf.RingTheory.MonicQuotientFaithfulTensorCoordinates` states
`AdjoinRoot.exists_monicQuotient_faithful_tensor_coordinates`. Its only theorem has
proof `sorry`. No definitions, auxiliary theorem nodes, dependency repairs, or
statement corrections are needed. The original node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- The commutative ring is `(R : Type u) [CommRing R]`, without `Nontrivial R`.
- The specified positive integer is `(d : ℕ) (hd : 1 ≤ d)`. The coefficient list is
  `(a : Fin d → R)`, preserving the specified index even over the zero ring.
- The polynomial is `(f : R[X])` with defining equality
  `hf : f = X ^ d + ∑ i : Fin d, C (a i) * X ^ (i : ℕ)`.
  Parameterizing a defined object by its defining equality is equivalent to
  substituting this expression everywhere; this imposes no additional restriction.
- `B` is Mathlib's `AdjoinRoot f`, definitionally
  `R[X] ⧸ Ideal.span {f}`. Its inferred algebra is the canonical quotient algebra,
  and `root f` is `AdjoinRoot.mk f X`, the required class of the variable.
- The basis clause is `∃ e : Module.Basis (Fin d) R (AdjoinRoot f)` together with
  `∀ i : Fin d, e i = root f ^ (i : ℕ)`.
- The unique coefficient maps are the existing linear maps `e.coord i`. Uniqueness
  is part of the `Module.Basis` interface (`repr` is a linear equivalence), so no
  extra arbitrary maps or unproved data are introduced. The reconstruction clause
  is `∀ b, b = ∑ i : Fin d, e.coord i b • root f ^ (i : ℕ)`.
- For every module `(N : Type v) [AddCommGroup N] [Module R N]`, the actual
  isomorphism `Φ_N` is
  `(TensorProduct.equivFinsuppOfBasisLeft e).trans
    (Finsupp.linearEquivFunOnFinite R N (Fin d))`.
  These Mathlib definitions construct the linear isomorphism; no choice or
  existential placeholder is used for it. Its source is `AdjoinRoot f ⊗[R] N`
  and its target is `Fin d → N`. The first quantified conjunction states
  `Φ_N (b ⊗ₜ[R] x) i = e.coord i b • x` and
  `Φ_N.symm x = ∑ i, (root f ^ (i : ℕ)) ⊗ₜ[R] x i`.
- Naturality quantifies over modules in independent universes `v` and `w`, every
  `h : N →ₗ[R] N'`, every tensor `q`, and every `i : Fin d`. It states
  `Φ_N' (h.lTensor (AdjoinRoot f) q) i = h (Φ_N q i)`.
  Equality on every coordinate and input is precisely equality of the two linear
  maps in the node. `h.lTensor B` is literally `TensorProduct.map LinearMap.id h`.
- The exactness clause quantifies over three modules in independent universes
  `v`, `w`, `z` and the two linear maps, with `k.comp h = 0`. It says
  `Function.Exact (h.lTensor B) (k.lTensor B) ↔ LinearMap.range h = LinearMap.ker k`.
  Thus it states both preservation and reflection, in the node's orientation.
- The last conjunct is `RingHom.FaithfullyFlat (algebraMap R (AdjoinRoot f))`,
  precisely faithful flatness of the canonical structure map.

Dependency declarations read and used:

- `def-weil-polynomial-ring`: `Polynomial`,
  `Mathlib.Algebra.Polynomial.Basic`, finitely supported coefficient construction;
  brought in by the public `Mathlib.RingTheory.AdjoinRoot` import.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom` from
  `Mathlib.Algebra.Algebra.Hom`, and `Ideal.Quotient.algebra` /
  `Ideal.Quotient.mkₐ` from `Mathlib.RingTheory.Ideal.Quotient.Operations`.
  `AdjoinRoot` uses precisely this quotient and canonical algebra structure.
  The definitions, `AdjoinRoot.mkₐ`, its algebra instance, and `AdjoinRoot.root`
  were inspected in their source files. No private replacement is made.
- `def-weil-pbc-free-module`: `Module.Free` from
  `Mathlib.LinearAlgebra.FreeModule.Basic` and `Module.Basis`, `Basis.repr`,
  `Basis.coord` from `Mathlib.LinearAlgebra.Basis.Defs`. The conclusion gives the
  specified basis, which is the node's stronger explicit form of freeness.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, and `LinearMap.lTensor` from Mathlib's
  `LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`. The explicit coordinate
  equivalence comes from `.Basis`, composed with
  `Finsupp.linearEquivFunOnFinite` from `LinearAlgebra.Finsupp.Defs`.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` and
  `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` from
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, and `RingHom.FaithfullyFlat` /
  `RingHom.faithfullyFlat_algebraMap_iff` from
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`. The latter is the public import
  giving the ring-map conclusion and exposing the module condition.
- Proof dependency `lem-weil-pbc-monic-quotient-free`: its recorded Mathlib match
  `AdjoinRoot.powerBasis'`, in `Mathlib.RingTheory.AdjoinRoot`, was read in full.
  This import is public because the statement itself uses `AdjoinRoot` and `root`.
  No other non-Mathlib proof dependency has a module to import.

Sources checked: `literature/stacks-project/algebra.tex`, `definition-flat`
(lines 8620ff: all four clauses, particularly (2) and (4)), and
`lemma-characterize-henselian`, proof of (10) implies (1) (lines 42272ff), where
`R[T]/(f)` is finite free. The extra coordinate argument is explicitly the node's
agent argument, reproduced step by step in the theorem docstring.

Edge cases checked before writing:

- Zero ring: no `Nontrivial` assumption or `natDegree f = d` requirement occurs.
  `AdjoinRoot f` and every unital `R`-module are singleton modules. A basis indexed
  by `Fin d` is valid since the coefficient module is also singleton. All formulas,
  naturality, exactness and the maximal-ideal characterization of faithful flatness
  hold. The specified index is retained.
- `d = 1`: the basis is the singleton `1`, and the formulas reduce to the usual
  `R ⊗[R] N ≃ₗ[R] N` identification.
- `d = 0` is excluded exactly as in the node. It must be excluded for reflection:
  the quotient by `1` is zero and cannot detect failure of exactness over a nonzero ring.
- For `f = X²` over `ℤ`, the formula gives `(r + s t) ⊗ x ↦ (r • x, s • x)`
  and inverse `(x₀,x₁) ↦ 1 ⊗ x₀ + t ⊗ x₁`, as required.
- Zero modules and zero maps are admitted. The exactness biconditional still tests
  the full image/kernel equality. Different module universes are not identified.

Searches actually run:

- `msearch.py ... leanfinder` with query “Positive degree monic polynomial quotient
  has natural tensor coordinates N^d and tensoring preserves and reflects exactness
  including the zero ring”: 8 hits, chiefly universal-factorization-ring and
  presentation tensor-model ingredients; no full statement.
- `msearch.py ... loogle '"AdjoinRoot", "FaithfullyFlat"'`: 0 hits.
- `msearch.py ... grep 'powerBasisAux|equivFinsuppOfBasisLeft|iff_exact_iff_lTensor_exact'`:
  23 hits, including `AdjoinRoot.powerBasisAux'`,
  `TensorProduct.equivFinsuppOfBasisLeft` and its formula lemmas, and the faithful
  flatness exactness characterization. These supply ingredients but not the full
  specified-length quotient theorem with naturality and the zero-ring branch.
- `msearch.py ... leansearch` with query “The quotient by a monic polynomial of
  specified positive degree has natural tensor coordinates and is faithfully flat
  even over the zero ring”: 8 hits including `AdjoinRoot.powerBasisAux'`,
  `Polynomial.Monic.free_quotient`, `.finite_quotient`, and monic division facts;
  no complete match.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for monic/tensor coordinate expressions, `monicQuotient`, `powerQuotient`, then
  `monic_quotient_faithful|exists_power_tensor_coordinates`: no equivalent theorem.
  The relevant nearby `MonicTensorPresentation` concerns iterated presentations;
  other tensor-coordinate results concern sheaves, complexes, and stalks.
- `rg` for the exact item id in `lean/WeilConjectures`: no hits. Project hits in
  other modules are only natural-language references to this prerequisite.
- Read the full signatures and docstrings of the dependency declarations and the
  two coordinate-equivalence constructors in the pinned Mathlib sources.

Validation: `scompile.py O1 lem-sfb-monic-quotient-faithful-tensor-coordinates <module>`
passed for both sandbox and named library module, 1.5 s each. An initial precedence
error in the inverse pure tensor was fixed by parenthesizing the power explicitly.
No diagnostics remain. There are no statement disputes or node faults.

## Second reading by O1

The dispatcher explicitly forbids starting another agent and assigns the independent
review to the maintainer. This section records my own second reading, not a claimed
independent review. I reopened the node and the final Lean module, checked each clause
against the correspondence above, and checked that all universes and variables are
explicitly bound. The key boundary check is that the basis is `Fin d` even when `R`
is the zero ring: the statement uses neither a nontriviality instance nor a degree
identity that would lose this case. The chosen `e` is pinned to each specified power;
its coefficient maps and constructed tensor equivalences give the exact requested
formulas. Naturality is pointwise equality of the same composites, and exactness is
a biconditional, not just preservation. No mismatch was found and no mathematical
statement changed during this rereading. The independent maintainer review remains
part of delivery, as instructed by the dispatcher brief.
