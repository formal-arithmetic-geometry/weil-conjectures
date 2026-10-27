## Worker report

The module `Sheaf.LinearAlgebra.BoundedCoordinateSplitProjections` states the entire
node as two theorems, both with `sorry` proofs:
`Module.Basis.bounded_coordinate_split_projections` (the general-index clauses) and
`Module.Basis.bounded_coordinate_split_reindexing` (the final natural-number clause).
There are no definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` field changes.

Source read: the node, including all seven proof steps, and the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
The current paragraph supplies the direct-image context; as the node explicitly says,
this coordinate lemma and its elementary proof are an agent auxiliary from the returned
reconstruction proof, rather than a theorem appearing verbatim in that paragraph.
The seven proof steps are preserved in the theorem docstrings, split as steps 1--5
and 6--7. The existing reconstruction consumer's source was also read to check its
norm-bound encoding and composition convention.

Hypotheses, exactly:

- The normed field K is `(K : Type u) [NormedField K]`. This extends Mathlib's `Field`
  of `def-weil-field` and permits a trivial scalar norm. No completeness or
  `NontriviallyNormedField` instance is imposed.
- The normed K-vector space is `(V : Type v) [NormedAddCommGroup V] [NormedSpace K V]`.
- The arbitrary algebraic basis and chosen index are `(J : Type w)` and
  `(b : Module.Basis J K V) (j₀ : J)`. All three universes are explicit and independent.
  The second theorem specializes the index to ℕ, exactly for the node's last clause;
  j₀ is absent there because no reindexing formula uses it.
- `c C : ℝ`, `_hc : 0 < c`, and `_hcC : c ≤ C` express `0 < c ≤ C < ∞`:
  real numbers are finite. The conjunction `_hb` quantifies over every `t : J →₀ K`
  (over `ℕ →₀ K` in the second theorem). `b.repr.symm t` is exactly the finite sum
  of `t j • b j`. The maximum is
  `(↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ)`; NNReal has bottom zero, so the empty
  maximum is zero. The two inequalities match the lower and upper bounds verbatim.
- `(A : Set ℕ) (_hA : A.Infinite)` in the second theorem expresses exactly the
  infinite-subset hypothesis, using the recorded predicate of `def-sfb-finite-infinite-set`.

Conclusions, clause by clause:

- `V →L[K] V` is D. Its multiplication is composition in the stated order; its `1`
  is the identity and `0` is the zero operator. All existential operators below have
  this bundled type, which asserts both K-linearity and continuity.
- `lam : J → V →L[K] K` and `(lam j).toLinearMap = b.coord j` specify the actual
  coordinate function. The next conjunct is precisely
  `‖lam j v₀‖ ≤ c⁻¹ * ‖v₀‖`. The scalar-field norm renders the absolute value.
- `E : J → J → V →L[K] V` is fixed pointwise by
  `E i j v₀ = lam j v₀ • b i`, and the same conjunct supplies its pointwise bound C/c.
- The matrix-unit product clause gives `E i j * E k l = E i l` when `j = k` and
  `E i j * E k l = 0` when `j ≠ k`. These are exactly the two values of the
  Kronecker delta, with no added decidability hypothesis on J.
- `theta : V → V →L[K] V` is fixed by `theta v₀ w₀ = lam j₀ w₀ • v₀`, with
  `‖theta v₀ w₀‖ ≤ c⁻¹ * ‖v₀‖ * ‖w₀‖`.
- `p : Set J → V →L[K] V` is fixed for every A and every vector by
  `(b.repr v₀).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j)`.
  The indicator gives `t • b j` for j in A and zero otherwise. `Finsupp.sum` only
  sums over the finite input support, even for infinite A. The same conjunct supplies
  `‖p A v₀‖ ≤ (C / c) * ‖v₀‖`.
- `∀ A B : Set J, p A * p B = p (A ∩ B)` is the arbitrary overlap identity.
- For `hF : (A ∩ B).Finite`, `hF.toFinset` is exactly F. The last conjunct gives both
  `p A * p B = ∑ k ∈ hF.toFinset, E k k` and
  `p A * p B = ∑ k ∈ hF.toFinset, E k j₀ * E j₀ j₀ * E j₀ k`.
- For J = ℕ, `a : ℕ ≃o A` is an increasing bijection onto the subset with its induced
  order. An order isomorphism between linear orders is precisely a strictly increasing
  bijection, so no order condition is lost or strengthened.
- `u r p : V →L[K] V` satisfy `u (b n) = b (a n : ℕ)`,
  `r (b (a n : ℕ)) = b n`, and `m ∉ A → r (b m) = 0`.
  These values on the algebraic basis uniquely determine the operators. The formula
  for p is repeated to identify it with the general theorem's coordinate projection;
  it is not an arbitrary splitting map.
- The remaining conjunction is precisely `r * u = 1`, `u * r = p`, `p * u = u`, and
  the two pointwise bounds `‖u v₀‖ ≤ (C / c) * ‖v₀‖` and
  `‖r v₀‖ ≤ (C / c) * ‖v₀‖`.

The existence statements determine every operator from the prescribed basis or pointwise
formula. They do not choose unconstrained data from a mere existence theorem. Their
continuity is part of the theorem to be proved at stage 3. No definition has postponed data.

Dependency declarations and APIs read:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, read together with
  `NormedField` in `Mathlib.Analysis.Normed.Field.Basic` and `NormedSpace` in
  `Mathlib.Analysis.Normed.Module.Basic`; these are exposed by the operator import.
- `def-sfb-finite-infinite-set`: `Set.Finite` and `Set.Infinite`,
  `Mathlib.Data.Finite.Defs` (185, 205); `Set.Finite.toFinset` in
  `Mathlib.Data.Set.Finite.Basic` (75) supplies the actual finite intersection.
- `Module.Basis.repr`, `Module.Basis.repr_symm_apply`, and `Module.Basis.coord`,
  `Mathlib.LinearAlgebra.Basis.Defs` (especially 139 and 670), for the existing notions
  of algebraic expansion and coordinates; no duplicate coordinate notion is defined.
- `Set.indicator` from `Mathlib.Algebra.Group.Indicator` supplies coordinate deletion
  without a decidability assumption, as documented in that module.
- Proof dependency `lem-sfb-additive-norm-bound-continuity`:
  `AddMonoidHomClass.continuous_of_bound`, generated by the `to_additive` declaration
  at `Mathlib.Analysis.Normed.Group.Uniform` (105--110). Its docstring and full
  multiplicative signature were read. The module is a plain proof import.
- Proof dependency `lem-sfb-infinite-nat-increasing-enumeration`:
  `Nat.Subtype.orderIsoOfNat`, `Mathlib.Order.OrderIsoNat` (95--111), which assumes
  only `[Infinite A]` and returns `ℕ ≃o A`. The module is a plain proof import.
  At stage 3, `A.Infinite` supplies that infinite subtype instance.

Edge cases checked before writing and reviewed after compilation:

- Zero input has empty coefficient support and maximum zero, so all estimates reduce
  to zero bounds. Empty intersection gives both empty sums and the zero projection.
- J cannot be empty because the node already supplies j₀; this is faithfully encoded.
  A singleton J is allowed. There is no accidental finite-dimensional assumption.
- A = ∅ gives the zero coordinate projection; A = J gives the identity; disjoint
  subsets give zero product; singleton intersection gives the corresponding matrix unit.
- In the natural-number case A = ℕ and A the even numbers both have the required
  increasing enumeration; coordinates outside A are explicitly killed by r.
- The hypotheses allow trivial scalar norms and incomplete normed spaces; continuity
  follows from the real Lipschitz bounds, without completion or infinite series.
- The finite overlap factors are in the correct composition order: first E_j₀k,
  then E_j₀j₀, then E_kj₀, producing E_kk.

Searches actually run through `msearch.py Q45 lem-sfb-bounded-coordinate-split-projections`:

- `leanfinder`: "Uniformly bounded algebraic basis coordinates yield continuous matrix
  units coordinate projections and split reindexing onto infinite subsets". Eight hits,
  including `Module.Basis.continuous_toMatrix`, `continuous_equivFun_basis`, and
  `Module.Basis.constrL`. These finite-dimensional statements require finite bases or
  extra scalar/completeness hypotheses; none gives this combined assertion.
- `loogle`: "Module.Basis, ContinuousLinearMap". Eight hits: `constrL`, its basis/apply
  formulas, `exists_opNorm_le`, `exists_opNNNorm_le`, `opNorm_le`, `opNNNorm_le`, and
  `InnerProductSpace.toMatrix_rankOne`. No exact match: the basis norm results assume
  finite bases and nontrivially normed complete scalar fields; the rank-one result
  assumes inner products.
- `grep`: "basis.*(bound|norm|continuous)|coordinate.*projection" in
  `Analysis/Normed/Module`. Ten hits in `Bases.lean` and `FiniteDimension.lean` concern
  Schauder bases or finite-dimensional estimates. These do not give the finite algebraic
  expansions and split operators of this node.
- `leansearch`: "Algebraic basis uniform coordinate norm bounds continuous projections
  and matrix units on a normed vector space". Eight hits, including finite-dimensional
  basis estimates, `Module.Basis.norm_repr_le_norm`, `ZLattice.abs_repr_le`, and
  `ContinuousLinearMap.norm_fst_le`. None states the full item or its natural-number
  reindexing clause under these hypotheses.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for coordinate split/projection
  language and proposed names, plus `grep -rn` for the exact node id in
  `lean/WeilConjectures`, found no existing statement. The relevant reconstruction
  consumer explains the calculation in its proof docstring but does not state this
  auxiliary. The proposed full names are unused in Mathlib and both project roots.

Validation: `scompile.py Q45 lem-sfb-bounded-coordinate-split-projections` compiled both
sandbox and library views of the complete module successfully, with no errors or warnings.
Every theorem proof is `sorry`; there are no auto-bound implicit variables, file-local
notation, instances, or private definitions. No statement dispute was found.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
