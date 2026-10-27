## Worker report

Item: `lem-trf-cartesian-subspace-scalar-tower`, group NV, stage 2.
Module: `Sheaf.Analysis.NormedSpace.CartesianSubspaceScalarTower`.
The two declarations `Module.exists_orthogonal_basis_subspace` and
`Module.exists_orthogonal_basis_restrictScalars` state clauses (1) and (2), respectively.
Their proofs are `sorry`; no definition or proof is added. The original node changes only
in `lean`. The record lists both declarations and copies the first signature verbatim.

Source checked: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Proposition 2.4.1/5,
printed p. 96 (scan p. 104), and Lemma 2.4.3/4, printed p. 100 (scan p. 108).
The PDF named by the node was fetched into this sandbox from
https://math.arizona.edu/~cais/scans/BGR-Non_Archimedean_Analysis.pdf and those two pages
were rendered and read. Proposition 5 gives cartesian subspaces of finite-dimensional
cartesian spaces; Lemma 4 gives cartesian restriction through a cartesian field extension.
The source also discusses supplements, but the node does not assert them and neither
Lean statement includes them. The source's proof of Lemma 4 is the finite-coefficient
argument recorded in the DAG. No statement correction or disputed statement is needed.

Hypothesis and conclusion correspondence for clause (1):

- The field is `{K : Type u} [Field K]`. `Field` is the Mathlib match of the only
  statement dependency, `def-weil-field`.
- The multiplicative real-valued absolute value is `abv : AbsoluteValue K ℝ≥0`.
  This uses the nonnegative-real codomain of an absolute value directly. Its multiplication,
  nonnegativity, definiteness, and triangle inequality are Mathlib's existing structure.
  `h_nontrivial : abv.IsNontrivial` is precisely a nonzero scalar with value different from
  one, and `h_nonarch : IsNonarchimedean abv` is the strong triangle inequality.
- The vector space is `{V : Type v} [AddCommGroup V] [Module K V]`; its norm is the
  arbitrary function `N : V → ℝ≥0` in the node. `h_definite` says `N x = 0 ↔ x = 0`,
  `h_ultra` is `N (x+y) ≤ max (N x) (N y)`, and `h_smul` is
  `N (a • x) = abv a * N x`. No topology, completion, or inner product is added.
- The finite basis is `b : Module.Basis (Fin n) K V`. `h_orthogonal` quantifies over
  every coefficient tuple and equates the norm of its sum to
  `Finset.univ.sup (fun i ↦ abv (a i) * N (b i))`.
  Indexing by `Fin n` covers any finite basis by reindexing.
- The arbitrary linear subspace is `U : Submodule K V`. There is no separate finite
  dimension hypothesis on `U`; it follows mathematically from the ambient finite basis.
- The conclusion provides `m : ℕ`, `c : Module.Basis (Fin m) K U`, and the exact same
  orthogonality equation for all `K` coefficients. The coercions from `U` to `V` ensure
  this is the restricted original norm, not a separately chosen norm.

Hypothesis and conclusion correspondence for clause (2):

- The base field and its absolute value are `[Field K]`, `abvK`, `hK_nontrivial`, and
  `hK_nonarch`, with the same meanings as in clause (1).
- The extension is `{F : Type w} [Field F] [Algebra K F]`. The algebra map between fields
  is injective. `abvF`, `hF_nontrivial`, and `hF_nonarch` give the absolute value of the
  other field of the stipulated kind. `h_isometric` states exactly
  `abvF (algebraMap K F a) = abvK a` for every `a : K`.
- `h_extension` quantifies over every `A : Submodule K F` with
  `[FiniteDimensional K A]`. It supplies a finite `K`-basis with the orthogonality
  equation using `abvF` on the actual elements of `F`, and `abvK` on coefficients.
- The normed `F`-vector space is `{W : Type t} [AddCommGroup W] [Module F W]` and
  `N : W → ℝ≥0`, together with definiteness, the strong triangle inequality, and
  `h_smul` for every `F` scalar, using `abvF`.
- `[Module K W] [IsScalarTower K F W]` specifies restriction along this extension.
  The scalar tower forces `a • w = (algebraMap K F a) • w`, by applying its law to
  `a`, `1 : F`, and `w`; it does not permit an unrelated base-field action.
  No separate `K`-homogeneity assumption is imposed: it follows from this law,
  `h_smul`, and `h_isometric`.
- `h_space` quantifies over every `M : Submodule F W` with `[FiniteDimensional F M]`
  and supplies its finite orthogonal `F`-basis. The equation applies `N` after
  coercion into `W`, and `abvF` to the `F` coefficients.
- The arbitrary requested subspace is `U : Submodule K W` with
  `[FiniteDimensional K U]`. The conclusion supplies a finite `K`-basis `c` and
  the exact orthogonality equation with `abvK` and the original `N` on `W`.
  Neither `F/K` nor `W/F` is required to have finite dimension.

Dependencies and existing notions read:

- `def-weil-field` records Mathlib `Field`, read in
  `Mathlib.Algebra.Field.Defs`, including its `CommRing`, `DivisionRing`,
  nontriviality, and inverse-law fields. It needs no dependency repair.
- `Mathlib.Algebra.Order.AbsoluteValue.Basic`: `AbsoluteValue`,
  `AbsoluteValue.IsNontrivial`; full defining signatures and docstrings read.
- `Mathlib.Algebra.Order.Ring.Basic`: `IsNonarchimedean` is exactly the maximum
  inequality (available through the public `IsNonarchimedean` import).
- `Mathlib.LinearAlgebra.Basis.Defs`: `Module.Basis` provides genuine independent
  spanning basis vectors via its coordinate linear equivalence.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional` is finite
  generation of a vector space, with the documented finite-basis equivalence.
- `Submodule`, `Algebra`, and `IsScalarTower` are the existing Mathlib structures.
- `Mathlib.Data.Finset.Lattice.Fold`: `Finset.sup` folds using lattice bottom;
  `Finset.sup_empty` gives bottom on the empty family. `NNReal.bot_eq_zero` makes
  this bottom zero.
- The proof dependency `lem-trf-cartesian-subspace` currently has no Lean record or
  Mathlib match in the read clone, so there is no module to import for it. It is named
  in both proof docstrings. The theorem statements do not need it as a notion.

Edge cases checked before drafting and on the second pass:

- `n = 0`, `m = 0`, `V = 0`, `U = 0`, and `W = 0` are included. No index
  nonemptiness or positive dimension is assumed. An empty supremum in `NNReal`
  is zero, matching the norm of the empty sum by definiteness.
- In clause (2), zero coefficient subspaces `A` and the zero `F`-subspace `M`
  are included in the hypotheses, using empty bases.
- The full subspace `U = ⊤`, one-dimensional spaces, and the identity field
  extension are allowed. No properness assumption occurs.
- Incomplete fields, arbitrary characteristics compatible with the valued-field
  hypotheses, and infinite-dimensional ambient `F` or `W` are not excluded.
- The universes of `K`, `V`, `F`, and `W` are independent and explicitly declared.
  Finite-dimensional tests are submodules of the actual fixed ambient spaces,
  so there is no smaller test universe and no vacuous quantification.

Searches performed (all wrapper outputs are retained in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder`: "A linear subspace of a finite dimensional
  nonarchimedean normed vector space admitting an orthogonal basis admits an
  orthogonal basis and cartesian restriction of scalars is transitive".
  Eight hits were inner-product orthonormal-basis/subordinate-basis results,
  `Module.Basis.ofZLatticeBasis_comap`, and `Orthonormal.codRestrict`; none is this
  exact nonarchimedean orthogonality theorem.
- `msearch.py ... loogle`: `"IsUltrametricDist", "Basis"`; zero hits.
- `msearch.py ... grep`: `orthogonal[Bb]asis|[Cc]artesian|exists.*orthogonal`,
  subdirectory `Analysis/Normed`; three hits concern cartesian products of
  operators, not orthogonal bases or cartesian normed spaces.
- `msearch.py ... leansearch`: "Every subspace of a nonarchimedean normed space
  with a finite orthogonal basis has a finite orthogonal basis and cartesian
  restriction of scalars is transitive". Eight hits concern inner-product
  `OrthonormalBasis` or normed restriction-of-scalars structures; none asserts
  preservation of exact orthogonal bases.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `cartesian.*[Ss]ubspace|orthogonal[Bb]asis|[Cc]artesianSpace|[Oo]rthogonal.*[Bb]asis`:
  no matching theorem. The countable ultrametric-basis theorem has discretely
  valued coefficients and best-approximation assumptions; it is not this result.
- Direct `grep -rn` of the item id in `lean/WeilConjectures`: no hits.
- Direct search of `dag/lean_names_upstream.json` for orthogonal/cartesian names:
  only unrelated cartesian-square and orthogonality declarations.
- The project's `IsStableNonarchimedeanField` was read: it is a predicate on
  finite field extensions with their spectral norms, not the statement here.
- Proposed declaration names were searched in Mathlib's `LinearAlgebra` and
  `Analysis`, in `WeilConjectures`, and in `Sheaf`: no collisions. The similarly
  named `LinearMap.BilinForm.exists_orthogonal_basis` concerns bilinear forms.

No additional notion is introduced: both the norm axioms and the finite orthogonality
equations occur explicitly as the node supplies them. All data types and operations
are Mathlib definitions. No new definition node or dependency module is necessary.

Validation: the prescribed `scompile.py NV lem-trf-cartesian-subspace-scalar-tower`
compiled both the sandbox module and its final library module name with exit code 0
and no warnings or errors. The initial probe exposed the missing activation of Mathlib's
scoped `NNReal` notation; adding `open scoped BigOperators NNReal` fixed it.

## Second reading by NV

Independent second reading by the maintainer reviewer (cc review service), replacing the
author's own second pass at delivery 8b29f69d, which was not an independent reading (H11).
The Lean module and node record are unchanged.

Node statement as a list, with the Lean that renders it and the verdict:

1. Field `K` [def-weil-field]: `{K : Type u} [Field K]`. Exact.
2. Nontrivial real-valued multiplicative nonarchimedean absolute value:
   `abv : AbsoluteValue K ℝ≥0`, `abv.IsNontrivial`, `IsNonarchimedean abv`
   (Mathlib `Algebra/Order/Ring/Basic.lean:94`, `∀ a b, f (a+b) ≤ f a ⊔ f b`). Exact;
   the `ℝ≥0` codomain is the real codomain with its nonnegativity.
3. Norm on `V`: `N : V → ℝ≥0`, `h_definite` (`N x = 0 ↔ x = 0`), `h_ultra`
   (`IsNonarchimedean N`), `h_smul` (`N (a • x) = abv a * N x`). Exact; nothing more.
4. Orthogonality of a finite family: `N (∑ i, a i • b i) = Finset.univ.sup (abv (a i) * N (b i))`
   for every `a : Fin n → K`. Exact; `Finset.sup` over `ℝ≥0` has empty value `⊥ = 0`, as the
   node's convention requires.
5. Clause (1): a finite orthogonal basis `b : Module.Basis (Fin n) K V` and an arbitrary
   `U : Submodule K V`; conclusion `∃ m (c : Module.Basis (Fin m) K U)` orthogonal for the
   restricted norm `N ∘ Subtype.val`. Exact (a basis of `U` is finite since `V` is; the
   `Fin m` indexing is a reindexing).
6. Clause (2), `F/K` an isometric extension of such valued fields: `[Field F] [Algebra K F]`,
   `abvF` nontrivial and nonarchimedean, `h_isometric : abvF (algebraMap K F a) = abvK a`.
   `hF_nontrivial` follows from `hK_nontrivial` and `h_isometric`, so it adds no strength;
   it renders "such valued fields". Exact.
7. Every finite-dimensional `K`-subspace of `F` has an orthogonal `K`-basis: `h_extension`
   over `A : Submodule K F` with `[FiniteDimensional K A]`, coefficients measured by `abvK`,
   vectors by `abvF`. Exact.
8. `W` a normed `F`-space with `N(aw) = |a|_F N(w)`: `[Module F W]`, definite, ultrametric,
   `F`-homogeneous `N`. The `K`-structure is `[Module K W] [IsScalarTower K F W]`, which forces
   `a • w = algebraMap K F a • w`, so it is the restriction of scalars and nothing else. Exact.
9. Every finite-dimensional `F`-subspace of `W` has an orthogonal `F`-basis: `h_space`. Exact.
10. Conclusion: every `U : Submodule K W` with `[FiniteDimensional K U]` has a finite
    orthogonal `K`-basis for `abvK` and the original `N`. Exact; quantifier order as in the node.

Edge cases: `n = 0`/`V = 0`, `U = 0` (empty basis, both sides `0`), `A = 0`, `M = 0`, `W = 0`
are all inside the binders; `F = K` and infinite `[F : K]`, `dim_F W = ∞` are allowed; no
completeness. Universes `u v w t` are independent and all bound; `autoImplicit false`.

Mathematics: clause (1) is the content of lem-trf-cartesian-subspace (the proof dependency,
no Lean record yet); clause (2) proof steps 2-6 checked: `M = ΣFu_j` finite over `F`, the
coefficient spans `A_i`, the product family `a_iℓ e_i`, its max-norm identity via the
`F`-orthogonality, the `K`-orthogonality in `A_i` and the isometry, independence from
definiteness, and the final application of clause (1) inside `V₀`. The docstrings carry
these steps, the BGR source places and `(blueprint: lem-trf-cartesian-subspace-scalar-tower)`.

Gates: no definitions (hence none hollow), both proofs are `sorry`, no extra instance or
hypothesis beyond the node, no pro-étale material. `lean.statement` is verbatim the first
signature in the file. The stmt_dep `def-weil-field` is the Mathlib `Field` used.

Searches: the worker's recorded searches; a further `rg` of `orthogonal_basis|CartesianSubspace`
in the side-live `lean/Sheaf` and `lean/WeilConjectures` trees finds only the unrelated
`RationalPositiveDefiniteGram` and `CountableUltrametricBasis` modules. No duplicate.

Advisory: when lem-trf-cartesian-subspace is stated, its Lean should reuse (or be stated
consistently with) `Module.exists_orthogonal_basis_subspace` rather than add a second copy
of clause (1) under the same name.
