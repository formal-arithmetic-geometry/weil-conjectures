## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.IsogenyQuasiInverse` states
`AlgebraicGeometry.IsIsogeny.exists_quasiInverse`. Its sole proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections were needed.
The node copy changes only `lean`.

Hypotheses and clauses, checked against the complete node statement:

- A field k: `{k : Type u} [Field k]`, with explicit universe u and no perfection,
  algebraic-closure, or characteristic assumption.
- Abelian varieties A and B over k: `{A B : Over (Spec (.of k))}`, `[GrpObj A]`,
  `[GrpObj B]`, `[IsAbelianVariety A]`, and `[IsAbelianVariety B]`.
  The latter class is proper, smooth, and connected; group structures are separate.
- The isogeny u is named f to keep it distinct from the universe u:
  `(f : A ⟶ B) [IsIsogeny f]`. This class includes the homomorphism property,
  surjectivity of the underlying scheme morphism, and finiteness of the
  scheme-theoretic kernel. No separability is required.
- A positive integer n: `∃ n : ℕ, 1 ≤ n ∧ ...`. Positive natural numbers encode
  precisely the integers at least one; no value of n is prescribed.
- A k-group-scheme homomorphism v is named g:
  `∃ g : B ⟶ A, IsMonHom g ∧ ...`. An Over morphism is already over k.
  `IsMonHom` states compatibility with identity and multiplication, equivalently
  a group-object homomorphism in this setting.
- The first composite v ∘ u = [n]_A is
  `f ≫ g = (𝟙 A : A ⟶ A) ^ n`.
- The second composite u ∘ v = [n]_B is
  `g ≫ f = (𝟙 B : B ⟶ B) ^ n`.
  These are morphism equalities, including on nonreduced test schemes. The power
  is pointwise group multiplication on Hom, not iteration under composition.
  It is exactly the library's repeated-addition multiplication map.
- The final absence-of-restrictions clause is respected: no assumption on
  perfection of k, separability of f, or invertibility of n was introduced.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field); available transitively.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety` (def-sc-abelian-variety).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsIsogeny` (def-sc-isogeny), and the documented
  multiplication `𝟙 G ^ n` whose kernel is `torsionSubgroupScheme G n`
  (def-sc-mult-n). The torsion subgroup itself does not occur in the conclusion.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, with
  `CategoryTheory.IsMonHom` from `Mathlib.CategoryTheory.Monoidal.Mon`
  (def-sc-group-scheme). All statement-dependency modules are public imports.

The stated proof dependencies are plain imports. They provide
`CategoryTheory.GrpObj.ker` in
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`,
`IsAbelianVariety.isCommMonObj` in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic`,
`IsIsogeny.isFinite`, `IsIsogeny.flat`, and `IsIsogeny.finrank_eq` in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny`, and
`finite_commutative_group_scheme_order_annihilator` in
`Sheaf.AlgebraicGeometry.FiniteGroupSchemeOrderAnnihilator`.
The Mathlib imports supply `IsFinite`, `Scheme.fpqcPrecoverage`, its subcanonical
fpqc topology, and `Precoverage.mem_coverings_of_isPullback`. In particular the
representable-descent node is a Mathlib leaf: the subcanonical instance supplies
representable sheaves, and `Presieve.isSheafFor_arrows_iff_pullbacks` expresses
exactly the compatible-family existence and uniqueness needed here. No private
copy of a dependency or a missing interface is introduced.

Sources opened: the local PDF of Milne AV, I Remark 8.6, printed p.36, and
Proposition 8.10, printed pp.38-39; the local Algebraic Groups PDF, Proposition
11.32, printed p.221. The source node already explains that 8.10 discusses a
finite abstract group over an algebraically closed field; arbitrary-field,
nonreduced-kernel quotient descent is instead supplied by the existing fpqc
representable-descent leaf. The declaration docstring records all six DAG proof
steps, including both cancellations and verification of the descended group law.

Edge cases checked before writing:

- Identity isogeny and arbitrary isomorphisms: n = 1 and the inverse satisfy
  both equalities; in particular multiplication by one is the identity.
- Dimension-zero abelian varieties: the trivial group variety is included,
  and its identity isogeny again permits n = 1. Empty schemes are excluded by
  the group identity section, as in the source, rather than by an extra binder.
- Multiplication isogenies, including multiplication by the characteristic:
  n need not be invertible, and the statement retains nonreduced kernels.
- Frobenius-type inseparable isogenies and imperfect base fields are allowed:
  there is no reduced-kernel, etale, separability, or perfect-field hypothesis.
- n = 0 is deliberately excluded by `1 ≤ n`, exactly as the node requires.
  No fixed dimension, field cardinality, or additional universe restriction occurs.

Searches performed through the prescribed `msearch.py`, with actual outputs
recorded in the sandbox's `searches.jsonl`:

- LeanFinder: "An isogeny of abelian varieties admits a quasi inverse composing
  to multiplication by a positive integer". Eight hits, concerning
  Weierstrass-curve variable changes and inverse scheme isomorphisms; no match.
- Loogle: `"Isogeny"`. Zero hits.
- Mathlib grep: `isogen|quasiInverse`, subdirectory `AlgebraicGeometry`.
  Zero hits.
- LeanSearch: "A surjective homomorphism of abelian varieties with finite kernel
  admits a reverse homomorphism whose composites are multiplication by a
  positive integer". Eight hits, including abstract additive-group quotient
  results, additive lifts, and abelian-category epimorphisms; no scheme theorem.
- `rg` in the project's `WeilConjectures` and `Sheaf` sources for isogeny,
  quasi-inverse, `quasiInverse`, `quasi_inverse`, and `exists.*npow`.
  Found the definitions and isogeny finiteness/degree theorems, a torsion
  factorization theorem, and docstring references in DualIsogenyDegree,
  HomFiniteFree, and PolarizationCalculusOverField. None states this result.
- `grep -rn` for this exact node id in `lean/WeilConjectures` found nothing.
  The upstream declaration-name index has no matching isogeny quasi-inverse.

No statement dispute or node fault was found. The prescribed scompile.py run
compiled both the sandbox and library module cleanly (10.1 s and 3.1 s).

## Second reading by Q70

A second pass by the same worker reopened the node and final Lean signature;
no second agent was started, as the dispatcher prohibits delegation. The
maintainer supplies the independent review. This pass checked both Over objects
against the same `Spec k`, the two separate group structures, and both abelian
variety instances. The isogeny class contains exactly the required surjectivity,
homomorphism, and finite-kernel assumptions. The witness is positive, and the
reverse arrow carries `IsMonHom`. Composition order was checked explicitly:
`f ≫ g` is v ∘ u on A and `g ≫ f` is u ∘ v on B. The same n occurs in both
pointwise powers. No field or characteristic restriction appears. Every variable
and universe is bound, with auto-implicit variables disabled. No mismatch was
found and no statement correction was made.
