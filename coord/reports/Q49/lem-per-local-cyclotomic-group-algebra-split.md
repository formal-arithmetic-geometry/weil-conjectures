## Worker report

The module `Sheaf.RepresentationTheory.LocalCyclotomicGroupAlgebraSplit` states
`MonoidAlgebra.exists_algEquiv_pi_matrix_local_cyclotomic`. Its hypotheses render the
node's integer `N ≥ 1` as `N : ℕ` and `hN : 0 < N`; the finite group as
`G : Type v` with `[Group G] [Finite G]`; the exponent condition as
`hG : ∀ g : G, g ^ N = 1`; and the primitive complex root as
`ζ : ℂ` with `hζ : IsPrimitiveRoot ζ N`. The coefficient ring is the subalgebra
`A : Subalgebra ℤ ℂ` with `hA : A = Algebra.adjoin ℤ {ζ, (N : ℂ)⁻¹}`.
The prime is `p : Ideal A` with `[p.IsPrime]`, and the local ring is `Λ : Type u`
with `[CommRing Λ]`, `[Algebra A Λ]`, and `[IsLocalization.AtPrime Λ p]`.
The conclusion gives `r : ℕ`, `d : Fin r → ℕ`, positivity `0 < r` and
`∀ i, 0 < d i`, and a nonempty `Λ`-algebra equivalence from
`MonoidAlgebra Λ G` to the finite product of square matrix algebras
`Π i : Fin r, Matrix (Fin (d i)) (Fin (d i)) Λ`.

The dependency declarations used are `Localization.AtPrime` from
`Mathlib.RingTheory.Localization.AtPrime.Basic` and `Matrix` from
`Mathlib.LinearAlgebra.Matrix.Defs`; their records are used through the types and
instances above. The proof dependencies are named in the declaration docstring:
`exists_prime_orderOf_dvd_card'`, `Algebra`, `lem-per-cyclotomic-local-ring-dvr`,
`lem-per-cyclotomic-field-brauer-splitting`, finite torsion-free freeness, and the
matrix adjugate identities. The proof is intentionally `sorry` at stage 2.

Edge cases checked: `N = 1` and the trivial group (then the conclusion permits
`r = 1`, `d 0 = 1`); a prime ideal with zero localization prime (the field case);
`r` and every `d i` are explicitly positive, so the product is nonempty and has no
zero matrix blocks; arbitrary finite groups, including nonabelian groups, are allowed.
The index universe is `Fin r` in the coefficient-ring universe, and the group algebra
uses Mathlib's canonical `MonoidAlgebra`, so no special case is excluded.

Searches made: `msearch.py ... leanfinder` for a finite group algebra over a local
cyclotomic ring (cyclotomic-extension declarations only, no match); `msearch.py ...
loogle 'MonoidAlgebra, Matrix'` (zero hits); `msearch.py ... leansearch` for the
integral splitting statement (field Wedderburn--Artin and Maschke hits only); and
`msearch.py ... grep` plus `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`
(no exact declaration). The source search found the consumer
`AlgebraicGeometry.exists_tame_smooth_representation_chart`, which uses this node.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q49

I reread the node and module. The exponent, finite-group, primitive-root, subalgebra,
prime-localization, and algebra-instance hypotheses all appear one-for-one. The
conclusion has exactly the positive number of blocks, positive matrix dimensions,
and the requested product algebra equivalence. `MonoidAlgebra` and `Matrix` are the
recorded canonical notions. No mismatch was found.
