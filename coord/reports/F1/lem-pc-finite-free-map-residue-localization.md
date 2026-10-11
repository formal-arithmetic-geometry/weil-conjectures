## Worker report

The module states `Module.finiteFreeMap_residue_localization` with a `sorry` proof.
It is the finite-free matrix specialization of Stacks Project, Algebra, Tag 00O0,
parts (1) and (3). The repository's `literature/stacks-project/algebra.tex` was
absent on this machine; the same Stacks source was read at
`/home/ubuntu/c1-stacks-review/algebra.tex`, lines 19472-19555.

- `R : Type*` and `[CommRing R]` render the commutative ring (Stacks' ring
  convention); `m n : ℕ` and `Fin m → R`, `Fin n → R` render the two finite
  free modules, including rank zero; `u : ... →ₗ[R] ...` is their map.
- `p : Ideal R` and `[p.IsPrime]` render the prime ideal. The residue-field
  map is `u.baseChange p.ResidueField`, namely extension of scalars to
  `κ(p)`; `Function.Injective` is the first hypothesis.
- The first `∃ f : R, f ∉ p` is the principal neighborhood. The map on
  `R_f` is `u.baseChange (Localization.Away f)` and its injectivity is
  `Function.Injective`.
- The cokernel is the quotient of the target tensor product by
  `LinearMap.range (u.baseChange (Localization.Away f))`. Its finite-free
  property is stated by both `Module.Finite` and `Module.Free` over
  `Localization.Away f`; this includes the zero cokernel.
- `Function.Bijective (u.baseChange p.ResidueField)` renders the second
  hypothesis, since an isomorphism of modules is equivalent to a bijective
  linear map. Its own `∃ f : R, f ∉ p` and `Function.Bijective
  (u.baseChange (Localization.Away f))` render the second conclusion.

Dependency declarations used: `Module.Free` from
`Mathlib.LinearAlgebra.FreeModule.Basic`; `LocalizedModule.Away` from
`Mathlib.Algebra.Module.LocalizedModule.Basic` identifies module localization
with tensor base change to `Localization.Away f`; `Module.Projective` from
`Mathlib.Algebra.Module.Projective` was read as the project's projective
module notion, though the finite-free conclusion does not require it.
`LinearMap.baseChange` is from `Mathlib.LinearAlgebra.TensorProduct.Tower`.

Edge cases: `m = 0` makes the first injectivity premise automatic and leaves
the target finite free; `n = 0` with `m > 0` cannot satisfy injectivity over
the nonzero residue field; `m = n = 0` satisfies both clauses with `f = 1`.
The prime ideal hypothesis excludes a zero-ring residue field. No finiteness
or Noetherian condition is imposed on `R`.

Searches: `msearch.py ... leanfinder` with the plain-language finite-free
residue-field localization claim found local-ring splitting and finite
presentation lemmas, no exact principal-localization statement.
`msearch.py ... loogle` with `LocalizedModule.Away, Module.Free,
LinearMap.baseChange` returned zero hits. `msearch.py ... grep` for
`residueField.*injective|injective.*residueField|exists.*notMem.*bijective`
in `RingTheory` found related residue-field and bijectivity lemmas, no match.
`rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`,
plus `grep -rn` for the node id in `WeilConjectures`, found no declaration
stating this node. Source searches found only nearby local-ring and
finite-presentation results, not this conjunction.

## Second reading by F1

I opened the node, its three dependency records, the Stacks source at Algebra Tag 00O0
(`lemma-cokernel-flat`), and the module. The node introduces a commutative ring `R`,
natural numbers `m,n`, a map `u : R^m -> R^n`, and a prime ideal `p`; the Lean binders
`{R : Type*} [CommRing R] (m n : ℕ) (u : (Fin m → R) →ₗ[R] (Fin n → R))
(p : Ideal R) [p.IsPrime]` render exactly these objects. `Fin m → R` and `Fin n → R`
are the finite free modules, including rank zero, and no Noetherian, finiteness, or
universe restriction is added.

The first hypothesis is exactly `Function.Injective (u.baseChange p.ResidueField)`.
Its conclusion is rendered by `∃ f : R, f ∉ p`, followed by injectivity of
`u.baseChange (Localization.Away f)` and `Module.Finite` plus `Module.Free` for
`TensorProduct R (Localization.Away f) (Fin n → R) ⧸
LinearMap.range (u.baseChange (Localization.Away f))`. This quotient is the cokernel
of the localized map, and the two class predicates state finite free as required.
The second hypothesis is exactly bijectivity of the residue-field base change, and
its conclusion is the same principal-neighborhood quantifier with bijectivity of the
localized base change. The conjunction and implication order is unchanged.

Edge cases checked: `m = 0` gives the zero-domain injective case; `n = 0` with
`m > 0` cannot satisfy injectivity over the nonzero residue field; `m = n = 0`
works with `f = 1`; the prime-ideal instance excludes the degenerate zero-ring
residue field; empty and zero free modules are allowed. The arbitrary `Type*` universe
does not remove any case in the node.

Searches were repeated with LeanFinder/Loogle/grep over Mathlib, `WeilConjectures`,
`lean/Sheaf`, and `dag/lean_names_upstream.json`; no exact declaration exists. The
recorded dependency declarations are the Mathlib notions `Module.Free` and
`LocalizedModule.Away`; `Module.Projective` is not needed by this finite-free
specialization. The source file available on this machine was
`/home/ubuntu/c1-stacks-review/algebra.tex`, lines 19472--19555.

The only mismatch found was documentation: the worker docstring gave a summary but
not the node proof step by step with its source place, violating H8. I replaced it
with explicit determinant/block-matrix and adjugate steps. The Lean statement itself
was unchanged and compiled cleanly.
