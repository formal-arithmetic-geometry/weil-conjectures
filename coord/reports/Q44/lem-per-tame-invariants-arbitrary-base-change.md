## Worker report

The module `Sheaf.DeligneLaumon.TameInvariantsArbitraryBaseChange` defines the
canonical invariant restriction map and states
`AlgebraicGeometry.tame_invariants_arbitrary_base_change`, with proof `sorry`.
The helper `invariantLinearMap` is a real `LinearMap.codRestrict` construction;
no definition contains postponed data. The other helpers define the fixed
B-submodule, its canonical tensor map, the fixed B-subalgebra, and its canonical
algebra map.

The binders render the hypotheses as follows. `A` is a commutative ring;
`G` has `[Group G] [Fintype G]`; `M` is an additive commutative group with an
`A`-module structure and `ρ : Representation A G M`; `d : ℕ`,
`hd : Fintype.card G = d`, and `hunit : IsUnit (d : A)` give the finite order
and its invertibility. The Reynolds operator is
`(↑(hunit.unit⁻¹) : A) • ∑ g : G, ρ g`.

The first conjunction states its idempotence by `e.comp e = e`, its image by
`Set.range e = (ρ.invariants : Set M)`, and its identity restriction by
`∀ x : ρ.invariants, e x = x`. For each commutative `A`-algebra `B` in its
own universe, `tameInvariantsBaseChangeMap ρ B` is the canonical map
`B ⊗[A] ρ.invariants →ₗ[B] tameBaseChangeFixedSubmodule ρ B`, whose codomain is
the intersection of the equalizers of `LinearMap.baseChange B (ρ g)` and the
identity. The theorem states this named map is bijective. Its pure-tensor map
is the `TensorProduct.AlgebraTensorModule.map` of the identity and the
invariant inclusion, corestricted to that fixed submodule.

The next clause quantifies independently over `B`, `B'`, and an `A`-algebra map
`vB : B →ₐ[A] B'`; its equality is the commuting square formed by the two
named canonical maps and the two induced tensor maps. The equivariant-map clause
quantifies independently over `N`, a representation `σ`, an `A`-linear map `f`,
and its intertwining equations. `invariantLinearMap ρ σ f hcomm` supplies the
map on invariant submodules, and the displayed equality is the square formed by
that named map, the two canonical base-change maps, and the tensor map of `f`.
No arbitrary map satisfying a pure-tensor formula is quantified.

For each `B` and independently chosen commutative `A`-algebra `C` carrying
`[MulSemiringAction G C] [SMulCommClass G A C]`, the final clause states that
the canonical `tameInvariantsAlgebraBaseChangeMap` is bijective. Its domain is
`B ⊗[A] FixedPoints.subalgebra A C G`; its codomain is the fixed B-subalgebra
`tameBaseChangeFixedSubalgebra A G B C`, the intersection of the equalizers of
`Algebra.TensorProduct.map (AlgHom.id B B) (MulSemiringAction.toAlgHom A C g)`
and the identity. Thus the algebra map is onto the fixed subalgebra, not onto
all of `B ⊗[A] C`. The universes for `B`, `B'`, `C`, and `N` are independent.

The only statement dependency is `def-weil-pbc-module-tensor-product`, whose
recorded Mathlib declaration is `TensorProduct` in
`Mathlib/LinearAlgebra/TensorProduct/Defs.lean`; the module uses Mathlib's
`TensorProduct` notation and maps directly. Other declarations used are
`Representation.invariants`, `LinearMap.baseChange`, `FixedPoints.subalgebra`,
`MulSemiringAction.toAlgHom`, and `TensorProduct.AlgebraTensorModule.map`.

Edge cases checked include the trivial group, `d = 1`, the zero module, zero
scalar algebra, non-flat scalar maps, and independent universe levels. The
invertible-order hypothesis is necessary: the sign action of `Z/2` on `Q`
becomes non-invariant after characteristic-two base change when invertibility is
removed.

Searches made: `msearch.py` LeanFinder query
`tame invariants arbitrary base change`, LeanSearch query
`invariants of a finite group module commute with any tensor base change if group order is invertible`,
Loogle query `Representation.invariants, TensorProduct`, and Mathlib grep query
`invariant.*baseChange|baseChange.*invariant|Reynolds`. They found only
`Representation.averageMap`, `averageMap_invariant`, `averageMap_id`, and
unrelated base-change declarations. `rg` over
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
`lean/Sheaf` found no existing comparison. No `STATEMENT-DISPUTED` flag applies.

## Second reading by Q44

I reopened the corrected node and module. The finite-group, cardinality, and
unit hypotheses are all present. The Reynolds clauses are explicit. The
base-change map is the named canonical map into the fixed B-submodule, and the
algebra map is the named canonical map into the fixed B-subalgebra. The two
naturality clauses use those named maps and quantify over no arbitrary map.
`B`, `B'`, `C`, and `N` have independent universe variables. The module compiles
with only the expected theorem-sorry warning.

## Statement corrected

The old statement asserted a map onto all of `B ⊗_A M` and an algebra map onto
all of `B ⊗_A C`; it also described naturality using arbitrary maps satisfying
the pure-tensor formula and forced `B`, `B'`, `C`, and `N` into the same
universes. A sign action of `Z/2` on `Q` disproves the old surjectivity clauses,
and the arbitrary-map naturality clauses are tautological. Following Stacks
Tag 0H36 (remark-when-iso) and its Reynolds argument, the statement now
corestricts both canonical maps to the explicitly defined fixed B-submodule or
fixed B-subalgebra, states squares for those named maps, and uses independent
universes.

The citer `lem-per-gabber-abelian-stage-toric-chart` holds: its proof uses the
Reynolds projection and fixed-subalgebra consequences supplied by the corrected
statement. No dependency or proof field changed.
