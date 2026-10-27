## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RationalBoundaryPositiveStabilizer` states
`AlgebraicGeometry.exists_rational_boundary_positive_stabilizer` with proof `sorry`.
It uses a bundled `Over (Spec k)` group scheme `G`, with `GrpObj G`, smoothness,
connectedness, separatedness, locally finite type and quasi-compact structure morphism, and
assumes `¬ IsProper G.hom`. The witness `X` is a scheme over `Spec k`; `j : G ⟶ X` is an
open immersion whose image is dense, `X` is integral and proper, and every local ring of
`X` is an integrally closed domain. The point `P` is represented by a `k`-point
`𝟙_ (Over (Spec k)) ⟶ X` whose image lies in the complement of `j(G)`.

The rational action is rendered by a partial map
`a : (G ⊗ X).left.PartialMap X.left` together with the maximal-domain equation
`a.domain = a.toRationalMap.domain`. Its restriction to `G × G` is rendered by
`t : (G ⊗ G).left ⟶ a.domain.toScheme`, with
`t ≫ a.domain.ι = (𝟙 G ⊗ₘ j).left` and
`t ≫ a.hom = μ[G].left ≫ j.left`; these clauses say that it extends left
multiplication on the dense open `G`. The open neighbourhood `V` is the inverse image of
`a.domain` under `g ↦ (g,P)`, written
`(lift (𝟙 G) (toUnit G ≫ P)).left ⁻¹ᵁ a.domain`, and it contains the identity section.

The subgroup witness is `i : S ⟶ G`, with `GrpObj S`, `IsClosedSubgroupScheme i`, and
`IsReduced S.left`. Its kernel ideal is the vanishing ideal of the closure of exactly the
points `g` for which a lift `q` of `(g,P)` lies in the maximal domain and satisfies
`q ≫ a.hom = P.left`; this renders the reduced Zariski closure of
`{g ∈ V(k) | α(g,P)=P}`. The final inequality
`(1 : WithBot ℕ∞) ≤ topologicalKrullDim S.left` is the positive-dimensional conclusion.

Dependencies used are the existing group-scheme declarations in
`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (`GrpObj`,
`IsClosedSubgroupScheme`), Mathlib's `Scheme.RationalMap` and
`Scheme.PartialMap`, `AlgebraicGeometry.IsIntegral`, `IsProper`, `IsOpenImmersion`,
`topologicalKrullDim`, `IsIntegrallyClosed`, `CategoryTheory.Limits.pullback` and
`Scheme.IdealSheafData.vanishingIdeal`, plus
`Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound` for the stated proof route.

Edge cases checked: `G = \mathbb G_a` and `G = \mathbb G_m` with the usual boundary in
`\mathbb P^1`; zero-dimensional groups are excluded by the non-proper smooth connected
hypothesis and the conclusion's positive dimension; the empty scheme is excluded by
`IsIntegral`; nonreduced candidate closures are handled by `IsReduced S.left` and the
vanishing ideal; no affineness or normality of `S` is asserted.

Searches made: `msearch.py ... leanfinder` for a nonproper smooth connected algebraic group
with a boundary point and positive-dimensional rational stabilizer (hits concerned modular
cusps and abstract stabilizers; no match); `msearch.py ... loogle '"Scheme", "stabilizer"'`
(0 hits); `msearch.py ... grep 'rationalAction|rational_action|boundary.*stabilizer|stabilizer.*dimension'`
under `AlgebraicGeometry` (0 hits). Direct `rg` over `lean/Sheaf` and
`lean/WeilConjectures` found no such theorem. The Mathlib rational-map search found the
maximal-domain declarations `RationalMap.domain`, `RationalMap.toPartialMap`,
`PartialMap.le_domain_toRationalMap`, and `RationalMap.toRationalMap_toPartialMap`; these
are the interfaces used by the statement.

No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by Q97

I reread the node and the complete Lean signature. The field, algebraic-closure, group-scheme,
subgroup, smoothness, connectedness, finite-type, separatedness, dimension, integrality,
fibre-product and open-immersion notions are all supplied by the listed dependencies or exact
Mathlib declarations. The non-proper hypothesis is exactly `¬ IsProper G.hom`. The witnesses
match the source objects `X`, `j`, `P`, `V`, `α` (represented by `a` and `t`) and `S`.
The maximal-domain clause, boundary membership, identity-in-`V` clause, stabilizer closure
ideal, closed-subgroup conclusion and dimension lower bound are each present. The statement
adds no global regular action, affineness, normality or connectedness claim for `S`; `X`'s
normality is rendered by the explicit local-domain and integrally-closed stalk conjunction.
The source's rational-map equivalence class is represented by Mathlib's `PartialMap`/
`RationalMap` pair, with the maximal representative equation making the correspondence
explicit. No mismatch was found.
