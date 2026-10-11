## Worker report

The delivered statement correction was reverted (H7): it named an error in the earlier Lean, not
in the node, and replaced the node by a weaker text with an arbitrary scheme X', an arbitrary
additive equivalence ι, an arbitrary ring map ρ and arbitrary subgroups L, L', and units of k(X)
instead of units of O_C(C). The node keeps its sheaf-dag statement.

The Lean is restated against that node. `AlgebraicGeometry.affine_unit_divisor_base_change`
binds k ⊆ k' algebraically closed, C with `f : C ⟶ Spec (.of k)`, `[IsConnectedCurve f]
[Smooth f] [IsAffine C]`, and `c : Compactification f` with `[IsConnectedCurve c.g] [Smooth c.g]`
(properness is a field of `Compactification`). The base change is `c.baseChange t` for
`t = Spec.map (CommRingCat.ofHom (algebraMap k k'))`, with C' = `pullback f t` (BASE CHANGE X_T).
The conclusion asserts integrality and noetherianity of X and X' (needed for `Scheme.div`),
the restriction maps φ, φ' from global sections into the function fields (tied to the germs
through the stalk maps of the open immersions), a bijection e between the boundaries
S = {closed P ∉ range c.i} and S' with each P' the only point of X' over P, and, with
ι = `Finsupp.domCongr e`: for each unit u of Γ(C, ⊤), the boundary part
(`Finsupp.subtypeDomain`) of `div` of the pullback u' (`appTop` of `pullback.fst f t`) equals ι
of the boundary part of `div u`; and ι maps the set of boundary divisors of units on C onto
the set on C'. Divisors are the landed `Scheme.Divisor` / `Scheme.div`.

## Second reading by R1

Superseded by reviewer R-udb: the statement correction of the second reading was reverted
(H7) and the Lean restated against the sheaf-dag node as described above.
