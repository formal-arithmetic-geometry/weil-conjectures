## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit` states
`AlgebraicGeometry.rho_regular_weyl_orbit` with one `sorry` and no definitions.
The source is Milne, *Algebraic Groups* (2017), Appendix C.21--C.22 and Summary
21.41/Definition 21.72. The statement keeps the fixed algebraically closed field,
reductive group, split maximal torus, Borel, root datum, character/cocharacter
pairing, and normalizer quotient Weyl group from the node.

The Lean rendering is clause by clause as follows.

- `{F : Type u} [Field F] [IsAlgClosed F]` renders the algebraically closed field.
  `G : Grp (Over (Spec (.of F)))` with `hG` renders the reductive group scheme.
- `T`, `iT`, `hT`, and `hsplit` render a split maximal torus; `B`, `iB`, `hB`,
  `j`, and `hj` render a Borel containing it.
- `aG`, `aB`, `Φ`, `P`, and `b` render the character lattice actions, finite root
  datum, and simple-root base. `hconjG`, `hconjB`, `hroot`, `hpair`, `hweights`,
  and `hpos` pin these to the conjugation actions, the integer character pairing,
  the nonzero tangent weights, and the positive roots from the Borel. `[P.IsReduced]`
  is the reducedness hypothesis from the recorded root datum.
- `ρ : TensorProduct ℤ ℚ (Additive (...))` and `hρ` render the rational root span
  and `rho = (1/2) * sum_{positive roots} root`. The tensor factor order is
  `ℚ ⊗_ℤ X`, so the root tensor is `TensorProduct.tmul ℤ (1 : ℚ) (P.root β)`.
- The first conjunction gives pairing one with every simple root (`α ∈ b.support`).
- `act : RankOneRoots.Weyl iT →* Aut T` is the action of
  `W = N_G(T)(F)/T(F)`; the representative equation in the theorem pins it to
  `(wχ)(t)=χ(n_w⁻¹tn_w)`. `ract` is its canonical rational-linear extension,
  explicitly required on pure tensors.
- `∀ w, ract w ρ = ρ ↔ w = 1` is the trivial stabilizer clause.
- `w₀`, the image equality on `{β | b.IsPos β}`, `w₀ ^ 2 = 1`, `ract w₀ ρ = -ρ`,
  and the final universal equivalence render existence, uniqueness, involutivity,
  the negative half-sum, and the characterization `wρ=-ρ ↔ w=w₀`.
- The final implication for `Φ = ∅` states that the rational span is bottom, every
  Weyl element is the identity, and `w₀ = 1`, covering the rank-zero case.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure`: the full root datum, base,
  character/cocharacter lattices, positive-root characterization, and conjugation
  actions were read from its signature and docstring.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`,
  `AlgebraicGeometry.RankOneRoots.Weyl`, `normalizer`, and `torusInNormalizer`:
  these give the exact normalizer quotient `W` and its denominator. This landed
  definition was added to `stmt_deps` because the item uses the notion directly.
- Mathlib `Field` (`Mathlib/Algebra/Field/Defs.lean`, class declaration) and
  `IsAlgClosed` (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, class declaration).
- Mathlib `TensorProduct`, `LinearEquiv`, `Finset`, `Set`, and
  `RootPairing.Base.IsPos`; these are used only through their existing definitions.

Edge cases checked: the empty root system (torus or trivial group), rank-one `SL₂`
with upper-triangular Borel, products of rank-one factors, a non-simply-laced `A₂`
example where `w₀` is not `-1` on the whole character lattice, characteristic two,
and central torus directions. The tensor formulation leaves central directions
outside the root span and does not assume roots span the full character lattice.
The empty implication explicitly gives bottom span and trivial Weyl quotient.

Searches made before writing:

- `msearch.py ... leanfinder` for “half sum of positive roots pairs to one with
  simple coroots, has trivial Weyl stabilizer, and the unique longest Weyl element
  takes it to its negative”: returned only abstract `RootPairing`/Lie-algebra
  declarations, with no algebraic-group Weyl-orbit theorem.
- `msearch.py ... loogle 'RootPairing.Base, "sum"'`: returned base height and
  decomposition lemmas, not the stated rho conclusion.
- `msearch.py ... grep 'weylVector|halfSum|half_sum|longest|chamber'
  LinearAlgebra/RootSystem`: no matching declaration for this algebraic-group
  statement.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/nodes` for rho/half-sum/
  longest-Weyl declarations and the exact item id: no existing declaration or
  duplicate node was found. The only reusable local notion was the landed
  `def-sfb-rank-one-root-interfaces` Weyl quotient.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q14

I reopened the node and module. The field, reductive group, split torus, Borel,
root datum, positive system, and character pairing are all represented by explicit
binders. The rational space is the tensor product of the additive character lattice
with `ℚ`; `hρ` identifies the exact half-sum. The simple-root pairing clause is
indexed by `b.support`, while the stabilizer, root-reversal, involution, negative
half-sum, and uniqueness clauses quantify over the actual normalizer quotient
`RankOneRoots.Weyl iT`. The representative equation fixes the action convention.
The empty-root implication supplies the rank-zero conclusions. I found no mismatch
and made no changes during this rereading.
