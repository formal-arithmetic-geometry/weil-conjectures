## Worker report

The module `Sheaf.RingTheory.DirectedCoalgebraComoduleDescent` states
`Coalgebra.directed_colimit_coalgebra_comodule_descent`. It contains one theorem
with `sorry`, no definitions, no additional axioms, and no auxiliary statements.
The item's existing statement is unchanged; only its `lean` record is supplied.
No missing dependency interface or new definition node is needed.

Source read: Milne, Algebraic Groups (2017), printed p.178, the paragraph
“Proof of Theorem 9.32 in the general case” and Theorem 9.37. That paragraph
uses the directed system indexed by classes of objects and passes to the
coalgebra limit. The assigned node makes the finite-coefficient argument
underlying this passage explicit. The six proof steps of the node are all
carried in the theorem docstring, including tensor-colimit compatibility,
eventual equality, the two coefficient calculations, and the zero-dimensional
cases.

Hypotheses and their Lean renderings:

- The field is `{k : Type u} [Field k]`.
- The nonempty directed preorder is `{I : Type v} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Antisymmetry is not imposed.
- The vector spaces and linear transition maps are `F : I ⥤ ModuleCat.{v} k`.
  The transition for `h : i ≤ j` is `(F.map (homOfLE h)).hom`. Functor identity
  and composition laws express exactly the two system laws, since the category
  of a preorder has one arrow per inequality. The index and carrier universes
  share `v`, as required by the project's directed-colimit convention.
- `[∀ i : I, Coalgebra k (F.obj i)]` supplies the two linear maps and the three
  coalgebra identities. Mathlib's `Coalgebra.coassoc` includes the tensor
  associator; its two counit laws identify the results with `1 tensor x` and
  `x tensor 1`. These are precisely the node's identities under the unitors.
- `hΔ` says the transition preserves comultiplication, using `TensorProduct.map`
  on both transition maps. `hε` says it preserves the counit.
- The vector-space colimit with its legs is `(c : Cocone F) (hc : IsColimit c)`.
  This uses the recorded dependency's universal-property notion, rather than
  restricting to one chosen implementation of the colimit.

Conclusion, clause by clause:

- `∃ d : Coalgebra k c.pt` is existence of the colimit coalgebra structure.
- The first conjunct is `d.comul ∘ₗ iota_i = (iota_i tensor iota_i) ∘ₗ Delta_i`.
- The second conjunct is `d.counit ∘ₗ iota_i = epsilon_i`.
- The third conjunct quantifies over every other `d'` satisfying both of those
  equations and asserts `d' = d`. In particular uniqueness is among all
  compatible coalgebra structures, without imposing descent as an extra
  condition on the competitor.
- The fourth conjunct quantifies over every `M : Type w`, its additive and
  module structures, `[FiniteDimensional k M]`, and its linear `ρ`. Its two
  antecedents are coassociativity, using `TensorProduct.assoc`, and counitality,
  using `TensorProduct.rid`. Its witnesses are an index `i` and a linear `ρi`
  on exactly the same `M`, satisfying both coaction identities and
  `ρ = (c.ι.app i).hom.lTensor M ∘ₗ ρi`.
- The final conjunct quantifies over `i`, finite-dimensional `M : Type w` and
  `N : Type t`, two linear coactions and a linear map `a`. Four antecedents
  give the two coaction laws for each space. The last antecedent expresses
  colinearity after composing both coactions with `1 tensor iota_i`.
  The witnesses `(j : I) (h : i ≤ j)` give precisely colinearity after
  composing both coactions with `1 tensor u_ij`, with `a.rTensor (F.obj j)`
  expressing `a tensor 1`. Preservation of the coalgebra structure ensures
  these transported maps are coactions; no new structure is chosen there.
- There is no injectivity hypothesis, no finite-dimensionality hypothesis on
  any `F.obj i`, and no characteristic restriction.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.map`,
  `LinearMap.lTensor`, `LinearMap.rTensor`, and the associator and unitor from
  Mathlib.LinearAlgebra.TensorProduct; available through the coalgebra import.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit` from Mathlib.CategoryTheory.Limits.HasLimits
  and its public imports. These are explicitly listed in the dependency record.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs, the alias for `Module.Finite`.
- Proof dependency `lem-weil-pbc-filtered-colimit-tensor-varying-rings`:
  `TensorProduct.exists_unique_colimit_tensor_varying_rings`, in
  Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings (plain import).
- Proof dependency `def-weil-directed-colimit-abelian-groups`:
  `AddCommGroup.DirectLimit`, Mathlib.Algebra.Colimit.Module (plain import).
- Proof dependency `lem-weil-pbc-filtered-colimit-modules-elementwise`:
  `Concrete.isColimit_exists_rep`, `Concrete.isColimit_rep_eq_iff_exists`,
  `Concrete.colimit_rep_eq_zero`, and
  `ModuleCat.FilteredColimits.forget_preservesFilteredColimits`; their recorded
  modules are imported for the proof plan.

Edge cases checked before writing: empty `I` is excluded exactly as in the node;
`M = 0` has its unique zero coaction and requires only any index; for either
`M = 0` or `N = 0` colinearity holds at `j = i`. A zero coalgebra is allowed.
A singleton directed set reduces to a compatible isomorphism of colimits.
Nonantisymmetric preorders are allowed. Zero transition maps are allowed when
they preserve the counits; no cancellation is implicit in any equation.
The comultiplication need not be cocommutative. Independent universes `w,t`
allow different sizes for the two finite-dimensional carrier types.

Searches performed with the prescribed msearch wrapper (raw responses are in
`searches.jsonl`):

- LeanFinder: “Finite dimensional comodules over a directed colimit of
  coalgebras descend to a stage and colinearity is eventually detected”.
  Eight hits, including Module.DirectLimit.exists_of and module colimit facts;
  none states the simultaneous coaction and colinearity descent.
- Loogle: `Coalgebra, TensorProduct.map, colimit`. Zero hits, reporting the
  unqualified identifier `colimit` unknown. This is not used as evidence alone.
- Grep: `Comodule|comodule|coalgebra.*[Cc]olimit|[Cc]olimit.*coalgebra`.
  Five hits in Mathlib.CategoryTheory.Monad.Limits, about coalgebras for one
  fixed comonad. Those are not varying ordinary coalgebras or their comodules.
  Read that file's description and the relevant existing search evidence.
- LeanSearch: “A finite dimensional coaction over a filtered colimit of
  coalgebras descends to one coalgebra in the diagram”. Eight hits, about
  comonad coalgebras and underlying filtered-set equality; no exact match.
- `rg` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` found no proposed declaration/name already
  present. The required item-id search in `lean/WeilConjectures` found none.
  The concept search found the existing `FiniteSubcomodule` and
  `FiniteComoduleCoefficientCoalgebra` modules; read both, including their
  full signatures. They use the same explicit right-coaction equations but
  assert different finiteness results, so neither supplies this theorem.

No statement dispute, correction, new node, or dependency repair is needed.

## Second reading by ND

A second pass by the author compared the unchanged node and the full theorem
signature. The two coalgebra compatibility equations precede uniqueness;
uniqueness tests all compatible coalgebras; descent keeps `M` fixed; colinearity
uses `a tensor 1` with the correct source and target tensor factors. All four
coaction hypotheses for `M,N` are present. Associators have direction
`(M tensor D) tensor D` to `M tensor (D tensor D)`, and the right unitor makes
the counit equality a map from `M` to `M`. No mismatch was found in this pass.
This is an author rereading, not a claimed independent agent review; the
assignment forbids starting other agents and assigns independent review to
the maintainer.

Validation: the prescribed `scompile.py` checked the delivered file separately
in sandbox mode and at its actual library module path. Both checks completed
without errors or warnings. The theorem proof remains exactly `by sorry`.
