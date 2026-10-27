## Worker report

The module `Sheaf.RingTheory.DirectedCoalgebraComoduleDescent` states
`Coalgebra.exists_directed_colimit_comodule_descent`, with its sole proof `sorry`.
It asserts all three parts of the node: the unique compatible coalgebra structure on
an arbitrary vector-space colimit cocone, finite-dimensional coaction descent on the
same vector space, and eventual colinearity for a fixed linear map. No new definitions,
new nodes, dependency repairs, or statement corrections are needed. The node copy
changes only `lean`.

Read Milne, *Algebraic Groups* (2017), printed p.178 (PDF page 190), especially
Theorem 9.37 and the paragraph immediately preceding it. This is the directed-limit
step for the reconstruction coalgebra. The node gives the explicit finite-coefficient
argument underlying that step; all six of its proof steps are in the theorem docstring.

Hypotheses and conclusions are rendered as follows.

| Node clause | Lean rendering |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| Nonempty directed preorder I | `{I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]` |
| Vector spaces D_i and linear transition maps u_ij | `F : I ⥤ ModuleCat.{v} k`; `F.obj i` and `(F.map (homOfLE h)).hom` |
| Identity and composition laws of u | The functor's `map_id` and `map_comp`; the preorder category has one arrow for each inequality |
| Comultiplication, counit, coassociativity, both counit identities at every stage | `[∀ i : I, Coalgebra k (F.obj i)]`; Mathlib's `Coalgebra` has exactly this linear data and these three axioms |
| Transitions preserve comultiplication | `hcomul`, the equality between `comul ∘ₗ u` and `TensorProduct.map u u ∘ₗ comul` |
| Transitions preserve counit | `hcounit`, the equality `counit ∘ₗ u = counit` |
| Given vector-space colimit (D,iota_i) | `(c : Cocone F) (hc : IsColimit c)`; `D = c.pt`, `iota_i = (c.ι.app i).hom`. This is any specified colimit, not a specially chosen carrier |
| Existence of coalgebra structure on D | `∃ d : Coalgebra k c.pt` |
| Delta iota_i = (iota_i tensor iota_i) Delta_i | First equality in the first conjunct under `∀ i` |
| epsilon iota_i = epsilon_i | Second equality in that conjunct |
| Uniqueness of compatible coalgebra structure | Next conjunct quantifies over every `d' : Coalgebra k c.pt` and asserts `d' = d` assuming just those two compatibility equalities, independently of descent properties |
| Any finite-dimensional vector space M and linear right coaction rho | First universal conjunct: `(M : Type w) [AddCommGroup M] [Module k M] [FiniteDimensional k M] (ρ : M →ₗ[k] M ⊗[k] c.pt)` |
| Coassociativity of rho | `(TensorProduct.assoc ...).toLinearMap ∘ₗ ρ.rTensor c.pt ∘ₗ ρ = d.comul.lTensor M ∘ₗ ρ` |
| Counitality of rho | `(TensorProduct.rid k M).toLinearMap ∘ₗ d.counit.lTensor M ∘ₗ ρ = LinearMap.id` |
| Some stage i and a right D_i-coaction on the same M | `∃ (i : I) (ρi : M →ₗ[k] M ⊗[k] F.obj i)` followed by its coassociativity and counit equalities |
| rho = (1_M tensor iota_i) rho_i | `ρ = (c.ι.app i).hom.lTensor M ∘ₗ ρi` |
| Fixed stage i, finite-dimensional right D_i-comodules M,N, linear a | Final conjunct quantifies over `i`, independent carrier universes `w,t`, both module and finite-dimension instances, the maps `ρM`, `ρN`, and `a : M →ₗ[k] N` |
| Both source coactions satisfy their identities | Four explicit antecedents: coassociativity and counitality for each of `ρM` and `ρN` |
| a is colinear after extension to D | `(c.ι.app i).hom.lTensor N ∘ₗ ρN ∘ₗ a = a.rTensor c.pt ∘ₗ (c.ι.app i).hom.lTensor M ∘ₗ ρM` |
| Some j >= i with a colinear after composing with 1 tensor u_ij | `∃ (j : I) (h : i ≤ j)` and the identical square with `(F.map (homOfLE h)).hom` in place of the colimit leg |
| No injectivity or finite-dimension assumption on D_i | Neither occurs among the binders or hypotheses |

The coactions after a transition really satisfy their coaction identities: this follows
from `hcomul` and `hcounit`, as explained in proof step 6. The final square uses precisely
these composed coactions, without an arbitrary replacement map. The tensor associator
turns `(M tensor D) tensor D` into `M tensor (D tensor D)`, and `rid` identifies
`M tensor k` with M. Thus each equation has the node's right-comodule tensor order.
No cocommutativity, multiplication, Hopf structure, or group action is assumed.

Dependency interfaces read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, supplied publicly
  through the coalgebra import.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`, `TensorProduct.map`, and
  `LinearMap.lTensor`/`rTensor` in `Mathlib.LinearAlgebra.TensorProduct.{Defs,Basic,Map}`.
  Associativity and unit maps come from `Mathlib.RingTheory.Coalgebra.Basic`'s imports.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and `IsColimit`
  (read their complete structures in `Limits.Cones` and `Limits.IsLimit`) publicly
  imported through `Mathlib.CategoryTheory.Limits.HasLimits`, the recorded module.
  The recorded chosen `colimit` is a special case of the arbitrary cocone used here.
- `def-weil-finite-dimensional-subspace`: Mathlib `FiniteDimensional`, the alias of
  `Module.Finite`, publicly imported from `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.

Proof-only dependency imports:

- `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`:
  `TensorProduct.exists_unique_colimit_tensor_varying_rings`, for identifying the
  diagonal tensor colimit.
- `Mathlib.Algebra.Colimit.Module`: `AddCommGroup.DirectLimit`, its stage maps,
  representatives, eventual equality, and universal map.
- `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`:
  `ModuleCat.FilteredColimits.forget_preservesFilteredColimits`.
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures`:
  the recorded `Concrete.isColimit_exists_rep`, `Concrete.isColimit_rep_eq_iff_exists`,
  and zero detection. The first two are in its imported `ConcreteCategory.Basic`.

Edge cases checked before writing:

- I cannot be empty, exactly as in the node. A singleton and a directed preorder
  with distinct equivalent indices are admitted; no antisymmetry is assumed.
- For M = 0 the finite coefficient family is empty and nonemptiness of I supplies
  a stage. The statement requires no nonzero carrier and no positive dimension.
- If either M or N is zero, the colinearity defects are empty and j = i works.
- The zero coalgebra and diagrams of zero coalgebras are allowed. A coaction over
  the zero coalgebra is only possible on a zero space, as its counit equation requires.
- Noninjective transitions are allowed, for example the map from the coalgebra on
  two group-like basis elements to k that sends both basis elements to 1. The proof
  detects eventual zero coefficients rather than canceling transition maps.
- No finite-dimensionality of the stages, characteristic restriction on k, or
  injectivity of the colimit legs appears.
- I and the diagram's carrier size use v, in accordance with the project's index
  universe convention. The coefficient field has its own u and the two comodule
  carriers have independent w,t; the colimit is any cocone in this module category.

Searches for an exact existing statement:

- `msearch.py`, LeanFinder: `Finite dimensional coactions and colinear maps descend
  along a directed colimit of coalgebras`. Eight hits, including
  `ModuleCat.directLimitIsColimit_desc`, `DirectLimit.Module.of_f`, and module
  direct-limit lift lemmas. These provide universal properties but none gives
  finite coaction descent or eventual colinearity.
- `msearch.py`, Loogle: `Coalgebra, TensorProduct.map`. Twelve hits, including
  product coalgebra identities and `CoassocSimps.map_counit_comp_comul_left`.
  None concerns directed limits or finite comodules.
- `msearch.py`, grep: `Comodule|coaction|coalgebra.*colimit`. Five hits in
  `CategoryTheory.Monad.Limits`: coalgebras for a fixed comonad, not changing
  coefficient coalgebras or finite-dimensional coactions.
- `rg` in the project's `lean/Sheaf` and `lean/WeilConjectures` for comodule,
  coaction, and coalgebra-colimit terms: existing finite-subcomodule and coefficient
  coalgebra modules use the same explicit right-coaction identities, but neither
  states directed-limit descent. Relative Hopf coactions add multiplication and
  extra module actions and do not express the general coalgebra setting here.
- `rg` in Mathlib's coalgebra and linear-algebra directories: coalgebras and tensor
  products exist, but no general algebraic comodule structure or matching theorem.
- Searched the item id in `lean/WeilConjectures`, and the proposed declaration name
  in both project roots, Mathlib, and `dag/lean_names_upstream.json`: no matches.

No `STATEMENT-DISPUTED` issue or node fault was found. The theorem and its library
module both compiled through `scompile.py` with no errors or warnings. The only
postponed theorem is the named item theorem; no data or definition contains `sorry`.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
