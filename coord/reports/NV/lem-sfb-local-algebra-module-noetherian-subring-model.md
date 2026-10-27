## Worker report

The module `Sheaf.RingTheory.LocalAlgebraModuleNoetherianSubringModel` states
`Algebra.exists_local_algebra_module_noetherian_subring_model`, with `sorry` as its only
proof. No definitions, additional nodes, dependency repairs or statement corrections are
needed. The item's node changes only in `lean`.

The inherited BLOCKED conclusion confused a reviewed stage-1 split with a stage-2 statement.
The live node has no `lean` or `reviewed_lean`, and `coord/queue.tsv` lists it in stage 2.
The Q86 PASS reviewed the natural-language proof, not a Lean statement. The stage-handoff
instruction in `coord/brief-stage2.md` §0 therefore applies; this delivery preserves that split.

Source read: `literature/stacks-project/flat.tex`, Tag 0AT8,
`lemma-find-pure-spreadout`, especially the paragraph choosing the local subring `A₀`,
the algebra `B₀`, and the module `N'₀` (lines 7270–7302). The node's accepted proof supplies
the finite-presentation coefficient construction that the source leaves implicit.

Hypotheses and clauses, matched individually:

- Commutative local ring `(R,m)`: `(R : Type u) [CommRing R] [IsLocalRing R]`.
  Its unique maximal ideal is `IsLocalRing.maximalIdeal R`.
- Finitely presented commutative `R`-algebra `C`: `(C : Type v) [CommRing C]
  [Algebra R C] [Algebra.FinitePresentation R C]`.
- Finitely presented `C`-module `M`: `(M : Type w) [AddCommGroup M] [Module C M]
  [Module.FinitePresentation C M]`. The binders `[Module R M] [IsScalarTower R C M]`
  express the restriction of this action along `algebraMap R C`. They are structure
  bookkeeping: the tower forces `r • m = algebraMap R C r • m`, so no additional
  mathematical hypothesis on `M` is imposed. Every `C`-module has this restriction.
- Unital subring: `∃ (R₀ : Subring R)`. Mathlib's `Subring` contains `1` and its
  canonical inclusion is `R₀.subtype`.
- Locality and the specified maximal ideal: `∃ (_ : IsLocalRing R₀)` and
  `IsLocalRing.maximalIdeal R₀ = (IsLocalRing.maximalIdeal R).comap R₀.subtype`.
  Ideal comap is exactly intersection with the ambient maximal ideal in this subring.
- Noetherianity: `IsNoetherianRing R₀`.
- Essentially finite type over the integers: `Algebra.EssFiniteType ℤ R₀`, using
  the canonical integer algebra structure on a commutative ring.
- Finite generation of the maximal ideal: `(IsLocalRing.maximalIdeal R₀).FG`.
- Finitely presented commutative model algebra: the existential `C₀`, its `CommRing`
  and `Algebra R₀ C₀` structures, and `Algebra.FinitePresentation R₀ C₀`.
- Algebra base-change isomorphism: `α : R ⊗[R₀] C₀ ≃ₐ[R] C`.
- The specified map `C₀ → C`: an existential `Algebra C₀ C` with
  `∀ c₀, algebraMap C₀ C c₀ = α (1 ⊗ₜ[R₀] c₀)`. This equation determines the
  ring map and its action uniquely; the map is not an arbitrary comparison.
- Finitely presented module model: existential `M₀`, its `AddCommGroup` and
  `Module C₀ M₀` structures, and `Module.FinitePresentation C₀ M₀`. The auxiliary
  `Module R₀ M₀` and scalar tower specify the unique restricted action, as for `M`.
- Module base-change isomorphism: `β : C ⊗[C₀] M₀ ≃ₗ[C] M` under the algebra
  structure determined by the preceding equation.
- The canonical balanced map is an `R`-linear isomorphism:
  `γ : R ⊗[R₀] M₀ ≃ₗ[R] M`, with
  `∀ r x, γ (r ⊗ₜ[R₀] x) = r • β (1 ⊗ₜ[C₀] x)`.
  A linear map on a tensor product is determined by pure tensors, so this
  existentially characterized equivalence is exactly the canonical map.
- Compatibility with the `C`-action through `α` is the last equation:
  `γ (r ⊗ₜ[R₀] (c₀ • x)) = α (1 ⊗ₜ[R₀] c₀) • γ (r ⊗ₜ[R₀] x)`.
  This gives compatibility with `1 ⊗ c₀`; `γ` being `R`-linear gives compatibility
  with `r ⊗ 1` because `α` is an `R`-algebra isomorphism. Every algebra tensor is a
  sum of products of these elements, and every module tensor is a sum of pure
  tensors. Thus the displayed generator equation is exactly compatibility with
  the full transported algebra action, without introducing a second action definition.
- No flatness assumption occurs anywhere.

Universes `u v w` are explicit and independent for the three input types.
`C₀` and `M₀` may be taken in `Type u`: finite polynomial quotients over the subring
`R₀ : Type u` and cokernels of finite free modules over those quotients are in this
universe. No input ring or module is required to have the size of another input.
`set_option autoImplicit false` prevents unbound implicit parameters.

Dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-pbc-finitely-presented-algebra | Mathlib.RingTheory.FinitePresentation | Algebra.FinitePresentation |
| def-sc-finitely-presented-module | Mathlib.Algebra.Module.FinitePresentation | Module.FinitePresentation |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-essentially-finite-type-algebra | Mathlib.RingTheory.EssentialFiniteness | Algebra.EssFiniteType |
| def-weil-pbc-module-tensor-product | Mathlib.LinearAlgebra.TensorProduct.Defs, publicly available through Mathlib.RingTheory.TensorProduct.Basic | TensorProduct, TensorProduct.mk |

The last two dependencies have `mathlib_match` records and need no new Lean record.
All three non-statement proof ingredients have their Mathlib modules imported privately:
`Mathlib.RingTheory.Extension.Presentation.Core` for the coefficient-model equivalence,
`Mathlib.RingTheory.Localization.Submodule` for localization preserving Noetherianity,
and `Mathlib.LinearAlgebra.TensorProduct.RightExactness` for tensor right exactness.
The theorem docstring carries all seven steps of the accepted proof, including
localization injectivity, the matrix cokernel, and both tensor-associativity formulas.

Edge cases checked mathematically before writing:

- `M = 0`, including an empty matrix presentation: take the zero module model.
- `C = 0`: the zero algebra is allowed by `CommRing C`; no nontriviality of `C` or
  of `C₀` was added. Its modules and tensor conclusions are zero.
- Empty variable or relation sets: the presentation and coefficient argument permit
  them; no positive dimension, rank, number of generators or relations is required.
- `R` a field, including positive characteristic: intersect the coefficient ring with
  its zero maximal ideal and localize. Essential finite type over `ℤ` allows both
  characteristic zero and positive characteristic.
- Zero divisors in `R` and nonflat examples such as `C = R/(a)`: denominators outside
  the maximal ideal are units; the localized subring still embeds. Module descent
  uses right exactness, so these examples are retained.
- The zero ring is excluded precisely by the ordinary local-ring hypothesis, which
  requires a proper unique maximal ideal; no further nontriviality assumption is added.

Searches performed (all on 2026-10-24):

- `msearch.py leanfinder`, query “A finitely presented algebra and finitely presented
  module over a local ring descend to a Noetherian local subring essentially of finite
  type over the integers”: 8 hits, including
  `Algebra.FinitePresentation.of_finiteType` and
  `Algebra.EssFiniteType.isNoetherianRing`. None supplies the simultaneous models.
- `msearch.py loogle`, query `Algebra.FinitePresentation, Module.FinitePresentation,
  IsLocalRing`: 0 hits.
- `msearch.py leansearch`, query “A finitely presented algebra and module descend
  simultaneously to a Noetherian local subring essentially of finite type over the
  integers”: 8 hits on finite-presentation definitions and finite generation over
  Noetherian rings, not the simultaneous local-subring descent theorem.
- `msearch.py grep` in Mathlib `RingTheory`, query
  `tensorModelOfHasCoeffsEquiv|[Nn]oetherian.*[Mm]odel|[Ll]ocal.*[Ss]ubring`:
  25 hits, including smooth-algebra descent, local-subring definitions, and the
  coefficient-presentation equivalence already cited in the node's proof dependencies.
  The coefficient equivalence does not itself state the simultaneous module result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  Noetherian/model/local-subring terminology found no declaration of this item.
  The upstream `Module.exists_noetherian_localModelTower` was read: it concerns
  a tower of local rings with localization comparisons, not this subring model
  with exact algebra and module tensor isomorphisms.
- `rg` in Mathlib, `dag/lean_names_upstream.json`, `lean/WeilConjectures` and
  `lean/Sheaf` for the proposed declaration and module names found no collision.

Validation: `scompile.py NV lem-sfb-local-algebra-module-noetherian-subring-model`
compiled the delivered module in both sandbox and library contexts (1.4 s and 1.5 s),
with no errors or warnings. Nothing is proved beyond the required `sorry` statement.
No STATEMENT-DISPUTED flag or unresolved node fault remains.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
