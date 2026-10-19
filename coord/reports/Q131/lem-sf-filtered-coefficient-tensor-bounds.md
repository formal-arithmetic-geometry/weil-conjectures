## Worker report

Item: `lem-sf-filtered-coefficient-tensor-bounds`. Group Q131, stage 2,
2026-10-17. Module: `Sheaf.Paper.FilteredCoefficientTensorBounds`.

The module states `AlgebraicGeometry.Scheme.filteredCoefficientTensor_constructible_bounds`.
Its four helpers belong to the coefficient complex explicitly introduced by this node:
they name the existing tensor functor, its actual differential, the two differential
proof obligations, and the resulting complex. No independent notion or dependency
interface repair is needed. Only the item's `lean` field changes.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Any scheme Y and its small pro-etale site | `Y : Scheme.{u}`, `ProEt.topology Y`, and `Y.ProEt` throughout; objects retain universe u+1 and morphisms universe u. |
| Finite commutative ring B | `B : Type (u + 1)`, `[CommRing B]`, `[Finite B]`. This is the published site-coefficient universe convention. |
| Constant ring B_Y | `adicLisseConstantRing Y B`, definitionally `(constantSheaf (ProEt.topology Y) CommRingCat).obj (CommRingCat.of B)`. |
| A sheaf of commutative rings R and unital rho | `R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}` and `ρ : R ⟶ adicLisseConstantRing Y B`; CommRingCat morphisms preserve one. |
| Integer cochain complex P of R-modules | `P : CochainComplex (pbcModules Y R) ℤ`; `pbcModules` is the existing `ringedSiteModules`/Mathlib `SheafOfModules` abbreviation. |
| Every term flat, meaning exact tensor | `hP : ∀ q : ℤ, SheafOfModules.IsFlatOnSite ... (P.X q)`; the type annotation fixes the published module universe and makes elaboration deterministic. `IsFlatOnSite` is precisely exactness of `siteSheafTensorRight`. No K-flatness or boundedness assumption is substituted. |
| Finite B-module V | `V : Type (u + 1)`, `[AddCommGroup V]`, `[Module B V]`, `[Finite V]`. |
| Length t at least zero | `t : ℕ`, including zero. |
| Decreasing submodule filtration | `F : Fin (t + 1) → Submodule B V`, `hF : Antitone F`. |
| V_0=V, V_t=0 | `hF₀ : F 0 = ⊤` and `hFt : F (Fin.last t) = ⊥`. |
| W_j=V_j/V_(j+1), for j<t | `j : Fin t` and the actual quotient `(F j.castSucc) ⧸ (F j.succ).comap (F j.castSucc).subtype`. Antitonicity makes the comap exactly V_(j+1) viewed as a submodule of V_j. |
| U_Y the constant coefficient module, with restricted R-action | `(adicLisseConstantModules Y B).obj U`, the published constant module-presheaf sheafification. The balanced R-action is through rho in `SheafOfModules.changeOfRings ρ`. |
| C_U=P tensor_R U_Y as a B_Y-complex | `filteredCoefficientTensorComplex Y B R ρ P U`. Its terms are `(B_Y tensor_R P^i) tensor_B_Y U_Y`, using the existing scalar extension and `siteSheafTensorRight`. The canonical identification to the node's tensor sends `(b tensor p) tensor v` to `p tensor bv`, with inverse `p tensor v` to `(1 tensor p) tensor v`. These are balanced, commute with restrictions and differentials, and induce inverse maps on sheafification. This is the canonical tensor construction, not an arbitrary complex or comparison assumption. |
| Differential d_P tensor 1 | `filteredCoefficientTensorDifferential`, explicitly the tensor functor's image of `changeOfRingsHom ρ (P.X i) (P.d i j)`. The definition of the complex has real X and d data. |
| Integers r<=s | `r s : ℤ`, `hrs : r ≤ s`. |
| All layer cohomology constructible | First conjunct of `hW`, for every `j : Fin t` and `n : ℤ`, uses `IsConstructibleProEtaleCoefficientModuleSheaf Y B` on `(C_W).homology n`. |
| Layer cohomology vanishes outside [r,s] | Second conjunct of `hW` is `(n < r ∨ s < n) → IsZero ((C_W).homology n)`. Endpoints remain included. |
| For every 0<=j<=t the same constructibility and interval | First conclusion conjunct quantifies over `j : Fin (t + 1)` and every integer n, with the same predicate and `IsZero` implication on the complex of `ModuleCat.of B (F j)`. |
| In particular for V itself, independently of length | Second conclusion conjunct uses `ModuleCat.of B V` directly, with the unchanged r and s; there is no t in either output bound. |

The module uses complex cohomology (`HomologicalComplex.homology`), as the node
states it for representing complexes; no derived representative or localization
choice is added to the hypotheses.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`:
  `AlgebraicGeometry.ProEtale.ModuleDerivedCategory`. Its current source was read
  with `scompile.py --source`; it documents the same small site and coefficient
  sizes. The theorem itself concerns representing cochain complexes in the ringed
  module presentation, so no derived-category term is needed in its signature.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; the cochain/homology infrastructure is imported.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of sheaf tensoring.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`:
  `SheafOfModules.siteSheafTensorRight`; its imported `TensorProduct` module
  also supplies `SheafOfModules.changeOfRings` and `changeOfRingsHom`.
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleCoefficientModuleSheaf`,
  with positive finite stratification, constructible strata, and actual
  inverse-image module sheaves locally finite constant. No Noetherian-scheme
  or etale-origin hypothesis is introduced.
- Existing support definitions are `AlgebraicGeometry.Scheme.pbcModules`
  (`Sheaf.Paper.BoundedConstructibleTower`), `adicLisseConstantRing` and
  `adicLisseConstantModules` (`Sheaf.Paper.AdicLisseModule`), and
  `CategoryTheory.ringedSiteModules` (`Sheaf.CategoryTheory.RingedSiteModules`).
  Their full definitions were read; each is reused, not copied.

The nonpublic imports retain the recorded proof dependencies: exact constant
sheafification (`Mathlib.CategoryTheory.Sites.Sheafification`), restriction of
scalars (`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`), the general
module category (`Sheaf.CategoryTheory.RingedSiteModules`), long exact complex
cohomology (`Mathlib.Algebra.Homology.HomologySequence`), the distinguished
short-exact triangle (`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`),
constructible triangulated closure (`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`),
and derived cohomology (`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`).
The triangulated predicate currently has the smaller finite-ring presentation;
transport along the finite coefficient ring equivalence is available at proof
stage, with no change in the present statement. It is not used to type the statement.

Sources: read `literature/stacks-project/proetale.tex` at
`lemma-constructible-serre` (Tag 09B5) and the adjacent
`lemma-compare-constructible-derived` (09AL). Tag 09B5 assumes a Noetherian ring;
the node's finite commutative B has this property. The finite coefficient
filtration argument is the agent-written application recorded in the DAG,
not a claim that the tag literally states this tensor theorem.

Edge cases checked before finalization:

- t=0: `Fin t` is empty, so the layer hypothesis is vacuous. The one filtration
  term is simultaneously top and bottom, forcing V to be zero; the conclusion
  gives the zero coefficient complex. There is no positive-length binder.
- Repeated filtration terms give zero successive quotients and are allowed.
- V=0, P=0, and the zero finite ring are allowed; no nontriviality assumption occurs.
- Empty Y is allowed by the existing constructibility predicate's single empty
  stratum. No nonempty-scheme or Noetherian-scheme assumption appears.
- r=s gives one permitted cohomological degree, including both endpoints.
- P is unbounded in both directions; only the layer cohomology is bounded.
- Scalar extension rho is arbitrary and need not be flat, injective or surjective.
- All term and quotient module carriers are in the published u+1 coefficient
  universe. Site object and morphism universes are never equated.

Searches for an existing statement (recorded also by `msearch.py` in searches.jsonl):

- LeanSearch: `Finite filtration of coefficient modules gives constructible
  cohomology in one fixed interval after tensoring a termwise flat sheaf complex`.
  Eight hits: ordinary flat-module exactness, `IsModuleFiltration`, and stable
  ideal filtrations; none is this sheaf-cohomology statement.
- LeanFinder: `Tensor a termwise flat complex of sheaves with a finite filtered
  coefficient module preserves constructible cohomology and a common
  cohomological interval`. Eight hits on ordinary-module flat tensor and
  light condensed monoidal sheaves; no match.
- Loogle: `"ShortComplex", "ShortExact"`. Twelve generic short-complex hits;
  none states filtered coefficient constructibility or the fixed interval.
- Mathlib grep through msearch: `[Ff]iltrat.*[Tt]ensor|[Tt]ensor.*[Ff]iltrat|[Cc]onstructible.*[Ee]xtension`.
  Zero hits.
- Source and side-library rg: the same regex and `filteredCoefficientTensor`.
  Source hits concern constructible extension closure and filtered
  representations. Side hits include `FlatFilteredComplexComparison`,
  `ProEtaleResidueTorTest`, `FiniteTensorConstructibleCohomology`, and
  `AdicConstructibleFiniteReductions`; these concern different inputs or
  conclusions. The first three modules were opened for comparison. None
  defines this arbitrary filtered B-module complex theorem.
- `grep -rn 'lem-sf-filtered-coefficient-tensor-bounds'` in the upstream
  `WeilConjectures` source: no hits. `rg 'filteredCoefficientTensor'` in
  `dag/lean_names_upstream.json`: no hits. No delivered declaration name
  already occurs in Mathlib, upstream, or the side source.

No statement correction or disputed mathematical claim. No new nodes and no
dependency modules. The two postponed theorems are
`filteredCoefficientTensorComplex_laws` (the named shape and square-zero proof
obligations explicitly required to define the node's C_U) and
`filteredCoefficientTensor_constructible_bounds` (the node's theorem).
Both have complete source/proof docstrings and are listed in `lean.declarations`.
The definitions contain no postponed data or arbitrary choices.

Validation: `scompile.py Q131 lem-sf-filtered-coefficient-tensor-bounds
lean/Sheaf/Paper/FilteredCoefficientTensorBounds.lean` passed for the sandbox
and its final library module, with no errors or warnings. Elaboration issues
were repaired by explicit site/module universe arguments and a typed named
differential; no heartbeat or time limit was raised. No library build was run.

## Second reading by Q131

This is a sequential second reading by the same dispatched worker; the brief
explicitly prohibits starting another agent. The node and final file were
reopened together for this pass.

The scheme/site and finite B binders match, including the unequal site
universes; the CommRingCat rho is unital. P has integer cochain shape and every
term is flat in the recorded exact-functor sense. V is finite as a set, with
its actual B-module structure. `Fin (t+1)`, `Antitone`, top at zero and bottom
at the last index match all finite decreasing filtrations including t=0.
`j.castSucc`/`j.succ` are the adjacent terms, and the comap quotient is the
actual W_j, not arbitrary isomorphic layer data. The coefficient tensor has
real term/differential data and the balanced inverse formulas identify it
with exactly P tensor_R U_Y. Neither R nor rho is specialized. Every layer
hypothesis quantifies over all n and every j<t. Both output clauses use the
recorded intrinsic constructibility predicate and exactly the same inclusive
[r,s]; the first covers every j<=t and the second V itself. No bound depends
on t, and no boundedness of P or extra geometry of Y is imposed.

The pass found a missing source/blueprint citation on the new named
differential's docstring; it was added. The final compile passed again.
No mathematical mismatch or changed statement was found.
