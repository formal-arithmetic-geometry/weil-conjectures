## Worker report

Item: `lem-trf-split-exterior-comparison-localization`, Q73, stage 2.
Source read: `literature/stacks-project/more-algebra.tex`, Tag 0FJB,
`lemma-det-ses`, lines 36283–36335, particularly the first construction and its
explicitly omitted verification. The node's nine proof steps supply that verification.
The statement is unchanged. The delivery consists of its node record and
`Sheaf.LinearAlgebra.SplitExteriorComparisonLocalization`.

The module states all clauses through ten named theorems, each with `sorry`, plus two
helper interfaces belonging to this node. `IsSplitExteriorComparison` is exactly the
arbitrary-lift formula. `SplitExteriorScalarComparison` packages the three exterior
localization equivalences and their tensor equivalence with normalizations on spanning
vectors. Neither helper contains postponed data. No new independent mathematical notion
or dependency repair is needed, and no other node is changed.

Hypotheses and clauses are rendered as follows. All names below are in `exteriorPower`.

| Node text | Lean rendering |
| --- | --- |
| Commutative ring R | `{R : Type u} [CommRing R]`; no `Nontrivial R` |
| Three R-modules | independent `U : Type v`, `V : Type w`, `W : Type z`, each with `AddCommGroup` and `Module R` |
| Linear i and p | `i : U →ₗ[R] V`, `p : V →ₗ[R] W` |
| i injective | `hi : Function.Injective i` in the existence theorems |
| p surjective | `hp : Function.Surjective p` |
| image i = kernel p | `hex : Function.Exact i p` (the Mathlib function exactness predicate, for linear maps equivalent to this submodule equality) |
| W projective, with no freeness yet | `[Module.Projective R W]` only in `splitExterior_exists_section`; the splitting statement has no basis or finiteness hypothesis |
| Existence of a section | first conjunct of `splitExterior_exists_section`: `∃ σ, p.comp σ = LinearMap.id` |
| Every section gives t(u,w)=i(u)+σ(w) | its second conjunct quantifies over every section, and gives a unique linear equivalence `t : (U × W) ≃ₗ[R] V` with precisely that formula; the product is the binary module direct sum |
| Inverse v maps to (u,pv), i(u)=v−σ(pv) | second property in that same unique-existence conclusion specifies both inverse coordinates |
| Section, t and inverse maps localize | `splitExterior_split_localization` uses `baseChange A` for i,p,σ and for `fst ∘ t.symm`; `tA.symm` equals the pair of these localized coordinates, and its final pure-tensor equality specifies localization of t |
| Split exactness at every multiplicative subset | that theorem quantifies over `T : Submonoid R`, any independent-universe `A` with `[IsLocalization T A]`, and concludes injectivity, surjectivity, `Function.Exact`, and the localized section identity |
| U and W free of finite lengths r,s₀ | `r s : ℕ`, `bU : Module.Basis (Fin r) R U`, `bW : Module.Basis (Fin s) R W` in `existsUnique_splitExteriorComparison`; a basis is the complete freeness hypothesis, so no extra free/projective assumptions are imposed |
| Exterior powers and tensor products | Mathlib `⋀[R]^n M` and `⊗[R]`, with `ιMulti R n` for pure wedges |
| Canonical direct-sum c, kernel block first | `splitExteriorComparison_section_composite` takes the isomorphism `c` with its full concatenation characterization `hc`; the existing `existsUnique_topDirectSum` gives exactly this c in the inverse orientation |
| θ=(exteriorPower t)∘c | conclusion of `splitExteriorComparison_section_composite`: `θ.toLinearMap = (map (r+s) t.toLinearMap).comp c.toLinearMap` |
| θ is an R-linear isomorphism | unique existential `θ : (...) ≃ₗ[R] (...)` in `existsUnique_splitExteriorComparison` |
| Formula for arbitrary kernel and quotient tuples | `IsSplitExteriorComparison` quantifies over all `x : Fin r → U` and `y : Fin s → W` |
| Formula for every lift tuple | the same predicate quantifies over all `l : Fin s → V`, assuming exactly `∀ k, p (l k)=y k`, and concludes the prescribed `ιMulti` concatenation equality |
| Independence of section | the same unique θ satisfies the formula for every lift tuple; `section_composite` applies to every σ and t and every normalized c |
| Independence of bases; replacement bases | the characterization contains no basis. For every replacement `bU,bW` the unique-existence theorem returns the same isomorphism, by its uniqueness clause. Its formula concerns arbitrary tuples, not just basis vectors |
| Exterior-power localization comparisons | `SplitExteriorScalarComparison.kernel`, `.middle`, `.quotient` are equivalences `A ⊗[R] ⋀^n M ≃ₗ[A] ⋀[A]^n (A ⊗[R] M)`; the corresponding `_wedge` fields fix their values on all scalar multiples of pure wedges |
| Tensor localization comparison | `.tensor` and `.tensor_pure`; the scalar goes into the first exterior factor |
| Canonical comparisons exist | `existsUnique_splitExteriorScalarComparison`: `∃ C, ∀ D, D=C`; this is unique existence of fully normalized data, with no arbitrary isomorphism assumption |
| A tensor θ equals the localized construction | `splitExteriorComparison_localization` produces `θA`, proves its full arbitrary-lift characterization for `i.baseChange A,p.baseChange A`, and gives the equality `C.middle ∘ θ_A(baseChange) = θA ∘ C.tensor` of A-linear maps (the first θ here is the original θ under scalar extension) |
| Compatibility with successive localizations | `splitExteriorComparison_successive_localization` covers R→A→B with T⊂R and S⊂A, their localization instances, and `IsScalarTower R A B`. Its first and second clauses give exterior and tensor cocycles under `cancelBaseChange`; its third gives equality for the twice extended θ and the directly extended θ after those comparisons |
| r=0 left unit followed by exteriorPower(p⁻¹) | `splitExteriorComparison_zero_left` supplies `e : V ≃ₗ[R] W` with `e.toLinearMap=p`, and the formula `θ(a⊗q)=a • map s e.symm q`, using `zeroEquiv` to identify the degree-zero source with R |
| s₀=0 right unit followed by exteriorPower i | `splitExteriorComparison_zero_right` gives that i is an isomorphism and `θ(q⊗a)=a • map r i q` |
| Both ranks zero: multiplication | `splitExteriorComparison_zero_zero`: `zeroEquiv R V (θ(a⊗b)) = a*b` |
| Characteristic two, zero ring, localization containing zero | no characteristic, nontriviality, domain, or nonzero-denominator hypothesis appears anywhere |

The two one-empty-block formulas are equalities after the canonical homogeneous
inclusion into `ExteriorAlgebra R V`, which is injective. This avoids an artificial
cast along `0+s=s` or `r+0=r` while retaining the whole equality. The double-empty-block
formula is directly in R using `zeroEquiv`.

Localization uses `A ⊗[R] M`, not a second definition of module localization.
`IsLocalization.tensorProduct_isLocalizedModule` and
`isLocalizedModule_iff_isBaseChange`, in
`Mathlib.RingTheory.Localization.BaseChange`, identify exactly this model with
`LocalizedModule T M` and its numerator map. `LocalizedModule.equivTensorProduct`
provides the explicit canonical equivalence when A is `Localization T`; its fraction
formula sends m/t to (1/t) tensor m. The module's inverse and section statements thus
state localization of the original maps, not a new arbitrary split sequence.

Dependency declarations read and used:

- `def-weil-pbc-projective-module`: `Module.Projective`,
  `Module.projective_lifting_property`, `LinearMap.exists_rightInverse_of_surjective`,
  in `Mathlib.Algebra.Module.Projective`.
- `def-weil-pbc-free-module`: `Module.Free`, and its basis interface `Module.Basis`,
  in `Mathlib.LinearAlgebra.FreeModule.Basic` and `Mathlib.LinearAlgebra.Basis.Defs`.
- `def-weil-pbc-exterior-algebra`: `ExteriorAlgebra`, `ExteriorAlgebra.ι`,
  `ExteriorAlgebra.ιMulti`, `exteriorPower`, plus `exteriorPower.ιMulti`, `map`,
  `zeroEquiv`, in `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` and
  `Mathlib.LinearAlgebra.ExteriorPower.Basic`.
- `def-weil-pbc-module-tensor-product` has a Mathlib match and requires no lean repair:
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`,
  `LinearMap.rTensor`, in the TensorProduct Defs/Basic/Map modules.
- `def-weil-pbc-module-localization`: `LocalizedModule`, `mk`, `mkLinearMap`,
  `IsLocalizedModule.map`, in `Mathlib.Algebra.Module.LocalizedModule.Basic`;
  its tensor model and maps use `Mathlib.RingTheory.Localization.BaseChange` and
  `Mathlib.LinearAlgebra.TensorProduct.Tower`.
- Proof imports: `WeilConjectures.LinearAlgebra.ExteriorTopDirectSum`
  (`exteriorPower.existsUnique_topDirectSum`, `topDirectSum_natural`),
  `WeilConjectures.LinearAlgebra.ExteriorPowerLocalization`
  (`exteriorPower.isLocalizedModule_of_wedge`),
  `Mathlib.LinearAlgebra.ExteriorPower.Basis`
  (`Module.Basis.exteriorPower`), and the tensor/basis and localization Mathlib
  modules supplying the recorded free-basis and tensor-localization matches.

Edge cases checked mathematically before writing and again on reading the file:

- r=0 and s=0: empty bases force the appropriate modules to vanish; the two inverse
  maps and the three separate unit formulas have exactly the orientations in the node.
- r=s=0: the empty wedge is 1 and the formula gives multiplication a*b.
- Characteristic two: vanishing uses alternation and the r+1 kernel-vector relation;
  there is no division by two or a characteristic restriction.
- R the zero ring: unital modules and all tensor/exterior modules are subsingletons;
  all displayed equivalences and normalizations still hold for every finite length.
- 0 in T, or in the second localization S: the localized modules vanish and both
  localization diagrams and comparison cocycles still hold.
- T={1}: the comparison is the ordinary unit identification; the section and inverse
  formulas reduce to their original versions.
- Different module/ring universes: u,v,w,z,a,b are independent; the iterated tensor
  comparison keeps both scalar rings and all module universes, without imposing equality.
- Successive localizations with new denominators in A: S is an arbitrary submonoid
  of A, rather than only the image of a submonoid of R.

Searches actually run with `msearch.py Q73 <item>`:

1. LeanFinder query: "In a split exact sequence of finite free modules the top exterior
   isomorphism is independent of the section and commutes with localization".
   Eight hits, including `lequivProdOfRightSplitExact`, `lequivProdOfLeftSplitExact`,
   `Function.Exact.splitInjectiveEquiv`, `Function.Exact.splitSurjectiveEquiv`, and
   degree-one ModuleCat exterior naturality. These supply splitting or basic functoriality,
   not this complete comparison statement.
2. Loogle query: `exteriorPower.map, LinearEquiv`.
   One hit, `exteriorPower.alternatingMapLinearEquiv_symm_map`; no combined statement.
3. Mathlib grep query: `baseChange|localiz|split`, restricted to
   `LinearAlgebra/ExteriorPower`. Zero hits reported by the search wrapper.
   Direct source inspection separately found `map`, `map_comp`, `zeroEquiv` and
   the tensor `baseChange` API, and these are reused.
4. LeanSearch query: "The top wedge map of a split exact sequence of finite free modules
   is independent of lifts and compatible with localization".
   Eight hits, including `IsLocalizedModule.lift_iso`, `LocalizedModule.lift'`,
   `LocalizedModule.map_exact`, `IsLocalizedModule.map_exact`, and basis splitting;
   none has the top-exterior comparison and its complete normalization/localization clauses.
5. Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf` and
   `dag/lean_names_upstream.json` for `SplitExteriorScalarComparison`,
   `IsSplitExteriorComparison`, `splitExterior_exists_section`, `splitExteriorComparison`
   found no duplicate declarations. A search for the item id in both source trees also
   found no statement. Related determinant modules were read: their maps use the
   determinant socle rather than the explicit finite-rank exterior powers here. In
   particular the parent `ProjectiveDeterminantExactSequence` imports this item in its
   DAG proof route and is not used to define the missing local wedge construction.
6. Source searches and full-signature readings covered the current upstream
   `ExteriorTopDirectSum` and `ExteriorPowerLocalization` declarations, the generic
   exterior-localization theorem, the Mathlib projective/free/exterior/tensor/localization
   definitions, and `cancelBaseChange` and `baseChange`. No existing single declaration
   states all clauses of this node.

No statement correction, dependency-module repair, or `STATEMENT-DISPUTED` issue.

## Second reading by Q73

Independent clause-by-clause reading by the maintainer's second reader (cc review service), replacing
the worker's own second pass (which was a self-audit, delivery-errors H11). The module and the node
record are unchanged.

Node clauses and their Lean rendering (verdict after each):

1. R commutative ring; i : U → V, p : V → W linear; i injective, p surjective, im i = ker p:
   `{R : Type u} [CommRing R]`, independent universes v w z, `hi`, `hp`, `hex : Function.Exact i p`. Correct; no Nontrivial.
2. W projective ⇒ ∃ section; every section s gives an iso t_s(u,w) = i u + s w with inverse v ↦ (u, pv), i u = v − s(pv):
   `splitExterior_exists_section` with `[Module.Projective R W]` (Mathlib, = def-weil-pbc-projective-module record).
   ∃! t is harmless (t is fixed by its formula). Both inverse coordinates given. Correct.
3. Section and inverse maps localize; localized sequence split exact for every multiplicative subset:
   `splitExterior_split_localization`, tensor model A ⊗[R] M with `[IsLocalization T A]` (canonically
   LocalizedModule by `isLocalizedModule_iff_isBaseChange`). Hypotheses do not include hi/hex, but they follow from
   t being an equivalence with t(x,y)=i x+σ y and (t.symm q).2 = p q (p∘i = 0 and ker p ⊆ im i), so the conclusion
   (injective, surjective, Exact, p_A σ_A = id, t_A with localized inverse coordinates, t_A(a⊗x,a⊗y)=a⊗t(x,y)) is true. Correct.
4. U, W free with finite bases of lengths r, s₀: `bU : Module.Basis (Fin r) R U`, `bW : Module.Basis (Fin s) R W`. Correct (r, s may be 0).
5. θ_s an R-linear iso satisfying the arbitrary-tuple, arbitrary-lift formula, independent of section and bases:
   `existsUnique_splitExteriorComparison` with `IsSplitExteriorComparison` (∀ x y l, p∘l = y → θ(ιx ⊗ ιy) = ι(Fin.append (i∘x) l)).
   The predicate contains no section and no basis; ∃! gives independence. Mathematically true: error terms contain
   r+1 vectors of i(U), image of ⋀^{r+1}U = 0. Pure tensors of pure wedges span, so uniqueness holds. Correct.
6. θ_s = (⋀^{r+s₀} t_s) ∘ c_{U,W}, c the concatenation comparison:
   `splitExteriorComparison_section_composite`, c given with its full characterization hc (exactly the inverse
   of `existsUnique_topDirectSum` of lem-sc-exterior-top-direct-sum, which pins e.symm by the same formula).
   Checked on generators: map t (c(ιx⊗ιy)) = ι(append(i x_j, σ y_k)) and σ y_k is a lift. Correct.
7. Exterior-power and tensor localization identifications: `SplitExteriorScalarComparison` (kernel/middle/quotient
   pinned on a₀ ⊗ ιMulti, tensor pinned on a₀ ⊗ (x ⊗ y)) and `existsUnique_splitExteriorScalarComparison` (∃ C, ∀ D, D = C).
   Data fields are canonical (all values fixed on generators), no hollow definition; no Mathlib exterior base-change
   equivalence exists (grep of LinearAlgebra/ExteriorPower and ExteriorAlgebra for baseChange: none). Correct.
8. A ⊗ θ_s equals the construction for i_A, p_A: `splitExteriorComparison_localization`, θA satisfies the
   arbitrary-lift predicate for `i.baseChange A`, `p.baseChange A`, and C.middle ∘ θ_A-base-change = θA ∘ C.tensor.
   Checked on a⊗(ιx⊗ιy): both sides give a • ι(append(1⊗i x_j, 1⊗l_k)). θA unique by item 5 over A (localized bases). Correct.
9. Compatibility with successive localizations: `splitExteriorComparison_successive_localization`, exterior and
   tensor cocycles through cancelBaseChange (b⊗(a⊗m) ↦ (a•b)⊗m) and the iterated θ square. Checked all three on
   generators; S is an arbitrary submonoid of A. Correct.
10. r = 0: left unit then ⋀^{s₀}(p⁻¹): `splitExteriorComparison_zero_left` (∃ e ≃ with e = p; equality in
    ExteriorAlgebra R V avoids the 0+s cast; the inclusion is injective). s₀ = 0: right unit then ⋀^r i:
    `_zero_right`. Both zero: multiplication via zeroEquiv: `_zero_zero`. Orientations match the node. Correct.
11. Characteristic 2, zero ring, 0 ∈ T: no Nontrivial, characteristic or nonzero-denominator hypothesis anywhere. Correct.

Edge cases: r = 0 / s = 0 (Fin 0 bases, ⋀^0 = R through zeroEquiv); zero ring (all modules subsingletons, statements
still true); 0 ∈ T (localized modules zero); T = {1}. Universes u v w z a b independent; nothing unbound
(autoImplicit off).

H4 search: rg of side-live lean/Sheaf and lean/WeilConjectures for SplitExterior/splitExterior: none. The parent
Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence works with the socle determinantModule, a different object;
no duplicate. Mathlib has no exterior-power base-change equivalence.

Records: lean.statement is verbatim the signature in the file; all 12 declarations in lean.declarations exist in the
module; docstrings carry the source place (Tag 0FJB; Algebra 00DK/00DL/0C6F) and the blueprint id, and the theorem
docstrings carry the node proof. Every proof is `sorry`. Proof imports (ExteriorTopDirectSum, ExteriorPowerLocalization)
are private and exist upstream.

Advisory: localization is rendered in the tensor model A ⊗[R] M rather than LocalizedModule (the record of
def-weil-pbc-module-localization); this is the canonical equivalent model and is stated in lean.note.

Verdict: the Lean says exactly what the node says. No change to the module or the node.
