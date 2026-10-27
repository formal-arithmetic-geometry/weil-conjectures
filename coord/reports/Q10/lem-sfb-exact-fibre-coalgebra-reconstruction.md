## Worker report

The delivery states `CategoryTheory.FibreReconstruction.exact_fibre_coalgebra_reconstruction`
in `Sheaf.CategoryTheory.ExactFibreCoalgebraReconstruction`. Its sole theorem has proof
`sorry`. The two additional modules contain actual definitions only. The item statement,
proof, and original dependencies are unchanged; its statement dependencies gain the two
new definition nodes described below.

Source read: Milne, Algebraic Groups (2017), printed pp.174–181, especially 9.32,
9.33–9.37 and 9.41–9.43, from the local PDF (PDF pages 186–193). The current blueprint
`latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), was also read.
The item is the explicit coefficient-quotient version of Milne 9.37, rather than
neutral tensor reconstruction. No statement correction is needed.

Hypothesis and clause matching:

| Node text | Lean rendering |
| --- | --- |
| Field k | `{k : Type u} [Field k]` |
| k-linear abelian A, bilinear composition | `[Category.{t} A] [Abelian A] [Linear k A]` |
| Essentially small; choose a small skeleton | `(S : Type (max u w)) [SmallCategory S] (hS : Skeletal S) (e : S ≌ A)` is the chosen small skeletal equivalence, an explicit witness of essential smallness. This is chosen data, not an extra mathematical hypothesis. |
| F to finite-dimensional vector spaces | `F : A ⥤ ModuleCat.{max u w} k` and `hfd : ∀ V, FiniteDimensional k (F.obj V)` |
| Faithful, exact, k-linear | `[F.Faithful]`, `[PreservesFiniteLimits F] [PreservesFiniteColimits F]`, `[F.Additive] [F.Linear k]`. In abelian categories this expresses exactness and linearity. |
| Direct sum of dual tensor fibres | `CoefficientSum (e.functor ⋙ F)` is exactly `⨁ V, Module.Dual k (F.obj (e.functor.obj V)) ⊗[k] F.obj (e.functor.obj V)` |
| N is the span of the displayed differences | `coefficientRelations` uses `Submodule.span` of exactly those differences; it adds no other generators. |
| B is that quotient; brackets | `CoefficientQuotient (e.functor ⋙ F)` is the actual submodule quotient, and `coefficient` is its quotient map after the summand inclusion. |
| Nonskeletal representatives | `coefficientAt F e V` uses `e.inverse.obj V` and `F.map` of the counit representative isomorphism and its inverse. |
| Counital coassociative structure on B | `∃ d : Coalgebra k (CoefficientQuotient (e.functor ⋙ F)), ...` uses Mathlib's full coalgebra structure and all three axioms. |
| Delta coefficient formula | First conjunct, quantified over each skeletal V, phi, v, n and `b : Module.Basis (Fin n) ...`; the two tensor factors occur in the prescribed order. |
| Epsilon coefficient formula | Second conjunct, `d.counit (coefficient ... V φ v) = φ v`. |
| Independence of finite basis | Delta and rho are each required to satisfy the formula for **every** finite basis of every cardinality n; the same d and E work for all bases. Any finite index basis can be reindexed by Fin n. |
| rho formula and equivalence | `∃ E : A ≌ Coalgebra.FiniteRightComodule d`, followed by the formula for its actual coaction after the specified transport to F(V). |
| Underlying object and arrow are F; composite equals F | `h : E.functor ⋙ Coalgebra.finiteRightComoduleForget d = F` is literal functor equality, so it also fixes every underlying arrow to F(f). `eqToHom` from the object component of h only expresses the necessary equality transport in the coaction formula. |
| Right comodules and morphisms | `finiteRightComoduleProperty` imposes finite dimension, `(assoc) (rho tensor 1) rho = (1 tensor Delta) rho` and `(rid) (1 tensor epsilon) rho = id`. The full subcategory of `Endofunctor.Coalgebra` inherits exactly colinear linear maps. |
| No tensor or dual-object assumptions on A or F | No monoidal, rigid, unit-object or tensor-compatibility binder appears. |
| Set-indexed sums in a containing universe | S and the fibre carriers live in `max u w`; B lives there too. The field, original category objects, and original category morphisms have independent universes u, v, t. The containing universe can always be enlarged. |

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`, implements the field definition.
- `CategoryTheory.Abelian`, `Mathlib.CategoryTheory.Abelian.Basic`, full signature and
  finite-products/kernels/cokernels and normal-mono/epi fields read at lines 105–120.
- `FiniteDimensional`, `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, is `Module.Finite`,
  hence the finite-spanning-set definition, not merely finite finrank.
- `TensorProduct`, `TensorProduct.mk`, and `LinearMap.rTensor`, from
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic` and `.Map`, give the exact universal
  tensor construction and tensor maps. DirectSum and quotient maps are Mathlib definitions.
- The new definition dependencies provide `CoefficientQuotient`, `coefficient`,
  `coefficientAt`, `Coalgebra.FiniteRightComodule`, and its forgetful functor.
- Stated proof dependencies are imported privately: `Module.Free.of_divisionRing`
  (`Mathlib.LinearAlgebra.Basis.VectorSpace`), `TensorProduct.dualDistribEquiv`
  (`Mathlib.LinearAlgebra.Contraction`), and `CategoryTheory.Limits.colimit`
  (`Mathlib.CategoryTheory.Limits.HasLimits`). The representability, generator-equivalence,
  finite-algebra dictionary and directed-descent proof nodes currently have no Lean records;
  they are not needed to type this statement, and are not restated. Their complete ten-step
  proof plan is included in the theorem docstring for stage 3.

Edge cases checked: zero category, zero fibres, empty basis (`n = 0`), zero coalgebra,
noncocommutative coefficient coalgebra, arbitrary field characteristic, and independent
original object/morphism universes. If B = 0, the comodule counit identity forces M = 0.
No nonempty/nonzero/basis-cardinality assumption excludes those cases. The relation for
an isomorphism exactly supplies the representative change used by coefficientAt. The
orientation of both tensor factors agrees with right comodules; no opposite coalgebra
or left-comodule convention is substituted.

Searches actually run through `msearch.py Q10 lem-sfb-exact-fibre-coalgebra-reconstruction`:
LeanFinder on exact faithful linear reconstruction (hits: CoalgCat and comonoid equivalence,
not reconstruction); Loogle `"Coalgebra", "Equivalence"` (comonadic/descent results, no match);
grep `coendomorphism|coend.*[Cc]oalgebra|[Cc]oalgebra.*coend|Comodule` (zero hits).
LeanSearch on coefficient quotient returned the general categorical coend and additive-group
colimit, neither this explicit module quotient nor its coalgebra reconstruction. LeanFinder
on the coefficient quotient returned Gabriel–Popescu and unrelated module presentations.
LeanFinder/LeanSearch on right comodules returned CoalgCat, comonoids and comonad coalgebras,
not the requested comodule category. A further combined LeanSearch/LeanFinder/grep set is
recorded verbatim in each new node's mathlib_searches. Repository rg over WeilConjectures
and Sheaf found only the Hopf-specialized coordinate-comodule subtype and unbundled coaction
lemmas; no general category or reconstruction theorem. The item-id grep in WeilConjectures
was empty. blueprint_refs searches for coalgebra and comodule returned zero blueprint nodes;
coefficient quotient returned five unrelated coefficient-tower nodes, read by their titles
and statements. DAG searches also found the same theorem's four proof inputs and its
neutral-tensor-envelope consumer, not a separate definition of these missing notions.

## New nodes

`def-sfb-fibre-coefficient-quotient` defines exactly the direct sum, naturality-relation span,
quotient and coefficient maps required by the item's displayed B. Its own module is
`Sheaf.CategoryTheory.FibreCoefficientQuotient`; no data is postponed. It also defines the
representative transport needed on nonskeletal objects. Source is the explicit coefficient
presentation of the item, identified with Milne 9.37 by its accepted proof. General Mathlib
coends exist, but do not define this concrete direct-sum/submodule quotient. Search evidence
is recorded above and verbatim in the new node; no duplicate DAG definition was found.

`def-sfb-finite-right-comodule` defines the requested category using Mathlib's existing
endofunctor-coalgebra category and full-subcategory construction. Its module is
`Sheaf.RingTheory.FiniteRightComodule`. `rightTensorFunctor` uses actual tensor maps;
its two functor laws are supplied by existing Mathlib lemmas, with no theorem or sorry
added. The predicate spells out exactly finite dimension and the two coaction laws.
The forgetful functor is the composite of existing forgetful/inclusion functors. Source:
Milne §9(d), pp.174–175 and equation (24), p.84. Existing HopfAction coaction predicates
require a commutative Hopf algebra and are unusable for a general noncocommutative coalgebra.
Searches found no node or declaration giving this general category.

## Second reading by Q10

Independent second reading (maintainer cc reviewer, 2026-10-24), replacing the delivering
worker's self-audit. Node, Milne §9(d) Theorems 9.32/9.37 (pp.174–178), the three modules and
the dependency records were open.

Node clauses and their Lean rendering:

- k a field: `{k : Type u} [Field k]`. Correct.
- A essentially small k-linear abelian: `[Category.{t} A] [Abelian A] [Linear k A]`; essential
  smallness and "choose a small skeleton" are the explicit data `S`, `[SmallCategory S]`,
  `Skeletal S`, `e : S ≌ A`, universally quantified, so the conclusion holds for every choice.
  S lives in the containing universe `max u w` of the fibres; Hom sets of A inject into
  fibre Hom spaces by faithfulness, so this is the node's "fixed containing universe", not an
  extra restriction. Correct.
- F faithful, exact, k-linear, finite-dimensional: `[F.Faithful]`, `[PreservesFiniteLimits F]`,
  `[PreservesFiniteColimits F]`, `[F.Additive] [F.Linear k]`, `hfd` with Mathlib
  `FiniteDimensional` (= `Module.Finite`, finite spanning set). Correct, no stronger.
- B: `CoefficientQuotient (e.functor ⋙ F)` = `(⨁ V : S, Dual ⊗ F V) ⧸ span{j_W(ψ⊗F f v) −
  j_V(ψ∘F f ⊗ v)}` over all morphisms f of S; exactly the node's generators, ψ on the target.
- Brackets on nonskeletal objects: `coefficientAt` = c_{e⁻¹V}(φ∘F(a_V), F(a_V⁻¹)v) with
  a_V the counit; the chosen representative. Correct.
- Counital coassociative coalgebra: `∃ d : Coalgebra k B` (Mathlib class with coassoc and
  both counit laws). Δ formula for every V, φ, v and every finite basis `Fin n` (this is the
  basis-independence clause; n = 0 included); ε[φ⊗v] = φ(v). Factor order as in the node.
- Equivalence: `∃ E : A ≌ FiniteRightComodule d` with `h : E.functor ⋙ forget = F` (literal
  equality, fixing objects F(V) and arrows F(f)), and the coaction of E(V), transported along h,
  equal to Σ b_i ⊗ [b_i^* ⊗ x]_V for every finite basis. Correct orientation: I checked by hand
  that ρ(v)=Σ e_i⊗c(e_i^*,v) is coassociative for the stated Δ and counital for ε.
- Right comodules: `finiteRightComoduleProperty` = finite dimension, assoc ∘ (ρ⊗1) ∘ ρ =
  (1⊗Δ) ∘ ρ, rid ∘ (1⊗ε) ∘ ρ = id; morphisms are those of `Endofunctor.Coalgebra` of the real
  functor (−)⊗B, i.e. linear maps with (f⊗1)ρ = ρ f; full subcategory. Correct.
- No monoidal/dual/unit assumptions: none present.

Edge cases: zero object and zero fibres (empty basis, n = 0), B = 0 (counit forces M = 0),
arbitrary characteristic, noncocommutative B, independent universes u, v, t for k and A.

New nodes: def-sfb-fibre-coefficient-quotient and def-sfb-finite-right-comodule are genuine
definitions with real data (no sorry); their statements match the modules; no DAG node,
Mathlib or project declaration gives a general comodule category or this quotient (rg over
side-live lean/Sheaf and lean/WeilConjectures: only Hopf-specialized `CoordinateComodule`
and unbundled coaction lemmas in `FiniteComoduleCoefficientCoalgebra`/`FiniteSubcomodule`).
The item changes only in `lean` and in `stmt_deps` gaining the two new nodes (§1(A)).

Mismatches found: none in the Lean or records; this section replaces the self-audit.
