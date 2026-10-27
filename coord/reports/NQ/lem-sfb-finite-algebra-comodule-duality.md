## Worker report

The delivery states `FiniteAlgebraComoduleDuality.finite_algebra_comodule_duality` in
`Sheaf.RingTheory.FiniteAlgebraComoduleDuality`. Its only postponed proof is this named theorem;
its docstring contains all nine proof steps of the node. The supporting definitions and the two
category structures are real constructions, in `Sheaf.RingTheory.FiniteAlgebraDualityData`, owned
by the new definition node described below. Nothing is selected from an unproved existence
statement, and no coalgebra or equivalence is defined by a `sorry`.

Source read: Milne, Algebraic Groups (2017), §9(d), printed pp.174–175 and 177–178,
Example 9.36, and 9.41–9.42, printed pp.179–180 (the local PDF, using pdftotext).
Example 9.36 explicitly has left algebra modules and right dual-coalgebra comodules;
the paragraph following Lemma 9.35 instead has right algebra modules and left comodules.
The delivery follows Example 9.36, as the node does. I also read the current latest blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), the item's ancestor route.

Hypothesis and conclusion mapping, clause by clause:

- The field is `{k : Type u} [Field k]`, the exact Mathlib leaf of `def-weil-field`.
- The associative unital, potentially noncommutative algebra is `{E : Type v} [Ring E]
  [Algebra k E]`. `Ring` supplies associative unital multiplication, and `Algebra` gives the
  central scalar structure and bilinear multiplication. There is no `CommRing E`,
  `Nontrivial E`, characteristic condition or additional hypothesis.
- Finite dimensionality is `[FiniteDimensional k E]`, the recorded Mathlib notion.
  `FiniteDimensional` abbreviates `Module.Finite`, i.e. a finite spanning set.
- The specified dual is always `Module.Dual k E`, definitionally `E →ₗ[k] k`.
  Every tensor is Mathlib's actual `TensorProduct k`, using `⊗[k]` and `⊗ₜ[k]`.
- `∃ c : Coalgebra k (Module.Dual k E)` asserts the coalgebra's existence, including
  coassociativity and both counit laws. `IsDualCoalgebra c` supplies exactly the displayed
  multiplication and unit pairings: `TensorProduct.dualDistrib k E E (c.comul d)
  (a ⊗ₜ[k] b) = d (a * b)` and `c.counit d = d 1`.
  The pairing map sends `f ⊗ g` evaluated at `a ⊗ b` to `f a * g b`.
- `(∀ c', IsDualCoalgebra c' → c' = c)` asserts uniqueness of that structure, rather
  than merely uniqueness of a convenient presentation of its maps.
- For every finite-dimensional vector space the family `e` gives the actual bijection
  `(E →ₐ[k] Module.End k M) ≃ RightCoaction c M`. Here `M : FGModuleCat.{w} k`
  is the existing bundled finite-dimensional vector-space notion. Every unbundled
  finite-dimensional space can be used via `FGModuleCat.of k M`, with the same carrier,
  additive group and scalar structure; no skeleton or basis is imposed on M.
  An algebra map to `End_k(M)` is precisely a unital associative k-bilinear left action:
  additivity/scalar compatibility in a are the algebra-map laws; linearity in m comes
  from the endomorphism; multiplication is composition, and one is the identity.
- `RightCoaction c M` is the subtype of linear maps `ρ : M →ₗ[k] M ⊗[k] E*`
  satisfying the two stated coaction equations. The first is
  `assoc ∘ₗ ρ.rTensor E* ∘ₗ ρ = c.comul.lTensor M ∘ₗ ρ`, and the second is
  `rid ∘ₗ c.counit.lTensor M ∘ₗ ρ = LinearMap.id`. Thus the parenthesization and
  unit identifications are canonical, and no cocommutativity is assumed.
- The first formula conjunct states `(e M).symm ρ a m = rid ((eval a).lTensor M (ρ m))`.
  This is exactly `a·m = (1_M ⊗ ev_a)ρ(m)`, including the right unitor.
- The second formula conjunct quantifies over every `I : Type t`, `[Fintype I]` and
  `b : Module.Basis I k E`, and states `(e M α).val m = ∑ i, α (b i) m ⊗ₜ b.coord i`.
  The coordinate functional `b.coord i` is precisely the i-th dual basis vector.
  Since e is fixed before b is quantified, this formula for every basis asserts basis
  independence. `Equiv` supplies both inverse identities, so the formula also applies
  to the recovered action of any coaction. The contraction formula uses no basis.
- The next conjunct quantifies over arbitrary finite-dimensional M,N, both actions and
  any `f : M →ₗ[k] N`. Its left side is `∀ a m, f (α a m) = β a (f m)`;
  its right side is `(e N β).val ∘ₗ f = f.rTensor E* ∘ₗ (e M α).val`.
  This is exactly E-linearity if and only if commuting with the corresponding coactions.
- The final conjunct supplies `Φ : LeftModule k E ≌ RightComodule c`. These are the
  actual categories just described, with their specified intertwining/colinear linear maps.
  `Φ.functor ⋙ forgetRight c = forgetLeft` and
  `Φ.inverse ⋙ forgetLeft = forgetRight c` impose identity on underlying spaces AND maps
  in both directions. The final two `HEq` clauses tie Φ's object action/coaction to the
  very same family e used in the formulas and morphism criterion. Heterogeneous equality
  only accommodates the carrier equality already required by the forgetful-functor
  equations; it does not insert an arbitrary isomorphism of vector spaces.
- The zero algebra and zero spaces are included: neither category nor the theorem has
  a nonzero hypothesis. Empty finite bases and empty sums are admitted.

The definitions of the new node match those clauses directly: `IsDualCoalgebra` is only
its displayed predicate; `RightCoaction` is only the two equations; `LeftModule` consists
of a genuine `FGModuleCat` space and an algebra action; `RightComodule` consists of a genuine
`FGModuleCat` space and a coaction. The two category instances use subtypes of linear maps,
with ordinary identity and composition. Their proof fields use reflexivity, substitution
and existing tensor-map functoriality; there are no extra postponed helper theorems.
`forgetLeft` and `forgetRight` retain the space and package exactly the original linear map
using `FGModuleCat.ofHom`.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs (abbreviation of `Module.Finite`).
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`, in Mathlib.LinearAlgebra.TensorProduct.Defs/Basic;
  `LinearMap.rTensor`, `LinearMap.lTensor`, `rTensor_comp_apply`, `rTensor_id_apply` in
  Mathlib.LinearAlgebra.TensorProduct.Map. I read their signatures and docstrings.
- The new node's eight declarations are publicly imported by the theorem module.
  The definition module publicly imports exactly the Mathlib interfaces its statements use:
  algebra homomorphisms, finite modules, coalgebras and the dual tensor pairing.
- Proof-only imports follow the recorded proof dependencies:
  `Module.Free.of_divisionRing`, Mathlib.LinearAlgebra.Basis.VectorSpace;
  `Module.Basis.tensorProduct` and `tensorProduct_apply`,
  Mathlib.LinearAlgebra.TensorProduct.Basis;
  `TensorProduct.dualDistribEquiv`, Mathlib.LinearAlgebra.Contraction, whose forward map
  is the pairing `TensorProduct.dualDistrib`; its pure-tensor formula is
  `TensorProduct.dualDistrib_apply`, Mathlib.LinearAlgebra.Dual.Lemmas.

Edge cases checked mathematically before writing: E=0 gives D=0 with zero structure maps.
For M≠0, no unital action of E=0 and no counital coaction of D=0 exist, so the structure
bijection is between empty types; for M=0 both sides have one structure. A nonzero algebra
also acts on the zero space. An empty basis yields the correct empty sum. Nothing requires
E to be commutative or split, or k to have a specified characteristic. Independent explicit
universes u,v,w,t cover the field, algebra, module carriers and finite basis index sets.

Searches made through msearch.py:

- LeanFinder: “Finite dimensional left modules over an associative algebra correspond to
  right comodules over its dual coalgebra”: eight hits, including FGModuleCat duals,
  `CoalgCat.comonEquivalence` and `Module.finite_dual_iff`; no whole dictionary.
- Loogle: `Coalgebra, Module`: twelve coalgebra/transport hits; no action/comodule dictionary.
- Mathlib grep: `Comodule|comodule|dualCoalgebra|coalgebraDual`, RingTheory: zero hits.
- LeanSearch: “Category of finite dimensional right comodules over a coalgebra with colinear
  linear maps”: eight coalgebra homomorphism/category and FDRep hits; no comodule category.
- LeanFinder: “Categories of finite dimensional algebra representations and counital
  coassociative right coactions with intertwining linear maps”: eight FDRep/representation
  hits; monoid representations lack additivity and scalar compatibility in a.
- Loogle: `Coalgebra.Comodule, AlgHom`: zero hits, unknown `Coalgebra.Comodule`.
- Mathlib grep: `Comodule|comodule|RightCoaction|IsDualCoalgebra|FiniteAlgebraComoduleDuality`,
  Algebra: zero hits.
- Project/upstream rg: no declaration carrying the item id; upstream comodule only occurs
  in prose in GeneralLinear/Representation.lean. Existing project coefficient/subcomodule
  results state coaction equations inline. `HopfAction.Coassociative` and `Counital` require
  a commutative Hopf algebra and `CoordinateComodule` is specialized to a group coordinate
  Hopf algebra, so neither provides the arbitrary dual-coalgebra notion here.
- DAG title/concept searches found only theorem nodes about comodules, not these definitions.
  blueprint_refs.py search “comodule” found zero nodes; “finite algebra” found only the
  unrelated finite-algebra spreading statement. Read `CoalgCat.comonEquivalence`: coalgebras
  versus comonoid objects, not module/comodule duality. Read `FDRep`: monoid representations,
  not algebra representations. Read `ModuleCat.Algebra`: it restricts scalars from an E-module
  and explicitly warns about retaining an independently given k-module structure; the fixed
  vector-space action interface here instead uses the existing `AlgHom` exactly.

No statement correction and no STATEMENT-DISPUTED issue. The item's text, proof and proof
dependencies are unchanged. Only its Lean record and the new definition dependency are added.
The inherited blueprint ancestor is null (confirmed by blueprint_refs.py); its existing long
via chain is preserved, with this item prepended for the new node, rather than inventing an
ancestor.

Validation: every module is checked separately, in dependency order, with scompile.py against
the live server build; the final dry run and delivery use deliver2.py. Initial compiler feedback
was a missing argument in `rTensor_id_apply` and unused identity binders; those were repaired.

## New nodes

`def-sfb-finite-algebra-duality-data` owns `Sheaf.RingTheory.FiniteAlgebraDualityData`.
It defines the dual-pairing predicate, right coactions, finite-dimensional left algebra modules
and right dual-coalgebra comodules, their actual morphisms/categories and forgetful functors.
Source: Milne §9(d), pp.174–175, and Example 9.36, p.178. The three existing field,
finite-dimensionality and tensor-product nodes are reused. All semantic, type/name, Mathlib,
project and DAG searches above are recorded in its mathlib_searches, including the raw msearch
JSON results. None provides this package, and its new id is absent. `FGModuleCat`, `AlgHom`,
`Module.End`, `Coalgebra` and tensor/dual maps themselves are reused, not redefined.

## Second reading by NQ

Independent second reading of delivery 0cc0bb7613ad by the maintainer's review service (cc reviewer),
replacing the worker's self-check (which itself said it was not an independent reading).
Node, Milne iAG2017 §9(d) / Example 9.36 (left E-modules ↔ right E^∨-comodules), the three
recorded stmt_dep leaves and the new node def-sfb-finite-algebra-duality-data were read against
both modules.

Clause list and Lean rendering:

1. k a field: `{k : Type u} [Field k]` (def-weil-field). Exact.
2. E finite-dimensional associative unital k-algebra, not commutative: `{E : Type v} [Ring E]
   [Algebra k E] [FiniteDimensional k E]`. No CommRing, Nontrivial or characteristic assumption. Exact.
3. D = Hom_k(E,k): `Module.Dual k E`; tensors are Mathlib `TensorProduct k` (def-weil-pbc-module-tensor-product). Exact.
4. Unique counital coassociative coalgebra with ⟨Δd,a⊗b⟩=d(ab), ε(d)=d(1): `∃ c : Coalgebra k D,
   IsDualCoalgebra c ∧ ∀ c', IsDualCoalgebra c' → c' = c`. Mathlib `Coalgebra` carries coassociativity
   and both counit laws; `IsDualCoalgebra` uses `TensorProduct.dualDistrib` with
   `dualDistrib_apply : (f ⊗ g)(a ⊗ b) = f a * g b` (Dual/Lemmas.lean:1099). Uniqueness is equality of
   the whole structure (Prop fields are irrelevant). Exact.
5. For every finite-dimensional M, unital associative bilinear left actions ↔ right coactions:
   `e : ∀ M : FGModuleCat.{w} k, (E →ₐ[k] Module.End k M) ≃ RightCoaction c M`. An algebra map into
   End_k(M) is exactly a k-bilinear unital associative action (the scalar compatibility λ(r·1)=r·id
   follows from bilinearity). `RightCoaction` = linear ρ with assoc∘(ρ⊗1)∘ρ = (1⊗Δ)∘ρ and
   rid∘(1⊗ε)∘ρ = id: the node's two equations with the canonical associator and unitor. M's universe w
   is free. Exact.
6. a·m = (1_M ⊗ ev_a)ρ(m): `(e M).symm ρ a m = rid ((Module.Dual.eval k E a).lTensor M (ρ.val m))`. Exact.
7. ρ(m) = Σ_j (a_j·m) ⊗ a_j^* for ANY finite basis, hence basis independence: quantified over every
   `I : Type t`, `[Fintype I]`, `b : Module.Basis I k E` after e is fixed; `b.coord i` is the dual basis.
   Exact (basis independence is the ∀ after ∃ e).
8. E-linear ⇔ colinear: `(∀ a m, f (α a m) = β a (f m)) ↔ (e N β).val ∘ₗ f = f.rTensor D ∘ₗ (e M α).val`,
   for all M, N, actions and linear f. Exact.
9. Equivalence identity on underlying spaces and maps: `Φ : LeftModule k E ≌ RightComodule c` with
   strict functor equations `Φ.functor ⋙ forgetRight c = forgetLeft`, `Φ.inverse ⋙ forgetLeft =
   forgetRight c`, and the HEq clauses tying object structures to the same e. Not weaker than the node
   (it pins Φ to the dictionary), and not stronger (the node says it is the identity on spaces and maps).
10. Zero algebra / zero spaces included: no nontriviality hypothesis anywhere.

New node def-sfb-finite-algebra-duality-data: real definitions (predicate, subtype of linear maps
satisfying both equations, structures with an FGModuleCat space and an AlgHom/coaction, categories whose
Hom are subtypes of linear maps with literal id/comp, forgetful functors via FGModuleCat.ofHom). No sorry,
no hollow data. Its text matches Milne §9(d)/Ex. 9.36 and asserts no coalgebra existence. Source and
blueprint docstrings present on every declaration. lean.statement of both records occurs verbatim in the
files.

Edge cases: E=0 ⇒ D=0, the zero coalgebra exists and satisfies IsDualCoalgebra; for M≠0 both structure
types are empty, for M=0 both singletons, so the Equiv is consistent. Empty basis gives empty sum = 0,
consistent with M=0 forced when E=0. Universes u, v, w, t independent.

Searches (reviewer's own): Mathlib grep `Comodule|comodule` – only comonad Coalgebra prose; no dual coalgebra
on `Module.Dual`. Side-live lean/Sheaf: `HopfAction.Coassociative/Counital` (HopfActionModuleData) require
`[CommRing C] [HopfAlgebra k C]`; `RelativeHopfModuleData.Coaction` is a Hopf-module coaction;
FiniteSubcomodule / FiniteComoduleCoefficientCoalgebra state unbundled equations; none gives a coaction
category for an arbitrary coalgebra, so the new node is not a duplicate. DAG: no comodule/coalgebra node.

Mismatches: none in the Lean or the records. The only change is this section (the original was a
self-check, H11).
