## Worker report

The module `Sheaf.CategoryTheory.CokernelCorepresentingBijection` states
`CategoryTheory.exists_cokernel_corepresenting_bijection`, with a single `sorry` proof.
No definitions or helper nodes are introduced. The node is unchanged except for `lean`.
The source was read at `literature/stacks-project/homology.tex`, lines 7387–7454:
Tag 0793, `lemma-partially-defined-adjoint`, especially the final three Hom identifications.
There is no repair note for this item. No statement fault or disputed claim was found.

Hypotheses, in the order of the node:

- The abelian categories are `{A : Type u₁} [Category.{v₁} A] [Abelian A]` and
  `{𝓑 : Type u₂} [Category.{v₂} 𝓑] [Abelian 𝓑]`. All four universes are independent.
- The arbitrary functor is `(R : A ⥤ 𝓑)`. No additivity or preservation assumption is imposed.
- The objects and presentation arrows are `{P₂ P₁ B : 𝓑}`, `(d : P₂ ⟶ P₁)` and
  `(q : P₁ ⟶ B)`. The assertion that q is a cokernel is exactly
  `(hdq : d ≫ q = 0)` and `(hq : IsColimit (CokernelCofork.ofπ q hdq))`.
  The zero composite is part of the cokernel assertion, not an extra restriction.
- The two objects of A are `(L₁ L₂ : A)`.
- The supplied bijections are the dependent families `θ₁` and `θ₂` of `Equiv`,
  respectively `(L₁ ⟶ X) ≃ (P₁ ⟶ R.obj X)` and
  `(L₂ ⟶ X) ≃ (P₂ ⟶ R.obj X)` for every `X : A`.
- Naturality for each family is `hθ₁` and `hθ₂`, quantifying over all `X X'`,
  `u : X ⟶ X'`, and morphisms `a` from the corresponding L, and asserting
  `θᵢ X' (a ≫ u) = θᵢ X a ≫ R.map u`.
- Both stated zero preservation hypotheses are retained, as `hθ₁_zero` and
  `hθ₂_zero`, each `∀ X : A, θᵢ X 0 = 0`.
- The compatible arrow is `(D : L₂ ⟶ L₁)` with
  `hD : ∀ (X : A) (a : L₁ ⟶ X), θ₂ X (D ≫ a) = d ≫ θ₁ X a`.
- An arbitrary cokernel of D is `{C : A}`, `(c : L₁ ⟶ C)`,
  `(hDc : D ≫ c = 0)`, and `(hc : IsColimit (CokernelCofork.ofπ c hDc))`.
  Thus neither cokernel is restricted to Mathlib's chosen object.

Conclusion clauses:

- `∃ ψ : ∀ X : A, (C ⟶ X) ≃ (B ⟶ R.obj X)` gives the family of bijections,
  including both inverse identities in the `Equiv` structure.
- The first conjunct, `∀ (X : A) (v : C ⟶ X), q ≫ ψ X v = θ₁ X (c ≫ v)`,
  is exactly the characterization of the forward map.
- The second conjunct quantifies over every other family `ψ'` and concludes
  `ψ' = ψ` from this characterization alone. It does not require the competitor
  to satisfy the inverse formula or naturality in advance.
- The third conjunct says for each `X` and `b : B ⟶ R.obj X` that
  `c ≫ (ψ X).symm b = (θ₁ X).symm (q ≫ b)`, and that every `v` satisfying
  this equality equals `(ψ X).symm b`. This includes existence and uniqueness
  of exactly the factorization describing the inverse in the node.
- The last conjunct is the naturality clause for every `X X'`, `u`, and `v`:
  `ψ X' (v ≫ u) = ψ X v ≫ R.map u`.

Lean's `f ≫ g` is the node's `g ∘ f`, consistently in all these formulas.
Every variable is explicitly bound; `set_option autoImplicit false` enforces this.

Dependency declarations used:

- Statement dependency `def-sp-abelian`: its `mathlib_match` is
  `CategoryTheory.Abelian` from `Mathlib.CategoryTheory.Abelian.Basic`.
  Read the full class and docstring, lines 101–120. This includes preadditivity,
  finite products, kernels, cokernels, and normal mono/epi conditions.
- Proof dependency `def-weil-pbc-category-colimit`: recorded module
  `Mathlib.CategoryTheory.Limits.HasLimits`, imported with plain `import`.
  Read `colimit` and `colimit.desc` through their `to_dual` source declarations,
  as well as the full `Cocone` and `IsColimit` structures and docstrings in
  `Limits.Cones` and `Limits.IsLimit`. The directly used universal-property
  declaration is `CategoryTheory.Limits.IsColimit`.
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels` supplies the standard
  `CategoryTheory.Limits.CokernelCofork` and `CokernelCofork.ofπ`; their full
  definitions/docstrings at lines 592–610 were read. No private cokernel notion
  is substituted. The module imports all stated statement and proof dependencies.

Edge cases checked before writing:

- When `d = 0`, compatibility and injectivity of θ₂ force `D = 0`.
  The cokernel projections are isomorphisms, and the result reduces to θ₁
  transported along these isomorphisms.
- When d and D are identities (with the corresponding identical objects and
  compatible θ), both cokernels are zero objects, and their outgoing Hom sets
  are singletons, as the claimed equivalence requires.
- Zero L/P objects and a constant-zero R create no missing nonzero or
  nonempty assumption; any supplied equivalences then enforce the needed
  singleton Hom sets. Nothing requires R to preserve zero morphisms.
- Arbitrarily chosen cokernel targets/projections are allowed by `IsColimit`.
- All target objects and arrows, including zero targets and zero `u` or `v`,
  remain quantified. No smallness relation is imposed on the two categories.

Searches actually run, using `msearch.py NN lem-trf-cokernel-corepresenting-bijection`:

- `leanfinder`: "Compatible natural Hom bijections for two objects induce a
  natural Hom bijection on their cokernels with specified factorization formula".
  Eight hits: `cokernel.map_desc`, `cokernel.mapIso`, `cokernel.mapIso_hom`,
  `cokernel.map`, `cokernel.mapIso_inv`, `cokernelIsoOfEq_hom_comp_desc`,
  `cokernel.congr_hom`, and `coker_map`. These compare cokernels within one
  category; none provides the specified cross-category θ families.
- `loogle`: "CategoryTheory.Functor.leftAdjointObjIsDefined_colimit,
  CategoryTheory.Limits.cokernel.mapIso" returned zero hits. A separate query
  "CategoryTheory.Functor.leftAdjointObjIsDefined_colimit" returned that one
  declaration. Read `Adjunction/PartialAdjoint.lean`, lines 149–193, including
  `corepresentableByCompCoyonedaObjOfIsColimit`. These use Mathlib's partial
  adjoint diagram and do not state the normalization for arbitrary supplied
  θ₁, θ₂, D and c. Thus they are not exact matches.
- `grep`, restricted to Mathlib `CategoryTheory`:
  `corepresent.*cokernel|cokernel.*corepresent|cokernel.*[Ee]quiv|[Ee]quiv.*cokernel`.
  Fifteen hits concerning cokernel comparison/isColimit transport, including
  Preadditive.LeftExact, ObjectProperty.Kernels, Limits.Preserves.Shapes.Kernels,
  and Abelian.SerreClass.Localization; none states this result.
- `leansearch`: "Compatible natural Hom bijections descend to a bijection
  between morphisms out of cokernels". Eight hits: the `cokernel.mapIso` family,
  `cokernelComparison_map_desc`, `cokernel.map_desc`, `cokernel.map`, `coker.π_app`,
  and `ComposableArrows.Exact.cokerIsoKer'_hom`; none matches the given θ data.
- Local `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `corepresent.*cokernel|cokernel.*corepresent|cokernelCorepresenting|cokernel_corepresenting`
  gave no hits; searching the item id in `lean/WeilConjectures` also gave no hits.
  The planned declaration/module names were additionally checked over both
  source roots and `dag/lean_names_upstream.json`: no hits.

Validation: `scompile.py NN lem-trf-cokernel-corepresenting-bijection` compiled
both the sandbox probe and the named library module successfully (0.8 seconds
for each), with no reported errors or unexpected warnings. Every theorem proof
remains `sorry`; its docstring contains all four source-based proof steps and
names the relevant DAG dependencies. No agents were started and no independent
second reading is claimed; the maintainer reviews this direct delivery.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
