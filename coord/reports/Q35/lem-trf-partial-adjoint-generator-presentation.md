## Worker report

The module `Sheaf.CategoryTheory.PartialAdjointGeneratorPresentation` states
`CategoryTheory.partialAdjointGeneratorPresentation`, with its sole proof `sorry`.
It states the full generator presentation and relation transport for the supplied
representing objects and natural bijections. No new notions or dependency repairs
are needed; the mathematical statement is unchanged.

Hypotheses, in the order of the node:

- The categories are `{A : Type u₁} {B : Type u₂}` with independent morphism
  universes `[Category.{v₁} A] [Category.{v₂} B]` and `[Abelian A] [Abelian B]`.
- The functor is `(R : A ⥤ B) [R.Additive]`.
- The class of objects is `(P : Set B)`; `p : P` is an object together with its
  membership proof. `hcover : ∀ Y : B, ∃ p : P, ∃ q : p.1 ⟶ Y, Epi q` is exactly
  the epimorphic covering hypothesis, without projectivity or smallness assumptions.
- `(L : P → A)` specifies the given representing objects. The equivalences
  `θ : ∀ (p : P) (X : A), (L p ⟶ X) ≃ (p.1 ⟶ R.obj X)` are the given bijections.
- `hθ` states precisely `θ p X' (a ≫ u) = θ p X a ≫ R.map u` for all objects,
  arrows, and members of `P`. No naturality in `p` or additivity of `θ` is assumed.

Conclusion, clause by clause:

- Each `i_P` is expanded as `θ p (L p) (𝟙 (L p))`. The first conjunct is
  `θ p X a = θ p (L p) (𝟙 (L p)) ≫ R.map a ∧ θ p X 0 = 0` for every `p,X,a`.
- For every `Y : B`, the statement quantifies `p₁ p₂ : P`,
  `q : p₁.1 ⟶ Y`, `K : B`, `k : K ⟶ p₁.1`, and `r : p₂.1 ⟶ K`.
  `Epi q ∧ Epi r` gives both specified epimorphisms.
- The witness `hk : k ≫ q = 0` and
  `Nonempty (IsLimit (KernelFork.ofι k hk))` say exactly that `k` is a kernel of
  `q`. `Nonempty` here wraps the actual universal-property structure in Prop;
  it is not used to choose any data or define an object.
- The specified `d = k ∘ r` is expanded everywhere as `r ≫ k`.
  `(r ≫ k) ≫ q = 0` is its zero composite with `q`.
- The cokernel universal property is stated explicitly:
  for every `Z : B` and `h : p₁.1 ⟶ Z` with `(r ≫ k) ≫ h = 0`,
  `∃! b : Y ⟶ Z, q ≫ b = h`.
- A witness `D : L p₂ ⟶ L p₁` has equation
  `θ p₂ (L p₁) D = (r ≫ k) ≫ θ p₁ (L p₁) (𝟙 (L p₁))`.
  The next conjunct quantifies every `D'` satisfying that same equation and
  asserts `D' = D`, so uniqueness concerns the defining equation itself.
- For this witness, every `X : A` and `a : L p₁ ⟶ X` satisfy
  `θ p₂ X (D ≫ a) = (r ≫ k) ≫ θ p₁ X a`, and
  `D ≫ a = 0 ↔ (r ≫ k) ≫ θ p₁ X a = 0`.

The composition notation `f ≫ g` means the source's `g ∘ f`; the report above
checks the orientation of every equation. All universes and variables are bound
explicitly. The module has no local notation, helper definition, or choice of
different representing objects.

Dependencies read and used:

- `def-sp-abelian` is a Mathlib leaf naming `CategoryTheory.Abelian`, in
  `Mathlib.CategoryTheory.Abelian.Basic`; its class signature and docstring were
  read at lines 103–115. The class already extends `Preadditive`.
- `def-weil-pbc-additive-functor` is a Mathlib leaf naming
  `CategoryTheory.Functor.Additive`, in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`; its signature and
  docstring were read at lines 43–48, together with the induced additive Hom map
  and zero-preservation instance. Both imports are public statement dependencies;
  they also exhaust the proof dependencies.

Source read: `literature/stacks-project/homology.tex`, lines 7387–7466,
`lemma-partially-defined-adjoint` (Tag 0793). Its first paragraph supplies the
identity-evaluation formula and induced morphism; its second supplies the exact
presentation. The node's additive specialization supplies the zero formulas.
The declaration docstring includes each of the node's five proof steps, including
the two covers, kernel cancellation, normal-epi argument, inverse bijection,
naturality, and injectivity argument.

Edge cases checked before writing:

- `P = ∅` cannot satisfy the cover hypothesis in an abelian category, since its
  zero object still needs a cover. No nonemptiness assumption is added.
- The zero category, the zero target object, zero morphisms, and an isomorphism
  `q` (whose kernel is zero) are covered. The second cover is still allowed to
  cover zero. For `a = 0` the transported equation and equivalence reduce to the
  explicitly included zero compatibility.
- No projectivity, exactness of `R`, chosen adjunction, pre-existing naturality
  in the generators, or smallness of either category is imposed. Separate object
  and Hom universes are retained in both categories; `Equiv` permits distinct
  universes for the two Hom types.
- Kernel and cokernel properties use arbitrary objects and maps, not just a
  chosen test object. Uniqueness of `D` is not restricted to arrows already
  satisfying the transported relations.

Searches actually run through `msearch.py` (logged in `searches.jsonl`):

- LeanFinder: “In abelian categories an epimorphically generating class with
  natural Hom bijections for an additive functor yields cokernel presentations
  and unique transported relations”. Eight hits, including
  `Abelian.epiIsCokernelOfKernel` and `Abelian.epiDesc`; none states the combined
  result with arbitrary supplied `L` and `θ`.
- Loogle: `CategoryTheory.Functor.partialLeftAdjointHomEquiv_map_comp,
  CategoryTheory.Abelian.epiIsCokernelOfKernel`: zero hits.
- Loogle: `CategoryTheory.coyonedaEquiv`: eight hits giving the Yoneda
  equivalence and its compatibility formulas, not this generator presentation.
- Mathlib grep: `generator.*presentation|partial.*[Aa]djoint|epiIsCokernelOfKernel`
  under `CategoryTheory`: fifteen hits, especially `Adjunction/PartialAdjoint`
  and `Abelian/Basic`. Read `PartialAdjoint.lean` lines 49–124 and the normal-epi
  theorem at `Abelian/Basic.lean` lines 472–477. The partial-adjoint API chooses
  its own representers; it does not give this statement for the supplied ones.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `generator.*presentation|partialAdjoint|partialLeftAdjoint|partial_adjoint|partial_adjoint_generator`
  found unrelated generator presentations but no matching partial-adjoint result.
  The required node-id grep in `lean/WeilConjectures` found no occurrences.
- Name-clash search for `partialAdjointGeneratorPresentation` and
  `partial_adjoint_generator_presentation` in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` returned no hits.

No statement dispute or source fault was found. Initial compilation rejected the
calligraphic binder `𝒫` as a token; it was renamed to `P` without changing meaning.

## Second reading by Q35

Independent second reading by the maintainer's reviewer (the delivered section was a
same-worker self-check, H11; replaced here). Read: the item node, both stmt_deps
(def-sp-abelian = Mathlib `CategoryTheory.Abelian`, def-weil-pbc-additive-functor =
Mathlib `CategoryTheory.Functor.Additive`), Stacks homology.tex Tag 0793
(lemma-partially-defined-adjoint, first and second paragraph), the delivered module and the
parent's landed `Functor.isRightAdjoint_of_epi_generating_class`.

Node statement as a list, with its Lean rendering:

1. Abelian `𝒜, ℬ`: `{A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]`; four independent universes. Exact.
2. Additive `R`: `(R : A ⥤ B) [R.Additive]`. Exact.
3. `𝒫 ⊂ Ob ℬ` with an epimorphism from 𝒫 onto every object: `(P : Set B)`, `hcover : ∀ Y, ∃ p : P, ∃ q : p.1 ⟶ Y, Epi q`. Exact; no projectivity or smallness; same encoding as the parent.
4. `L_P` and bijections `θ_{P,X}` natural in X, `θ(u∘a)=R(u)∘θ(a)`: `L : P → A`, `θ p X : (L p ⟶ X) ≃ (p.1 ⟶ R.obj X)`, `hθ : θ p X' (a ≫ u) = θ p X a ≫ R.map u`. Exact (diagrammatic order checked).
5. `i_P = θ(id)`: inlined as `θ p (L p) (𝟙 (L p))`.
6. `θ(a)=R(a)∘i_P` and `θ(0)=0` for all P, X, a: first conjunct, `θ p X a = i ≫ R.map a ∧ θ p X 0 = 0`. Exact.
7. For every B: `P₁,P₂ ∈ 𝒫`, epis `q : P₁ ↠ B`, `r : P₂ ↠ K`, kernel `k : K → P₁` of q: `∃ p₁ p₂ q K k r (hk : k ≫ q = 0), Epi q ∧ Epi r ∧ Nonempty (IsLimit (KernelFork.ofι k hk))`. Exact (Prop-level universal property, not a choice of data).
8. `d = k∘r` with q a cokernel of d: `q∘d = 0`: `(r ≫ k) ≫ q = 0`; every `h : P₁ → Y` with `h∘d = 0` factors uniquely: `∀ Z h, (r ≫ k) ≫ h = 0 → ∃! b, q ≫ b = h`, Z arbitrary in B. Exact.
9. Unique `D : L_{P₂} → L_{P₁}` with `θ(D) = i_{P₁}∘d`: `∃ D, θ p₂ (L p₁) D = (r ≫ k) ≫ i_{p₁} ∧ ∀ D', (same equation) → D' = D`. Exact; uniqueness among all arrows.
10. `θ_{P₂,X}(a∘D) = θ_{P₁,X}(a)∘d` and `a∘D = 0 ↔ θ(a)∘d = 0` for all X, a: `θ p₂ X (D ≫ a) = (r ≫ k) ≫ θ p₁ X a ∧ (D ≫ a = 0 ↔ (r ≫ k) ≫ θ p₁ X a = 0)`. Exact. Precedence checked (`≫` 80, `=` 50, `∧` 35, `↔`, `→`).

Edge cases: B = 0 (q from any P₁, K = P₁ possible), q iso (K = 0, r : P₂ → 0), P = all objects, R = 0 (L_P ≅ 0), zero categories: all within the statement; no nonemptiness, projectivity, exactness or smallness added. Universes all bound; Equiv between Hom types of different universes allowed.

Mathematics: steps 1–5 of the node prove each clause (step 3 uses the normal-epi axiom of `Abelian`). The statement is consistent with the parent `isRightAdjoint_of_epi_generating_class` (same `P`, `hcover`, `θ`, naturality encoding).

Gates: module docstring and declaration docstring carry the source place and `(blueprint: lem-trf-partial-adjoint-generator-presentation)`; the declaration docstring carries the five proof steps; only proof is `sorry`; no definitions, so nothing hollow; node `lean.statement` verbatim equal to the file signature; only `lean` changed in the node; imports are the two stmt_dep Mathlib modules. No duplicate: Mathlib `partialLeftAdjoint*` uses library-chosen representers, `ProjectivePresentation` needs projectivity.

No mathematical change. Only this report section was replaced.
