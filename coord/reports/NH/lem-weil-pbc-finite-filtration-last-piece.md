## Worker report

The module `Sheaf.CategoryTheory.FiniteFiltrationLastPiece` states
`CategoryTheory.DecreasingFiltration.finite_filtration_last_piece`, with `sorry` as
its only proof. No definition or new node is needed. Only the item's `lean` field
changes. The statement and accepted stage-1 proof are unchanged.

Hypothesis and clause matching:

- The abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`, with independent
  explicitly declared object and morphism universes. The object is `{V : C}`.
- The integer `n ≥ 0` is `(n : ℤ) (hn : 0 ≤ n)`; no natural-number replacement or
  bound on the index universe is imposed.
- The decreasing filtration is `(F : DecreasingFiltration V)`, using the exact
  recorded dependency declaration and its `F` and `F_succ_le` fields.
- `F⁰V = V` is `h₀ : F.F 0 = ⊤` in the subobject lattice.
- `Fⁿ⁺¹V = 0` is `h₁ : F.F (n + 1) = ⊥` in the same lattice.
- All earlier graded pieces vanish: `hgr : ∀ p : ℤ, 0 ≤ p → p < n → IsZero (F.gr p)`.
  Upstream `DecreasingFiltration.gr` is exactly the cokernel of the inclusion
  `Subobject.ofLE _ _ (F.F_succ_le p)`.
- Equality of every intermediate step with the whole subobject is the first
  conclusion `∀ p : ℤ, 0 ≤ p → p ≤ n → F.F p = ⊤`.
- The canonical inclusion is an isomorphism: the existential isomorphism
  `j : (F.F n : C) ≅ V` satisfies `j.hom = (F.F n).arrow`.
- The canonical last quotient is an isomorphism: the existential isomorphism
  `ρ : (F.F n : C) ≅ F.gr n` satisfies
  `ρ.hom = cokernel.π (Subobject.ofLE _ _ (F.F_succ_le n))`.
  Thus these are witnesses for the specified maps, not arbitrary identifications.
- All objects `A B` and isomorphisms `a : A ≅ B`, `c : F.gr n ≅ B` are universally
  quantified after the canonical witnesses, which do not depend on them.
- The unique map solving the node's equation is stated literally as
  `∃! f : A ⟶ (F.F n : C), f ≫ ρ.hom = a.hom ≫ c.inv`.
- Every solution of that equation is separately asserted to equal
  `a.hom ≫ c.inv ≫ ρ.inv`. Lean's composition order is opposite to the written
  functional order `ρ⁻¹ ∘ c⁻¹ ∘ a`.
- For every such solution, `∃ e : A ≅ V, e.hom = f ≫ j.hom` states precisely
  that the specified composite is an isomorphism. Its inverse is explicitly
  `e.inv = j.inv ≫ ρ.hom ≫ c.hom ≫ a.inv`, the node's formula in Lean order.
- The zero-object implication is `IsZero V → IsZero A`, under the same arbitrary
  comparison data, as in the node. It is not asserted without `a` and `c`.

Dependency declarations read and used:

- `def-sp-abelian`: Mathlib `CategoryTheory.Abelian`, from
  `Mathlib.CategoryTheory.Abelian.Basic`; its full class and docstring were read.
  It supplies preadditivity, kernels, cokernels, normal monos/epis and finite products.
- `def-sp-filtration`: `CategoryTheory.DecreasingFiltration` and
  `CategoryTheory.DecreasingFiltration.gr`, from the recorded
  `WeilConjectures.CategoryTheory.Abelian.Filtration`; their complete definitions
  and docstrings were read. The compatibility module
  `WeilConjectures.CategoryTheory.CanonicalFiltration` was also read; its aliases
  are unnecessary here. No dependency repair is required.
- Proof dependency `lem-weil-pbc-preadditive-epi-iff-cokernel-zero`: exact Mathlib leaf
  `CategoryTheory.Preadditive.epi_iff_isZero_cokernel'`, from
  `Mathlib.CategoryTheory.Preadditive.Basic`. Its signature for a cokernel cofork
  with an `IsColimit` witness was read, and the module is a plain proof import.

The theorem docstring reproduces all four accepted proof steps: epi plus mono
makes successive steps equal; bounded induction gives the full last subobject;
the quotient by zero is invertible; the unique comparison and both inverse
identities follow by cancellation, with zero-object transport at the end.
Sources read: `literature/stacks-project/homology.tex`, definition-filtered
(Tag 0121), and lemma-biregular-ss-converges (Tag 012W), especially proof of (4).

Edge cases checked before writing:

- `n = 0`: the earlier graded-piece condition is empty; `h₀` identifies the last
  step with `V` directly and `h₁` makes its quotient an isomorphism.
- `n = 1`: the sole earlier vanishing condition is `IsZero (F.gr 0)`, forcing
  `F.F 1 = F.F 0`; the final zero step still controls the quotient.
- `V` zero: all its subobjects are zero, and the comparison forces `A` zero.
- Negative indices are permitted for `F`; no additional boundedness, separatedness,
  exhaustive-filtration, or completeness hypothesis has been introduced.
- Removing `h₁` would invalidate invertibility of the last quotient; removing an
  earlier-piece hypothesis can invalidate the full-subobject conclusion. Thus the
  endpoint and vanishing assumptions have their intended separate roles.

Searches made:

- `msearch.py ... leanfinder`: query “A finite decreasing filtration in an abelian
  category with only the last graded piece nonzero has canonical inclusion and
  quotient isomorphisms”. Eight results: `IsModuleFiltration.mk_int`,
  `IsRingFiltration.mk_int`, Dold–Kan eventual-constancy results, graded-object
  single-component isomorphisms, and general module/ring filtration results.
  None states this result for abelian-category subobject filtrations or the
  specified comparison formulas.
- `msearch.py ... loogle`: `CategoryTheory.Subobject.ofLE, CategoryTheory.IsIso`.
  One result, `CategoryTheory.Limits.kernelSubobject_comp_mono_isIso`; it concerns
  kernels of composites, not this filtration-collapse statement.
- `msearch.py ... grep`: `gradedPiece|finite.*filtration|filtration.*[Ii]so`,
  Mathlib subdirectory `CategoryTheory`: zero hits.
- Direct `rg` searches of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `lastPiece`, `last_piece`,
  `finite_filtration_last_piece`, and filtration/collapse patterns found no
  declaration of the item. The only initial project hit was an unrelated
  explanatory sentence in `GrothendieckCocycleComparison.lean`.
- `grep -rn 'lem-weil-pbc-finite-filtration-last-piece' lean/WeilConjectures`:
  no upstream attachment. Further searches for graded-piece vanishing and
  isomorphisms in both CategoryTheory trees found no exact existing statement.

Validation: `scompile.py NH lem-weil-pbc-finite-filtration-last-piece` compiled
both its sandbox view and final library module successfully (0.8 seconds each),
with no errors or warnings. Every variable and universe is explicitly bound;
the longest Lean line is 89 characters. There are no statement disputes or node faults.

## Second reading by NH

Final consistency reread by the assigned worker (not an independent review;
the dispatch forbids subagents, and the maintainer supplies independent review).
I re-opened the node and the final Lean statement and checked the mapping above.
The two existential isomorphisms are explicitly fixed to the original inclusion
and cokernel projection, and the comparison isomorphism is fixed both on its
forward map and inverse. Uniqueness concerns the original equation alone,
not a stronger predicate containing the other conclusions. Integer bounds,
all three endpoint/vanishing conditions, the equality of subobjects, the exact
inverse order, and the zero case are present. No mismatch or correction was found.
