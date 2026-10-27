## Worker report

The module `Sheaf.CategoryTheory.Sites.SheafifiedArrowsCoverRefinement` states
`CategoryTheory.sheafified_arrows_cover_refinement`, with its sole proof `sorry`.
The DAG statement is unchanged. No definitions, new nodes, dependency modules or
additional hypotheses are introduced. The source read is Stacks `sites.tex`,
Tag 0D06 (`lemma-quasi-compact`), especially lines 3345–3361, together with
Tag 00WK (`lemma-sections-sheafification`, lines 2155–2177). The theorem docstring
records all four steps of the DAG proof, including the final local-equality
refinement needed without subcanonicity.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The category of the small site is `{C : Type u} [Category.{v} C]`. Its coverings
  are `(J : Precoverage C)` with `(_hJ : J.IsSiteForCoverings)`, exactly the
  recorded site component of `def-weil-pbc-sites-and-cohomology`. This uses
  covering-presieve bind composition and existence of covering pullbacks, rather
  than assuming all pullbacks or the stronger Mathlib composition instance.
- The universe containing objects, morphisms and indexing sets is `max u v w`.
  Objects, morphisms, the input indices `{I : Type w}`, all sheaf values and the
  output indices `B : Type (max u v w)` fit in it. Independent object/morphism
  universes are retained. This implements `def-weil-size-convention` directly;
  its recorded interface is metatheoretic and has no module to import.
- For every T, the representable Hom(-,T) is Mathlib's `uliftYoneda.{max u w}.obj T`.
  This is the ordinary representable, with its Hom sets transported by ULift into
  the common set universe, not a second definition of representability.
- H_T is `(presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
  (uliftYoneda.{max u w}.obj T)`. The unit eta_T is the dependency's `toSheafify`
  on this presheaf; it is mentioned in the proof description but need not appear
  as a separate binder because neither the hypothesis nor the conclusion uses it.
- `(U : C)`, `(U_i : I → C)` and `(a : ∀ i : I, U_i i ⟶ U)` introduce precisely
  the object and arbitrary arrow family. There is no covering assumption on a.
- The induced arrow H(a_i) is the sheafification functor's `.map` applied to
  `uliftYoneda.{max u w}.map (a i)`. `Sigma.desc (fun i ↦ ...)` is the canonical
  map from their coproduct **in sheaves**, not the pointwise presheaf coproduct.
  Read `Sigma.desc` at Products.lean:278: it is `colimit.desc` for `Cofan.mk`,
  hence uses exactly `def-weil-pbc-category-colimit`'s recorded construction.
- `(hepi : Epi (Sigma.desc ...))` is the stated cancellation condition against
  every sheaf G and maps f,g from H_U. Mathlib's `Epi.left_cancellation`
  (Category/Basic.lean:321–323) says exactly p ≫ f = p ≫ g implies f = g.
- The existential `(B : Type (max u v w)) (V : B → C)
  (b : ∀ k : B, V k ⟶ U)` introduces the requested covering family v_b.
  `Presieve.ofArrows V b ∈ J U` is its covering condition.
- `(α : B → I)` is the requested index function; `(g : ∀ k : B, V k ⟶ U_i (α k))`
  is precisely the family of factorization arrows to the labelled original members.
- `∀ k : B, g k ≫ a (α k) = b k` is a_{alpha(b)} composed with g_b = v_b in C.
  It asserts equality of actual site arrows, not equality of their images in H_U.
  No subcanonical hypothesis or identification of a representable with a sheaf
  is present.

Dependency declarations and imports:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (full definition and docstring read).
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  `CategoryTheory.presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`
  (definitions and docstrings read). `LeftExact` supplies set sheafification in
  the common universe; no existence-of-sheafification binder is added.
- `Mathlib.CategoryTheory.Limits.HasLimits`:
  `CategoryTheory.Limits.colimit` and `colimit.desc`, via
  `Mathlib.CategoryTheory.Limits.Shapes.Products`'s `Sigma.desc`.
  `Mathlib.CategoryTheory.Sites.Limits` supplies coproducts of set sheaves.
- `Mathlib.CategoryTheory.Yoneda`: `CategoryTheory.uliftYoneda` (lines 43–66 read).
- Proof-only import `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`:
  `CategoryTheory.sheafification_sections_local` (entire declaration and docstring read).
  The node's other proof dependency `lem-trf-site-epimorphic-family-cover-lifts`
  has no recorded Lean declaration in the current DAG, so has no module to import.
  It is retained in the proof plan, without changing the item's proof dependencies.
  The existing local-sections declaration has stronger precoverage instance binders
  than the recorded general site axioms; it is imported for the proof plan, not
  used to add assumptions here. A future general-site proof must extract actual
  covers from covering sieves under IsSiteForCoverings, rather than impose those
  stronger instance binders on this statement.

Edge cases checked:

- I may be empty. An epimorphism from the empty sheaf coproduct onto H_U implies
  that U has an empty covering; B may be empty, and the index function and
  factorization arrows then exist. No Nonempty binder excludes this case.
- Empty covers in either local-representation or local-equality refinement give
  empty dependent-sum summands; the site composition axioms still apply.
- On a non-subcanonical site, sheafification-unit equality need not be sectionwise
  equality. The proof plan explicitly refines once more to obtain equality in C.
- Repetitions among a_i, infinite I and non-finite covering refinements are allowed;
  no Finite, distinctness, or covering hypothesis on the original family appears.
- Distinct object and morphism universes, and input indices in a larger universe,
  are retained through max u v w. An empty category has no U, hence no excluded case.

Searches actually run (2026-10-24):

1. `msearch.py ... leanfinder`, query “If arrows Ui to U induce an epimorphism
   from the coproduct of sheafified representables then there is a covering family
   of U factoring through those arrows”: eight hits, mainly
   `Sheaf.isLocallySurjective_iff_epi` and variants; no complete refinement statement.
2. `msearch.py ... loogle`, query
   `CategoryTheory.Presheaf.ofArrows_mem_iff_isLocallySurjective, CategoryTheory.Sheaf.isLocallySurjective_iff_epi`:
   no hits; the first identifier does not exist. Corrected query
   `"ofArrows", "IsLocallySurjective"` returned four topology/presheaf criteria.
   Read LocallySurjective.lean:415–497, particularly
   `GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`.
   It identifies a covering sieve with local surjectivity of a **presheaf**
   coproduct map. It does not state the required actual covering refinement from
   the epimorphic **sheaf** coproduct map.
3. `msearch.py ... grep`, query
   `sheafif.*(cover|refin)|(cover|refin).*sheafif` in `CategoryTheory/Sites`:
   eight hits concerning subsheafification, generic sheafification and dense
   subsites; no exact statement.
4. `msearch.py ... leansearch`, query “An epimorphism from a coproduct of
   sheafified representables gives an actual covering family factoring through
   the original arrows”: eight hits concerning effective epi families and local
   surjectivity of sheaf maps; no exact statement.
5. `rg` in `lean/WeilConjectures`, `lean/Sheaf` and Mathlib's sites directory for
   sheafified arrows, covering refinements and epi/Yoneda combinations; the closest
   project hit is `site_quasiCompact_iff_sheafifiedYoneda_quasiCompact`, which is
   the parent criterion and does not state this arbitrary-family refinement lemma.
   Its full signature was read. `grep -rn` for this item id in WeilConjectures
   returned no match. Name search for `sheafified_arrows_cover_refinement` in
   `dag/lean_names_upstream.json` and Mathlib returned no match.

Validation: `scompile.py Q26 lem-trf-site-sheafified-arrows-cover-refinement` compiled
this file in both sandbox and final-library-module modes successfully (2.5 s and
1.4 s), with no errors or warnings. Every binder and universe is explicit and
`autoImplicit` is disabled. The module has one named theorem, with the required
source/proof docstring, and no definitions. Only the item's `lean` field changes.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
