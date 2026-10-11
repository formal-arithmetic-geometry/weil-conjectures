## Worker report

The module defines `CategoryTheory.DecreasingFiltration.image`.  For an abelian
category `C`, objects `A B : C`, a decreasing filtration `F` on `A`, and a
morphism `f : A ⟶ B`, its step at `i : ℤ` is
`(Subobject.«exists» f).obj (F.step i)`.  This is Mathlib's image-of-subobject
functor, so it renders `FⁱB := im(FⁱA → B)`.  The `antitone_step` field renders
the clause `Fⁱ⁺¹B ≤ FⁱB`: it maps `F.antitone_step` through the order-preserving
`Subobject.«exists» f` functor.  No other hypotheses or clauses occur in the
node statement.

The statement dependency `def-sp-filtration` is imported from
`Sheaf.CategoryTheory.Filtration`, declaration
`CategoryTheory.DecreasingFiltration`.  The dependency `def-sp-abelian` is the
Mathlib declaration `CategoryTheory.Abelian` (in
`Mathlib/CategoryTheory/Abelian/Basic`).

Edge cases checked: the index type is all of `ℤ`; the source or target object
may be zero; the morphism may be zero or an isomorphism; and no nonempty or
finite-index assumption is introduced.  In particular, `Subobject.«exists»`
maps the zero subobject to the zero image and maps an isomorphism's steps to
the corresponding target subobjects.

Searches for an existing definition: `msearch.py ... leanfinder` with the
image-filtration query returned only `CategoryTheory.Abelian.imageFunctor` and
unrelated declarations; `... loogle` for
`CategoryTheory.Subobject, image, filtration, Filtered` returned zero hits;
`... grep` for `imageFiltration|image filtration|Filtered in Mathlib` returned
no matches.  `rg` over `WeilConjectures/` and the project found only the
specialized spectral-sequence `imageFiltration`, not this general notion.
The recorded node searches also included unavailable LeanSearch and additional
Loogle/grep queries, all with no exact match.

No `STATEMENT-DISPUTED` or node fault.

## Second reading by C1

I reread the node and `ImageFiltration.lean`.  The binders `A`, `B`, `F`, and
`f` correspond exactly to the filtered object and morphism in the node.  The
`step` field is precisely the image `im(FⁿA → B)`, and the `antitone_step` field
is precisely the stated inclusion of successive images.  The imported
`DecreasingFiltration` supplies the meaning of a decreasing filtration, while
`Subobject.«exists»` supplies categorical images.  No clause, hypothesis, or
edge case from the node was added or omitted, and no change was needed after
this reading.
