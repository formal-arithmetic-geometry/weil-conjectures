## Worker report

The module `Sheaf.CategoryTheory.TruncationDescends` states
`DerivedCategory.truncation_descends`. Its only proof is `sorry`; there are no new definitions,
new nodes, dependency modules, or statement corrections. The item's JSON changes only `lean`.

Hypotheses and introductory objects:

- The arbitrary abelian category is `A : Type u`, `[Category.{v} A]`, `[Abelian A]`.
- The chosen morphism universe of its derived category is `[HasDerivedCategory.{w} A]`.
  This is the size convention already present in def-weil-abstract-derived-category, not
  an extra existence assumption. All three universes are explicit and independent.
- The index is `q : ℤ`, without a nonnegativity or boundedness assumption.
- The localization is Mathlib's `DerivedCategory.Q` on `CochainComplex A ℤ`.
- Canonical truncation is `(ComplexShape.embeddingUpIntLE q).truncLEFunctor A`, whose
  objects and maps are Mathlib's `K.truncLE q` and `CochainComplex.truncLEMap s q`.
  It has the original terms below q, cycles at q, and zero above q.
- The cohomology single-complex functor is
  `HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
  CochainComplex.singleFunctor A q`. The single functor puts its argument in degree q,
  expressing H^q(-)[-q], without a reversed shift sign.
- The node introduces the canonical natural transformations i and j. They have no existing
  unbounded declarations in the project, so the theorem supplies them existentially with
  their characterizing equations, rather than defining them again or assuming additional
  input data. `i.app K ≫ K.ιTruncLE q = K.ιTruncLE (q - 1)` characterizes the inclusion
  because the truncation inclusion into K is monic. The degree-q component of `j.app K`,
  after the canonical `singleObjXSelf` identification, is exactly
  `(K.truncLEXIsoCycles q).hom ≫ K.homologyπ q`. All other target terms are zero, so this
  characterizes the entire projection. The types `i : ... ⟶ ...` and `j : ... ⟶ ...`
  make them natural transformations, including their naturality on complexes.

Clause-by-clause correspondence:

- (a) The first conjunct quantifies over every K, L and s, and assumes only `QuasiIso s`.
  Its three conclusions are `QuasiIso (truncLEMap s q)`, the same at q-1, and `QuasiIso`
  for the single-complex map of the degree-q cohomology map.
- The parenthetical cohomology description is the second conjunct:
  `r ≤ q → QuasiIsoAt (K.ιTruncLE q) r` and
  `q < r → IsZero ((K.truncLE q).homology r)` for all K and r.
  The isomorphisms below q are induced by the canonical inclusion, already natural as
  `ComplexShape.Embedding.ιTruncLENatTrans`, hence this states the natural comparison,
  not merely an unrelated objectwise isomorphism.
- (b) `T₀`, `T₁`, `H : DerivedCategory A ⥤ DerivedCategory A` are respectively the
  descended truncations at q-1 and q and descended single-cohomology functor.
  `e₀`, `e₁`, `eH` are the specified natural isomorphisms from `Q ⋙` each descent to the
  corresponding complex functor followed by Q. Functor composition is left to right in Lean.
  The source's category-of-fractions parenthesis describes an alternative construction with
  strict factorization; for the arbitrary chosen Mathlib localization we use the specified
  natural-isomorphism formulation, as the node explicitly allows.
- Each functor is unique up to unique compatible isomorphism: the three clauses quantify
  over every alternative descent G and comparison e and assert
  `∃! a : Tᵢ ≅ G, whiskerLeft Q a.hom ≫ e.hom = eᵢ.hom` (and the H version).
  Compatibility is essential: no assertion that all isomorphisms between the functors
  coincide is made.
- The two `∃!` clauses give unique `iD : T₀ ⟶ T₁` and `jD : T₁ ⟶ H` whose restrictions
  along Q agree with `whiskerRight i Q` and `whiskerRight j Q` after the comparison
  isomorphisms. The subsequent witnesses satisfy these same equations, so by uniqueness
  they are those unique transformations, not additional independent choices.
- The first final universal clause ranges over all derived objects K, L and all f : K ⟶ L.
  It asserts `iD.app K ≫ T₁.map f = T₀.map f ≫ iD.app L` and
  `jD.app K ≫ H.map f = T₁.map f ≫ jD.app L`. These are precisely the two naturality
  squares in the node, with composition written in Lean's left-to-right order.
- The second final universal clause ranges over all complex maps φ and gives the three
  compatibility equations for `T₀.map (Q.map φ)`, `T₁.map (Q.map φ)` and `H.map (Q.map φ)`
  with the corresponding Q-images. Each is the node's conjugation equation with its
  comparison inverse moved to the other side.

Dependency declarations read and used:

- def-weil-abstract-derived-category has status mathlib and no `lean` record, as allowed.
  Its `mathlib_match` names `DerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. I read its full definition, the
  `HasDerivedCategory` definition and chosen-universe documentation, `Q` and its
  localization instance. That record is usable and no dependency replacement is needed.
- Canonical complex truncation and its maps are from
  `Mathlib.Algebra.Homology.Embedding.CochainComplex`; its functor is
  `ComplexShape.Embedding.truncLEFunctor` from `Embedding.TruncLE`.
- `HomologicalComplex.homologyFunctor`, `QuasiIso`, and `QuasiIsoAt` are Mathlib's
  cohomology and quasi-isomorphism notions. `CochainComplex.singleFunctor` and
  `HomologicalComplex.singleObjXSelf` are from `Mathlib.Algebra.Homology.Single`.
- `Functor.whiskerLeft` and `Functor.whiskerRight` express restriction and Q-images of
  natural transformations; the namespace is opened explicitly in the module.

Edge cases checked before writing: q=0 and negative q are included by ℤ indexing; the
zero complex gives zero cohomology and the unique maps between zero objects; complexes
unbounded in either direction are allowed; r=q uses cycles modulo incoming boundaries;
r=q+1 is zero; a single nonzero term in degree q gives identity cohomology at q, and a
single term above q is annihilated. No enough-injectives, bounded-below, smallness of A,
or nonzero-object hypothesis is imposed. The universe w is exactly the dependency's
chosen localization morphism universe. No statement fault or disputed assertion found.

Searches (2026-10-11):

- msearch.py leansearch, query `truncation functors cochain complexes localization derived
  category`: UNAVAILABLE, Internal Server Error. Recorded without claiming a negative result.
- msearch.py leanfinder, query `canonical truncation of cochain complexes descends to derived
  category with natural inclusion and cohomology projection`: eight hits, all complex-level
  truncation maps, shortComplexTruncLE, and naturality; none states descent and uniqueness.
- msearch.py loogle, query `DerivedCategory.Q, CochainComplex.truncLE`: zero hits.
- msearch.py grep, query `truncLE.*(Q|descend)|Q.*truncLE|truncation_descends`, subdirectory
  `Algebra/Homology`: 25 hits include cohomology/quasi-isomorphism truncation lemmas and
  uses of Q inside DerivedCategory/TStructure proofs; no full descent theorem.
- Local rg for `truncLE|truncation|Truncation` in project and upstream CategoryTheory, and
  for `truncation_descends|Q.*truncLE|truncLE.*Q` in all upstream WeilConjectures and
  project lean/Sheaf: no matching full declaration. The project TruncationCouple module
  constructs bounded-below object-level maps, so it does not supply this unbounded
  statement or natural transformations and has not been copied.
- Local rg for the exact blueprint id in all upstream WeilConjectures: no match.
  Local rg for `DerivedCategory.truncation_descends` in dag/lean_names_upstream.json:
  no conflicting full declaration name.
- Read the Stacks source online because literature/stacks-project/*.tex is absent here:
  [08J5](https://stacks.math.columbia.edu/tag/08J5),
  [0118](https://stacks.math.columbia.edu/tag/0118), and
  [05RU](https://stacks.math.columbia.edu/tag/05RU).
  They give the canonical truncation terms, cohomology comparison, and derived localization
  used in this statement; no extra geometric hypothesis is involved.

Validation: scompile.py compiled this single module cleanly in 1.7 seconds on the server.
The first compile identified unopened Functor.whiskerLeft/whiskerRight; opening
CategoryTheory.Functor repaired that error. All binders and universes are explicit;
there is no local notation, local instance, private copy, hollow definition, or proved theorem.

## Second reading by F1

I independently compared the node's introductory objects, hypotheses, and conclusion with
`DerivedCategory.truncation_descends` in
`lean/Sheaf/CategoryTheory/TruncationDescends.lean`. The arbitrary abelian category is
rendered by `A : Type u`, `[Category.{v} A]`, and `[Abelian A]`; the selected derived-category
morphism universe is `[HasDerivedCategory.{w} A]`; and the unrestricted integer is `q : ℤ`.
These are exactly the source assumptions, with no boundedness, smallness, or geometric
condition added. The localization is `DerivedCategory.Q` on `CochainComplex A ℤ`.
The canonical truncations are rendered by
`ComplexShape.embeddingUpIntLE (q - 1/q).truncLEFunctor A`, with maps
`CochainComplex.truncLEMap`; the cohomology single complex is rendered by
`HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
CochainComplex.singleFunctor A q`. The first conjunct quantifies over every `K`, `L`, and
`s`, assumes only `QuasiIso s`, and gives the three quasi-isomorphism conclusions. The
second conjunct gives `QuasiIsoAt (K.ιTruncLE q) r` for `r ≤ q` and
`IsZero ((K.truncLE q).homology r)` for `q < r`. The existential `i` and `j` are natural
transformations of the stated complex functors and their two displayed component equations
are the inclusion and cycles-to-cohomology projection. The descended functors `T₀`, `T₁`,
and `H`, comparisons `e₀`, `e₁`, `eH`, their three compatible uniqueness clauses, and the
compatible unique descended transformations `iD`, `jD` all occur in the same order as the
node. The final two universal clauses render respectively naturality on derived morphisms
and the three comparison equations for every `Q.map φ`, with composition order matching
Lean's convention.

No mismatch was found and no source or Lean text was changed. In particular, the comparison
isomorphisms are correctly stated rather than equalities (equalities are only the category of
fractions special case in the source), and the equations for `iD` and `jD` retain the required
compatibility with those comparisons. The dependency declarations were checked: truncation
and its maps are Mathlib's `ComplexShape.Embedding.truncLEFunctor` and
`CochainComplex.truncLEMap`, cohomology and quasi-isomorphism notions are Mathlib's
`HomologicalComplex.homologyFunctor`, `QuasiIso`, and `QuasiIsoAt`, and localization is the
recorded `DerivedCategory.Q`.

Edge cases checked are `q = 0`, negative `q`, `r = q`, and `r = q + 1`; zero and single-term
complexes; complexes unbounded in either direction; and empty/zero objects. The signature
covers all of them without a nonzero or boundedness hypothesis, and its universes do not
exclude any case.

The existing-declaration searches were reread: LeanSearch was unavailable, LeanFinder and
Loogle found only complex-level truncation declarations, and grep over Mathlib, the upstream
project, and this project's `lean/Sheaf` found no descent theorem or conflicting declaration.
The Stacks places 08J5, 0118, and 05RU were checked against the canonical truncation,
cohomology comparison, and localization claims. The module compiles cleanly with
`scompile.py`; it contains only the required `sorry` proof and no hollow definition.
