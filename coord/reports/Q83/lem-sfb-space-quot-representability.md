## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuotRepresentability` states
`AlgebraicGeometry.AlgebraicSpace.exists_properQuot_representing_space`, with its
whole proof postponed by `sorry`. The statement is unchanged from the DAG node.
No definitions, helper nodes, dependency repairs, or statement corrections are needed.
The source read was Stacks `quot.tex`, Situation 09TR (`situation-quot`) and
Proposition 09TU (`proposition-quot`). The latter explicitly separates algebraicity
for arbitrary quasi-coherent F from the conditional local finite presentation.

Hypotheses and clauses, matched individually:

- A scheme S is `{S : Scheme.{u}}`, with the universe explicitly bound.
- The spaces A and B over S are `{A B : AlgebraicSpace S}`, and their morphism is
  `(a : A ⟶ B)`. This is the recorded full subcategory of fppf sheaves, not scheme-only
  geometry. The inherited size convention is represented by universe polymorphism.
- Finite presentation of a is `ha : ProperQuotFinitePresentation a`. This unfolds to
  chartwise local finite presentation, quasi-compactness, and quasi-compact diagonal.
- Separatedness is `hsep : MapIsSeparated a`, the representable closed-immersion diagonal.
- An arbitrary quasi-coherent O_A-module is `(F : A.QCoh)`. Its underlying module is
  `F.obj`. There is no finite-presentation, flatness, or properness assumption on F.
- The proper-support Quot functor is exactly the recorded `properQuotFunctor a ha F`.
  Its construction uses sheaf fibre products, tensor pullback, and admissible targets
  that are quasi-coherent, finitely presented, flat over T, with proper support.
  Its values quotient actual surjections by intertwining target isomorphisms.
- Existence of R over S and a morphism to B is `∃ (R : AlgebraicSpace S) (r : R ⟶ B)`.
- Every scheme T over B, including its specified structural morphism, is an object
  `T : ProperQuotTest B = CostructuredArrow yoneda B.obj.obj`. Its `T.left : Over S`
  is the underlying S-scheme and `T.hom` is its map to B.
- The relative Hom set is the subtype
  `{ f : yoneda.obj T.left ⟶ R.obj.obj // f ≫ r.hom.hom = T.hom }`.
  By Yoneda and the full embeddings, this is precisely maps of spaces T → R over B;
  it imposes no representability assumption on r.
- The family `e` consists of equivalences from these Hom sets to
  `(properQuotFunctor a ha F).obj (op T)`, so the asserted maps are bijections.
- Naturality is the first conjunct after `e`: for every `h : T' ⟶ T` and maps f, f'
  with `yoneda.map h.left ≫ f.val = f'.val`, the equation identifies `e T' f'` with
  `(properQuotFunctor a ha F).map h.op (e T f)`. Such an f' exists uniquely for
  every h and f: it is their composite, whose triangle follows from the commuting
  triangle for h. Quantifying over f' and its equality avoids introducing a helper
  or a proof term inside the statement, and is exactly contravariant naturality.
- The final conjunct is `F.obj.IsFinitePresentation → MapIsLocallyOfFinitePresentation r`.
  It concerns the same R and r as the unconditional bijections. It requires neither
  quasi-compactness nor finite presentation of r, as the node only concludes local
  finite presentation.
- No flatness or properness of a, and no finite presentation of F, occurs among
  the theorem's assumptions. Arbitrary, including nonflat, test morphisms occur.

Recorded statement dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  its fppf-sheaf full-subcategory morphisms. The module and full defining signatures
  were read, including scheme-test representability and the atlas condition.
- `def-weil-size-convention` is explicitly a metatheoretic convention, with no
  declaration to import; the theorem binds its universe u explicitly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace` (and the node's
  `etaleCover_pullback` and `etale_fibreProduct_isScheme`, read in its source).
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`:
  `AlgebraicGeometry.AlgebraicSpace.ProperQuotTest`, `ProperQuotFinitePresentation`,
  `ProperQuotient`, `ProperQuotientRel`, `ProperQuotClasses`, `properQuotFunctor`,
  and its canonical tensor-pullback transitions, read in full. Its public imports
  supply `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`, and `QCoh` without
  redeclaring any of them.

All statement-dependency modules are public imports. Plain proof imports are the
recorded modules `SpaceCoherentStackGeneral`, `AlgebraicSpaceFlatProperFpLocality`,
`AlgebraicSpaceModulePullbackQuasiCoherent`, `AlgebraicSpaceOpenSubspace`,
`RepresentableSourceAlgebraic`, `AlgebraicSetoidSpace`, and
`SpaceLocalPropertiesChartTest`. The proof-only nodes
`lem-sfb-space-module-hom-affine`, `lem-sfb-space-module-surjectivity-open`,
`lem-sfb-space-separated-fp-composition`, and
`lem-sfb-smooth-cover-flat-lfp-descent` currently have no Lean record and so no
module import; their exact roles remain in the theorem's full proof docstring.
They are not needed to type the statement. No import cycle was introduced.

Edge cases checked before writing:

- The zero source module is allowed; its only quotient is zero, so the expected
  representing space is B with the identity map. The conditional conclusion
  permits this identity without any finiteness assumption on B over S.
- Empty A, empty B, and empty test schemes are allowed by all binders and by the
  existing quotient definition. For empty A the zero quotient gives the terminal
  relative functor; for an empty test scheme both the relative section and quotient
  sets have their unique empty-base element.
- A non-finitely-presented quasi-coherent F remains within the theorem, and only
  the final implication has a finite-presentation antecedent.
- Nonflat and nonproper separated finitely presented a are allowed. No property
  of a beyond ha and hsep is accidentally assumed.
- Identity and composite test maps, arbitrary test schemes (including nonreduced
  ones), and nonflat test maps all occur in the universal naturality clause.
- Modules and quotient classes retain their recorded coefficient universes:
  `properQuotFunctor` takes values in `Type (u + 1)`, while the equivalences can
  relate this to the relative Hom subtype without assuming a universe equality
  or an unrecorded smallness condition.

Searches made, all on 2026-10-24:

- `msearch.py leanfinder`, query “The proper support Quot functor of any quasi coherent
  module on a separated finitely presented algebraic space is represented by an
  algebraic space”: eight hits about `SheafOfModules` finite/quasi-coherent
  presentation data, none giving Quot representability.
- `msearch.py leansearch`, query “Quot functor algebraic space separated finite
  presentation”: eight hits about categorical quotients, polynomial functors,
  scheme separatedness, and separation quotients, none matching the theorem.
- `msearch.py loogle`, query `AlgebraicSpace, properQuotFunctor, representable`:
  zero hits, unknown identifier `AlgebraicSpace` in the Mathlib search service.
- `msearch.py grep`, query `properQuot|Quot.*[Rr]epresent|quot.*[Rr]epresent`:
  fourteen unrelated Mathlib hits concerning categorical or algebraic quotients.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`,
  patterns `properQuot|quot_represent|[Qq]uot.*[Rr]epresent|schemeSpaceMap|MapIsSeparated`:
  found the existing properQuotFunctor construction and the chartwise morphism
  predicates; no representing theorem. The item-id search in WeilConjectures
  returned no hit. A second definition of Quot is therefore unnecessary and avoided.
- The proposed name `exists_properQuot_representing_space` is new in these searches.

Validation: `scompile.py Q83 lem-sfb-space-quot-representability` compiled the
single delivered file in sandbox mode and its library module mode successfully,
with no errors or warnings (24.8 s and 3.3 s respectively). All variables and
universes are explicitly bound; no diagnostics remain in the file. The node copy
changes only `lean`, keeping indent 1, Unicode, and a final newline. Its recorded
signature is extracted verbatim from the theorem in the file.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
