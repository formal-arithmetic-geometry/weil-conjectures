## Worker report

The module `Sheaf.AlgebraicGeometry.SectionMarkedFinitePartsScheme` states
`AlgebraicGeometry.exists_section_marked_finite_parts_scheme`, with `sorry` as its
whole proof. Its auxiliary abbreviation `SectionMarkedFiniteOpenPair` spells out
this node's own pair set; it has real data and is listed in `lean.declarations`.
It does not introduce a second definition of schemes, finite morphisms, opens,
fibre products, quasi-finiteness, or representability. As in the existing
unmarked finite-part interface, pullback naturality is expressed directly by
projection equations and inverse images of opens.

The source read was `literature/stacks-project/spaces-more-groupoids.tex`,
`lemma-finite-separated-flat-locally-finite-presentation` (04RI),
`equation-finite-conditions-variant` (04RQ), `lemma-finite-plus-section` (04RR),
and the fibre-piece paragraph in `lemma-quasi-splitting` (04RW). These give the
marked subfunctor, schemehood, separatedness, etaleness, and the residue-field
point construction. The recorded proof's use of the elementary etale finite-piece
lemma (02LK) is retained. The source's reversed order of fibre-product factors
is represented by the node's specified `pullback f.left a.left` throughout.

Hypothesis and clause matching:

- A scheme S in the fixed universe is `{S : Scheme.{u}}`, with explicit `universe u`.
  The S-schemes X and Y are `(X Y : Over S)` and the S-morphism is `(f : X ⟶ Y)`.
- Separatedness, flatness, and local finite presentation are respectively
  `[IsSeparated f.left]`, `[Flat f.left]`, and
  `[LocallyOfFinitePresentation f.left]`. No quasi-compactness, no Noetherian
  hypothesis, and no global quasi-finiteness are imposed.
- The section is `(σ : Y ⟶ X)` and `(hσ : σ ≫ f = 𝟙 Y)`; categorical composition
  has precisely the order f composed with σ. The section is over S as required.
- Tests are all `T : Over S`. In `SectionMarkedFiniteOpenPair f σ T`, the sigma
  coordinate `a : T ⟶ Y` is the S-map a. Its second coordinate is an open
  `Z : (pullback f.left a.left).Opens`, with its canonical restricted scheme
  `Z.toScheme` and immersion `Z.ι` from Mathlib. Opens are subsets with their
  induced structure, so different isomorphic presentations are not extra data.
- Finiteness over T is `IsFinite (Z.ι ≫ pullback.snd f.left a.left)`.
  The remaining predicate is `∃ s : T.left ⟶ Z.toScheme` with
  `s ≫ Z.ι ≫ pullback.fst ... = a.left ≫ σ.left` and
  `s ≫ Z.ι ≫ pullback.snd ... = 𝟙 T.left`. These are exactly factorization of
  `(σ a, id_T)` through Z by the fibre-product universal property. The witness
  belongs to Prop; the pair set carries no chosen lift or extra choices.
- The representing S-scheme and its S-morphism to Y are
  `∃ (M : Over S) (g : M ⟶ Y)`. The equivalences
  `e : ∀ T : Over S, (T ⟶ M) ≃ SectionMarkedFiniteOpenPair f σ T`
  are exactly the required bijections of S-morphism sets with the pair sets.
- The first conjunct `(e T q).1 = q ≫ g` identifies forgetting the open with
  composition into g for every T and q.
- Pullback naturality is the second conjunct, for all T, T', h, and q. Its map
  b has the two required projection equations: the X coordinate stays fixed,
  and the T coordinate is composed with `h.left`. Those equations uniquely
  characterize the canonical fibre-product map, rather than an arbitrary map.
  The equation `(e T' (h ≫ q)).2.val = b ⁻¹ᵁ (e T q).2.val` is exactly pullback
  of the open part. The first conjunct also identifies its target map with
  `h ≫ q ≫ g`. Consequently these clauses give the specified functor, not
  merely unrelated objectwise bijections. Functor laws follow from pullback
  uniqueness and inverse-image laws; no extra theorem with postponed proof
  is used to define an action.
- `IsSeparated g.left ∧ Etale g.left` renders both stated properties of g.
- The universal open is `(e M (𝟙 M)).2.val`. It is a genuine open of the fibre
  product; its finite projection and section factorization are its subtype
  predicate. `IsClosed (...)` is its additional closedness. The first conjunct
  at the identity identifies its base map with g, so it is exactly the
  universal part of `X ×_Y M`. Naturality at q = identity identifies its pullback
  with every represented pair. There is no independent universal family.
- For every `y : Y.left`, the condition is the recorded predicate
  `f.left.IsQuasiFiniteAtPoint (σ.left y)`. Its conclusion is
  `∃ m : M.left, g.left m = y ∧ IsIso (g.left.residueFieldMap m)`.
  The equality identifies the source field κ(g(m)) with κ(y); `IsIso` is
  exactly the assertion that this induced field map is an isomorphism.
- The schemes M, its universal open, and all fibre products are in `Scheme.{u}`.
  This realizes the final chosen-universe clause without a larger-scheme witness.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated` (defined in its
  imported `Morphisms.Separated`, as closed diagonal), and proof input
  `IsProper.of_comp`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with its stalkwise
  characterization; `Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the canonical
  `Scheme.Opens.toScheme` and `Scheme.Opens.ι` are the restricted open subschemes.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and the uniquely determined induced map.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsQuasiFiniteAtPoint`, including its local finite-type requirement.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, the map induced by the local stalk homomorphism.
- `def-weil-size-convention` has a convention-only record; it is rendered by
  explicit universe polymorphism rather than a nonexistent Lean object.

All stated proof modules are imported, including
`Sheaf.AlgebraicGeometry.UnmarkedFiniteOpenPartsSpace`,
`Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme`, and the upstream
`SeparatedLqfBaseChange`, `QuasiFiniteAtPointIsolated`, and `EtaleLocalFiniteAtPoint`.
Mathlib proof leaves are supplied by `FiniteType`, `Proper`, `QuasiFinite`,
`UniversallyOpen`, `PullbackCarrier`, `ClosedImmersion`, `OpenImmersion`, `Finite`,
`Flat`, `FinitePresentation`, `Etale`, and `ResidueField`.
The proof docstring reproduces all six DAG proof steps and names their inputs.

Edge cases checked:

- Empty T has its unique empty open and a factorization from the empty scheme;
  the pair set remains correct and no Nonempty assumption excludes it.
- If Y is empty, the point assertion is vacuous and M can be empty. The existence
  of a section already rules out an empty X over nonempty Y.
- The empty open on nonempty T cannot satisfy the section factorization. Thus
  unmarked empty parts do not accidentally survive the marked condition.
- For the identity family, containing the identity section forces the whole
  open, so the pair set reduces to maps into Y and M is Y as expected.
- A quasi-finite section point is required only in the final implication; the
  representing scheme still makes sense for families with no such points.
- Non-quasi-compact and non-Noetherian schemes, arbitrary characteristics, and
  arbitrary universe u remain allowed. The residue-field map uses the genuine
  project predicate for quasi-finiteness and the genuine induced field map.

Searches actually made:

- `msearch.py ... leanfinder`: “The functor of finite open subschemes containing
  a section of a separated flat locally finitely presented scheme is represented
  by a separated etale scheme”. Eight hits: Etale over-categories and
  `Scheme.LocalRepresentability.representableBy`/`isRepresentable`. These require
  previously constructed charts and do not state this theorem.
- `msearch.py ... loogle`: `"Scheme", "finite", "section"`. Zero hits.
- `msearch.py ... grep` in `AlgebraicGeometry`:
  `finite[Pp]art|finite_part|marked.*finite|finite.*subscheme.*represent`.
  Zero hits.
- `msearch.py ... leansearch`: “Scheme representing finite open subschemes of a
  flat family containing a section”. Eight hits concerning opens, affine opens,
  restriction to opens, and flatness; no marked finite-part theorem.
- `rg` over both live source roots, for `finiteOpen|FiniteOpen|finite_open|finiteParts|finitePart|markedFinite`,
  found the unmarked theorem and unrelated finite-parts presentations. Reading
  `UnmarkedFiniteOpenPartsSpace.lean` established that it lacks a section and
  the separated representing-scheme conclusion. The unmarked interface uses
  the same direct pullback-naturality encoding employed here.
- `rg` over both roots for
  `SectionMarkedFiniteOpenPair|exists_section_marked_finite_open_parts_scheme|marked.*[Ff]inite.*[Pp]art|[Ff]inite.*[Oo]pen.*[Pp]air`
  found the unmarked theorem and the downstream quasi-splitting proof citation,
  not an existing pair abbreviation or theorem.
- `rg` over both roots and `dag/lean_names_upstream.json` for the item id and
  marked-finite names found no declaration for the item. The required
  `grep -rn` of the item id in `lean/WeilConjectures` found none.

No statement correction, dependency repair, new node, or disputed statement is
needed. The sole `sorry` is the assigned theorem. Compilation through
`scompile.py` passed for both the isolated sandbox and the final module with no
errors or warnings. The first compile diagnosed an ambiguous `Set (pullback ...)`
coercion (Lean inferred the category of types); explicitly coercing the scheme
as `Set ↑(pullback ...)` fixed it without changing the mathematical statement.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
