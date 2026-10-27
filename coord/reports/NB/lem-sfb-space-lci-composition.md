## Worker report

Item: lem-sfb-space-lci-composition. The new module
`Sheaf.AlgebraicGeometry.SpaceLciComposition` states the two conclusions as
`AlgebraicGeometry.AlgebraicSpace.lci_comp` and
`AlgebraicGeometry.AlgebraicSpace.lci_of_etale`. Both proofs are exactly `by sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The item node changes only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme S is the explicit binder `{S : Scheme.{u}}` in both declarations.
- X, Y and W are algebraic spaces over S: `{X Y W : AlgebraicSpace S}` in
  `lci_comp`. This is the dependency's actual full subcategory of fppf sheaves,
  including representable diagonal and existence of a representable surjective
  etale atlas; arbitrary sheaves are not substituted for algebraic spaces.
- The size convention is an explicit `universe u`. Schemes, the over-category,
  and the presheaf value types used by the recorded interface use that level;
  there is no equality assumption between independently specified universes.
- The two space morphisms are `(f : X ⟶ Y) (g : Y ⟶ W)`, hence over S.
  Their underlying natural transformations are `f.hom.hom` and `g.hom.hom`.
- The lci hypothesis on f is `hf : RelativeFiniteHilbert.SpaceProperty
  (fun _ _ h ↦ RelativeFiniteHilbert.SchemeLci h) f.hom.hom`; `hg` renders
  the identical hypothesis on g.
- This is exactly the condition of def-sfb-relative-finite-hilbert-groupoids:
  `SpaceProperty` existentially supplies surjective etale V → target and
  surjective etale U → source ×_target V, with a scheme morphism q : U → V
  and the equality identifying its Yoneda map with the projection composite.
  `SchemeLci q.left` says that for each point there is an open neighbourhood,
  a closed immersion i into a scheme P, and a smooth q from P to the target,
  with the stated factorization equality and
  `CotangentPresentation.IsKoszulImmersion i`.
- The latter recorded predicate uses affine neighbourhoods of each point of
  the immersed scheme, a finite family `a : Fin r → Γ(P,W)`,
  `RingTheory.Sequence.IsKoszulRegular a`, and equality of its generated ideal
  with the actual kernel ideal. Thus the finite Koszul-regular requirement is
  retained, rather than replaced by regular sequences or bare closed immersions.
- The composition conclusion is the same `SpaceProperty` with `SchemeLci`,
  applied to `(f ≫ g).hom.hom`. Lean's f ≫ g is the paper's g ∘ f.
- The etale clause quantifies independently over `{X Y : AlgebraicSpace S}`
  and `(e : X ⟶ Y)` in `lci_of_etale`. Its hypothesis is
  `SpaceProperty (fun _ _ h ↦ Etale h) e.hom.hom`: the compatible etale
  scheme-chart test explicitly requested by the item. It does not impose an
  additional representability hypothesis on the space map.
- Its conclusion is `SpaceProperty (fun _ _ h ↦ SchemeLci h) e.hom.hom`.
- No flatness of f or g, separation of any space or map, Noetherian condition,
  nonemptiness, characteristic restriction, finite global rank, or prescribed
  atlas occurs among the binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, including their structure signatures and docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, and
  `IsSurjective`; the category's morphisms supply the natural transformations.
- `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`:
  `AlgebraicGeometry.RelativeFiniteHilbert.SchemeLci` and `SpaceProperty`.
  The recorded main declaration `RelativeFiniteHilbert.groupoid` belongs to
  the larger dependency node; the two listed predicates in its declarations
  are the exact portions needed here. Their signatures and full docstrings
  were read directly in the source.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, the
  recorded affine-local etale scheme predicate, supplies the chart condition.
- `def-weil-size-convention` is the recorded metatheoretic convention without
  a declaration; it is implemented by the explicit universe binder.

The module publicly imports the statement dependency modules. Plain proof
imports include the recorded presentation criterion, etale-smooth theorem,
Koszul regularity, closed immersions, affine space and smoothness modules.
The proof nodes lem-sfb-scheme-lci-etale-locality,
lem-sfb-lci-polynomial-local-factorization, lem-sfb-koszul-immersion-composition,
and lem-sfb-unramified-etale-compatible-charts have no recorded declarations
in the read snapshot and hence supply no import. These are proof prerequisites,
not missing objects in the statement. The theorem docstrings retain all six
proof steps of the node, including the coefficientwise polynomial Koszul
argument and the empty-sequence argument for the etale clause.

Sources read: spaces-more-morphisms.tex definition-lci, lemma-composition-lci
and lemma-flat-lci (06C4, 06C8, 06C9); spaces-morphisms.tex lemma-etale-smooth
and lemma-smooth-syntomic (04XX, 06CP). These give exactly the two assertions.
No node fault or statement dispute was found.

Edge cases checked by reading the definitions:

- Empty source: `SchemeLci` is pointwise and therefore vacuous on an empty
  source. There is no nonempty-source hypothesis on either theorem.
- Zero generators: `r : ℕ` in `IsKoszulImmersion` includes r = 0. The zero
  ideal of an identity immersion is generated by the empty family. The
  Koszul regularity condition asks only for homology in positive degrees.
- Identity and isomorphism maps: the identity/smooth factorization used in
  the etale clause is admitted; no positive codimension is required.
- Nonflat lci maps: the composition theorem includes them, since neither
  `hf` nor `hg` mentions flatness. Arbitrary base change stability is not
  claimed. The polynomial base change in the proof is the appropriate one.
- Noetherian and characteristic assumptions are absent from both the source
  statements and the Lean binders.

Searches for an existing declaration, all run through the prescribed msearch
wrapper with group NB and this item (2026-10-24):

- LeanFinder query: "Composition of local complete intersection morphisms of
  algebraic spaces is local complete intersection and every etale morphism
  is local complete intersection". Eight hits, concerning scheme etale,
  smooth and ordinary immersion composition; no lci-space composition result.
- LeanSearch query: "local complete intersection morphisms of algebraic
  spaces are stable under composition". Eight hits: general stability of
  morphism properties, integral/separated/finite/formally-unramified/smooth
  composition and source-local closure; none states the present result.
- Loogle query: `AlgebraicGeometry.RelativeFiniteHilbert.SchemeLci,
  AlgebraicGeometry.RelativeFiniteHilbert.SpaceProperty`. Zero hits; the
  external index does not know the project's SchemeLci identifier.
- Mathlib grep through msearch:
  `SchemeLci|SpaceProperty|IsLocalCompleteIntersection|KoszulRegularImmersion`
  under AlgebraicGeometry: zero hits.
- Local rg of `SchemeLci|SpaceProperty|space_lci_comp|lci_comp|lci_of_etale`
  in Mathlib and WeilConjectures: no matching declarations. Local rg in
  lean/Sheaf finds the two reused predicates and the existing affine lci
  conormal splitting consumer, but no result matching this item.
- Local rg for `lem-sfb-space-lci-composition` in WeilConjectures: no hits.
  The upstream name index also has no binding for the item.

Validation: scompile.py compiled both the sandbox and intended library module
successfully, in 3.6 s and 4.4 s respectively, with no errors or warnings.

## Second reading by NB

The dispatcher explicitly prohibited starting other agents; the maintainer
performs the independent review of this delivery. This section records my own
second reading, not an independent worker's review.

I reopened the node and final module and compared the binders and conclusions.
`lci_comp` has exactly the two lci hypotheses and the composed-map conclusion.
`lci_of_etale` separately quantifies an arbitrary space map, so the etale
assertion is not restricted to the maps already assumed lci in the first
assertion. The chart predicate is reused directly in all five occurrences;
composition order is f ≫ g; the etale hypothesis uses the stated scheme-chart
interpretation with Mathlib Etale. I checked that both morphisms really have
algebraic-space endpoints, and that no flatness or finiteness assumption was
introduced. The proof docstrings cover the two conclusions and retain the
source's intermediate reductions. No mismatch was found and no statement
correction was required.
