## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceRelativeLciSourceLocus` states
`AlgebraicGeometry.AlgebraicSpace.relative_lci_source_locus`, with exactly one postponed
proof (`sorry`). It introduces no definitions. Source read: the complete statement and
proof of Stacks, spaces-more-morphisms.tex, Tag 06CA, and the preceding Tag 06C4 definition.
The original mathematical statement, proof plan, and all other existing node fields are
preserved. The only changes are `lean` and addition of two already landed definition
nodes to `stmt_deps`, as authorized by brief-stage2 §5: def-sfb-space-morphism-properties
and def-sfb-relative-finite-hilbert-groupoids. Their recorded declarations are reused.
Their dependency closures were inspected and neither depends on this item.

Hypotheses and clauses, individually:

- The scheme S and universe convention are `{S : Scheme.{u}}` with explicit `universe u`.
  All algebraic spaces are the recorded `AlgebraicSpace S`. There is no additional
  field, Noetherian, finiteness, separation, or universe-equality hypothesis.
- The three spaces and morphisms are `A C B`, `p : A ⟶ B`, `q : C ⟶ B`, and `u : A ⟶ C`.
  The triangle is `(hu : u ≫ q = p)`, with categorical composition in diagram order.
- Flatness of p and q is `hp : MapIsFlat p` and `hq : MapIsFlat q`. Local finite
  presentation is `hpLfp : MapIsLocallyOfFinitePresentation p` and its q counterpart.
  These are the existing universal compatible étale scheme-chart tests, using Mathlib's
  `Flat` and `LocallyOfFinitePresentation`. Neither u nor any base-change map is flat
  by assumption.
- Lci everywhere is the existing `RelativeFiniteHilbert.SpaceProperty
  (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f)`. `SpaceProperty` uses surjective
  étale scheme charts of the target and of the source fibre product. `SchemeLci`
  requires locally a factorization through a closed immersion into a smooth scheme,
  with `CotangentPresentation.IsKoszulImmersion` on the closed factor. The latter
  uses the actual kernel ideal and `RingTheory.Sequence.IsKoszulRegular` on a finite
  sequence; its length can be zero. Thus no regular-sequence/Noetherian substitution
  or extra unramifiedness condition is introduced.
- The open is `∃ U : OpenSubspace A`. Its point subset is rendered for every
  `x : Point A.obj.obj` by `x ∈ pointImage U.val.ι ↔ ∃ N : OpenSubspace A,
  x ∈ pointImage N.val.ι ∧ ... (N.val.ι ≫ u.hom.hom)`. This is exactly lci on some
  open neighbourhood, using the recorded field-valued point classes and point image.
- The lci restriction is `SpaceProperty ... (U.val.ι ≫ u.hom.hom)`; this uses the
  actual subfunctor inclusion, without choosing an unrelated representing object.
- The global criterion is `SpaceProperty ... u.hom.hom ↔ U.val = ⊤`.
  Here `⊤` is the full subfunctor of A; equality is equality as an open subspace of A.
- Arbitrary base change is quantified over `B' : AlgebraicSpace S` and `g : B' ⟶ B`.
  `A'` and `C'` can be any representatives of the fibre products: the hypotheses
  `IsPullback a.hom p'.hom p.hom g.hom` and
  `IsPullback c.hom q'.hom q.hom g.hom` assert exactly those two sheaf fibre-product
  squares. Such fibre products are algebraic spaces by the recorded fibre-product
  closure theorem. This representation-independent statement includes the chosen
  categorical pullbacks and all schemes and algebraic spaces in the node.
- The map `u'` is the induced map, uniquely specified by
  `u' ≫ c = a ≫ u` and `u' ≫ q' = p'`. Joint monicity of the two projections of
  the second pullback square gives uniqueness, and the first square and hu supply
  existence by the pullback universal property. These are specifying equations for
  the canonical map, not additional restrictions on g or on the original diagram.
- The existential `U' : OpenSubspace A'` is characterized by exactly the same
  neighbourhood formula for u'. Its restriction is lci, too. Thus it is U(u') in
  the statement, not an arbitrary open chosen only to satisfy a base-change equation.
- `U'.val = U.val.preimage a.hom.hom` says the open subspaces are equal, using the
  literal subfunctor preimage which represents A' times_A U. In particular this is
  stronger data than merely an uncharacterized isomorphism, but mathematically the
  very equality of subspaces required by the node, not an extra claim.
- `SpaceProperty ... u'.hom.hom ↔ U.val.preimage a.hom.hom = ⊤` is the first final
  criterion. The second is `SpaceProperty ... u'.hom.hom ↔ ∀ x : Point A'.obj.obj,
  mapPoint a.hom.hom x ∈ pointImage U.val.ι`. This is the clause that every point
  of A' maps into the original locus. No base-change case is discarded.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, and `IsSurjective` (including full docstrings).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` supplies the interpretation of the pullback squares.
  The theorem is imported publicly as the recorded statement dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` and its stalkwise interpretation;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, read with its homology-vanishing definition.
  These last three notions occur inside the reused `SchemeLci` and
  `CotangentPresentation.IsKoszulImmersion`, rather than private copies.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `pointTopologicalSpace`; its public point-classes module supplies `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- Added landed dependency `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`. Its existing
  dependency `ProperCurveModuli` supplies `mapPoint`; that definition was also read.
- Added landed dependency `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`:
  `RelativeFiniteHilbert.SchemeLci` and `RelativeFiniteHilbert.SpaceProperty`, both
  read in full. No Hilbert object, degree, moduli-stack datum, or unramifiedness
  binder is needed by these general helper declarations.

Recorded, stated proof dependencies are imported without `public`:
`SpaceEtalePresentationPropertyCriterion`, `AlgebraicSpaceEtaleOpenImage`,
`AlgebraicSpaceOpenFactorSchemeTests`, `AlgebraicSpacePointOpenCalculus`,
`SchemeEtaleSourceTargetProperties`, and Mathlib `Morphisms.Etale`.
Algebraic-space and fibre-product proof dependencies are already public statement
imports. The nodes lem-sfb-scheme-lci-etale-locality and
lem-sfb-scheme-relative-lci-base-change-points have no Lean records in the read clone;
there is no proof import for those unstated proof prerequisites. They are named in
full in the proof docstring. They are not prerequisites for typing this statement.

Edge cases checked before writing and during the second reading:

- Empty A: neighbourhood tests are vacuous; the unique open is the full empty source
  and the chart predicate admits the empty source chart. Empty C forces A empty.
- Empty B' or empty fibres: the theorem quantifies without a nonemptiness binder;
  the final all-points condition is vacuous when A' is empty, as required.
- Identity u of a possibly singular flat lfp family: identity is lci with the empty
  Koszul sequence. No regularity of A or B was imposed.
- Empty Koszul sequence, zero rings on empty affine charts, and variable local
  codimension are allowed by the reused definitions.
- Nonflat g (for example a closed point of a nonreduced base) is included. Only
  structural p and q are flat; the relative map may fail flatness.
- Non-surjective g and identity g are included. The pullback equations specialize
  to the usual chosen pullbacks, with the canonical comparison unique.
- No properness, closedness, quasi-compactness, surjectivity, or local Noetherian
  assumptions appear, and there is no independent small test universe.

Searches actually run:

1. `msearch.py ... leanfinder` with query "The local complete intersection locus of
   a morphism between flat locally finitely presented algebraic spaces is open and
   preserved by arbitrary base change": 8 hits on universal openness, smoothness,
   and flatness; no matching theorem.
2. `msearch.py ... leansearch` with query "local complete intersection locus open
   arbitrary base change flat locally finite presentation algebraic spaces": 8 hits
   on universal openness, lfp, and flat base change; no matching lci theorem.
3. `msearch.py ... loogle` with query
   `AlgebraicGeometry.AlgebraicSpace, AlgebraicGeometry.IsLocalCompleteIntersection,
   AlgebraicGeometry.IsLci`: 0 hits, unknown identifier AlgebraicGeometry.AlgebraicSpace.
   This is recorded as an unsuccessful name query, not evidence of a semantic match.
4. `msearch.py ... grep` with `SchemeLci|IsLocalCompleteIntersection|IsKoszulRegular|IsLci|IsLCI`
   in `AlgebraicGeometry`: 0 Mathlib hits. Direct Mathlib searches for definitions of
   lci/complete-intersection morphisms also found none.
5. `rg` of the same lci names and definitions in `lean/WeilConjectures` and
   `lean/Sheaf` found the existing general `SchemeLci`, `SpaceProperty`, and
   `IsKoszulImmersion` above; they are reused. The field-algebra complete-intersection
   predicate and flat-lci duality structures are narrower notions, not replacements.
6. `rg` of the item id and proposed declaration in `lean/WeilConjectures`,
   `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing statement.
   A search of lci locus names found only the unrelated isolated-lci curve-stack
   smooth-open theorem.
7. `tools/blueprint_refs.py search 'local complete intersection'` returned zero
   blueprint nodes. No new node is needed because the required notions are landed.

Validation: the required `scompile.py Q06 lem-sfb-space-relative-lci-source-locus`
compiled this file both in sandbox and library mode without errors or warnings
(4.0 s and 10.4 s). Only the theorem proof is postponed. There is no
STATEMENT-DISPUTED flag, statement correction, dependency interface repair, or new node.

## Second reading by Q06

Separate second pass by the same worker, with the node and completed Lean file open;
no other agent was started, as required by the dispatcher brief. I compared each clause
again with the Stacks 06CA statement and the Tag 06C4 pointwise definition.

The order of composition is correct: `u ≫ q = p`. Only the four structural flat/lfp
hypotheses occur. The lci predicate contains Koszul regularity rather than regularity
under a hidden Noetherian hypothesis, and the length is not forced positive. Each
pointwise clause quantifies over an actual open neighbourhood of the specified source,
with the restricted map given by inclusion followed by the original map. The first
existential includes both the lci restriction and the whole-source iff. The base-change
clause uses two actual sheaf pullback squares; u' satisfies both projection equations,
so it cannot be an unrelated map. Its open has its own pointwise characterization and
lci restriction, and is equal as a subfunctor to the pulled-back original open. Both
final iff clauses occur, including every point of A'. All hypotheses and conclusions
allow empty sources and arbitrary g.

I also checked the two added landed statement dependencies against their recorded
interfaces and dependency closures. Their general helpers have no moduli parameters
in the used signatures, and no new DAG cycle is introduced. The named proof
prerequisites without Lean records are correctly omitted from imports. No mismatch
was found and no mathematical statement was changed in this pass. Independent
maintainer review remains the next review step.
