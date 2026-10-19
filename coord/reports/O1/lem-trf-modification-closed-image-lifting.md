## Worker report

The module `lean/Sheaf/Paper/ModificationClosedImageLifting.lean` states
`AlgebraicGeometry.Orgogozo.exists_finite_cover_modified_closedImage` with proof `sorry`.
The source is Orgogozo, *Modifications et cycles proches sur une base générale*,
Lemma 3.2.1, pp. 7--8 (the blueprint node
`lem-trf-modification-closed-image-lifting`). The blow-up is the canonical
`Scheme.IdealSheafData.blowup` and its structure morphism
`Scheme.IdealSheafData.blowupMap` from the upstream blow-up construction; the
modification predicate is `AlgebraicGeometry.Orgogozo.IsModification`.

The Lean statement renders the source clauses as follows.

* `{S F' : Scheme.{u}}` introduces the ambient scheme and the proper source.
  `[IsReduced S] [IsNoetherian S] [IsReduced F'] [IsNoetherian F']` says that
  both schemes are reduced and Noetherian. `(g : F' ⟶ S) [IsProper g]` is the
  proper morphism hypothesis.
* `(F : Scheme.{u}) (i : F ⟶ S) [IsClosedImmersion i] [IsReduced F]` gives
  the reduced closed subscheme representing the closed image. The equation
  `himage : Set.range i = Set.range g` identifies its underlying closed image,
  and `factor : ∃ gF : F' ⟶ F, gF ≫ i = g` supplies the scheme-theoretic
  factorization through the reduced closed image.
* `∃ I : S.IdealSheafData` chooses the center and the canonical blow-up
  `I.blowupMap : I.blowup ⟶ S`. `IsNowhereDense (I.support : Set S)` says the
  center is nowhere dense, while `IsModification I.blowupMap` says the blow-up
  is a modification.
* `∃ G : Scheme.{u}, gG : G ⟶ F` makes `G` an `F`-scheme. The map
  `a : G ⟶ F'` is an `F`-morphism through
  `a ≫ g = gG ≫ i`. The map
  `q : G ⟶ pullback i I.blowupMap` is the map to
  `F ×_S I.blowup`; its `F`-compatibility is
  `q ≫ pullback.fst i I.blowupMap = gG`. Finally `IsFinite q ∧ Surjective q`
  is the required finite surjective `F`-morphism.

The statement dependencies and declarations used are:

* `def-trf-orgogozo-induction-data`: imported from
  `Sheaf.Paper.OrgogozoInductionData`, using
  `AlgebraicGeometry.Orgogozo.IsModification` (the same module also supplies
  the source's modification vocabulary).
* `def-weil-proper-morphism`: Mathlib
  `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
* `def-weil-closed-immersion`: Mathlib
  `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
* `def-weil-finite-integral-morphism`: Mathlib
  `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
* `def-pc-fibre-product`: Mathlib
  `CategoryTheory.Limits.pullback`, with projections
  `CategoryTheory.Limits.pullback.fst` and `.snd`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.

The canonical blow-up declarations are imported from
`WeilConjectures.Blowup.AdmissibleBlowup` (ultimately
`WeilConjectures.Blowup.Gluing`), where
`Scheme.IdealSheafData.blowup` and `blowupMap` are real constructions by
relative gluing of affine Rees blow-ups. The proof-plan imports are retained
for the stated proof dependencies: `WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology`,
`WeilConjectures.Blowup.Proper`, `WeilConjectures.Blowup.Density`,
`WeilConjectures.Blowup.Extension`, and
`WeilConjectures.Compactification.StrictTransformBlowup`.

Edge cases checked before writing:

* If `F` is empty, the conclusion permits `G` empty; the finite-surjective map
  to the empty fibre product is represented by the same `IsFinite` and
  `Surjective` clauses.
* If the closed image is empty, the source proof's empty-product center and
  identity blow-up are represented by an ideal with empty support and the
  canonical `blowupMap`.
* Zero-dimensional `S`, zero-dimensional `F'`, and an identity proper map are
  covered by the same typeclass hypotheses; no positive-dimension assumption
  is introduced.
* The index of the blow-up center is the ambient scheme's own universe, so no
  independent universe restriction is imposed.

Searches performed:

* `msearch.py ... leanfinder "Gabber finite cover of a modified closed image"`:
  eight hits, all generic scheme covers/affine-transition declarations; no
  matching Gabber statement.
* `msearch.py ... loogle "IsNowhereDense, IsModification, blowupMap"`:
  zero hits (the combined identifier pattern was unknown); this did not supply
  an existing declaration.
* `msearch.py ... grep "closedImage|modified_closed|finite_cover" WeilConjectures/AlgebraicGeometry`:
  zero hits.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for the declaration name and
  closed-image/blow-up vocabulary found no existing declaration of this
  statement. The upstream source was inspected and its canonical blow-up
  definitions were used.

No new definition node or dependency repair was needed, and there is no
`STATEMENT-DISPUTED` flag.

## Second reading by N1

Independent reading by the maintainer's reviewer (the worker delivered directly; this section
replaces the placeholder). Node statement against the Lean, clause by clause:

* g : F' → S proper, F', S reduced Noetherian — `{S F' : Scheme.{u}} [IsReduced S] [IsNoetherian S]
  [IsReduced F'] [IsNoetherian F'] (g : F' ⟶ S) [IsProper g]` (Mathlib `IsProper`, the recorded
  declaration of def-weil-proper-morphism). Correct; `IsNoetherian F'` is the node's own hypothesis.
* F ⊂ S the closed image with reduced induced structure — `(F) (i : F ⟶ S) [IsClosedImmersion i]
  [IsReduced F] (himage : Set.range i = Set.range g)`. A reduced closed subscheme is determined up to
  unique isomorphism by its (closed) support, so this characterises the reduced closed image. The extra
  `factor : ∃ gF, gF ≫ i = g` is implied by the others (F' reduced, range g ⊆ range i), so it
  does not narrow the statement; it records proof Step 1 for the caller. Correct.
* a blowup p : S' → S with nowhere dense centre — `∃ I : S.IdealSheafData`, `I.blowupMap` (the
  canonical glued Rees blow-up of WeilConjectures.Blowup.Gluing, defined for every ideal sheaf),
  `IsNowhereDense (I.support : Set S)` (Mathlib `support` is the vanishing locus of I). Correct.
* p is a modification — `IsModification I.blowupMap` (def-trf-orgogozo-induction-data; its
  `[IsLocallyNoetherian S] [CompactSpace S]` follow from `IsNoetherian S`). Correct.
* an F-scheme G with an F-morphism G → F' — `∃ G gG a, a ≫ g = gG ≫ i`; since i is a monomorphism this
  is equivalent to `a ≫ gF = gG`. Correct.
* a finite surjective F-morphism G → F ×_S S' — `q : G ⟶ pullback i I.blowupMap`,
  `q ≫ pullback.fst i I.blowupMap = gG`, `IsFinite q ∧ Surjective q`. Correct.

Edge cases: S empty; F empty (unit ideal I = ⊤, empty support, G = ∅); F = S; zero-dimensional
schemes; all are covered with no extra hypothesis. Universes: one universe u throughout, G and the
ideal sheaf in the same universe as S; nothing unbound. Searches: the Mathlib IdealSheaf/blow-up
API, `Scheme.Hom` closed-image vocabulary and the project's lean/Sheaf tree hold no existing
statement. Change made: the theorem docstring now carries the node's proof step by step (Step 3,
the constructible-topology finite subcover, was missing). Statement and signature unchanged; the
per-file compile is clean.
