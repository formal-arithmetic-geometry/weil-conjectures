## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveCoordinateBoundary` states
`AlgebraicGeometry.exists_isFinite_projective_coordinate_boundary`, with one `sorry`
and no new definitions. The node's statement is unchanged. No faults or statement disputes
were found. The source is the complete blueprint lemma and its five-step DAG proof.

Hypotheses, clause by clause:

- `A : Type u`, `[CommRing A]` and `Spec (CommRingCat.of A)` give the affine base S.
  `[IsIntegral (Spec (CommRingCat.of A))]` is exactly the integral-scheme hypothesis,
  including nonemptiness, rather than an extra domain assumption.
  `[IsNoetherianRing A]` gives the Noetherian affine base.
- `Y : Scheme.{u}`, `f : Y ⟶ Spec (CommRingCat.of A)`, and `[IsProjective f]`
  give the projective morphism with the canonical upstream H-projective convention.
- `ι : Type v`, `[Finite ι]`, and `U : ι → Y.affineOpens` give a finite family of affine
  open subschemes. `hcover : (⨆ i, (U i).1) = ⊤` is exactly the covering condition.
  No nonempty index or nonempty chart assumption is imposed.
- `m : ι → ℕ` and `hm : ∀ i, 1 ≤ m i` render the positive chart dimensions.
- `e i : (U i).1.toScheme ⟶ AffineSpace (ULift.{u} (Fin (m i))) S`,
  `[he : ∀ i, IsClosedImmersion (e i)]`, and `hover` render the closed S-immersions:
  `e i` followed by affine-space projection is chart inclusion followed by f.
- The rth coordinate projection is the existing `AffineSpace.reindex` for the function
  from the singleton coordinate type `ULift (Fin 1)` constantly equal to `ULift.up r`.
  Thus `e i ≫ AffineSpace.reindex ... S` is exactly t_{ir}, not an arbitrary chosen map.
- `V i r` is an open in `AffineSpace (ULift (Fin 1)) S`; `hV` states its density
  in that entire affine line, not merely in the chart image.

Conclusion, clause by clause:

- `∃ a : A, Nonempty (PrimeSpectrum.basicOpen a) ∧ ...` provides a nonempty principal
  open D(a). `Scheme.Opens.ι (X := Spec (CommRingCat.of A)) (PrimeSpectrum.basicOpen a)`
  is its canonical open immersion into S.
- The ambient scheme is `pullback f` of this inclusion, namely Y ×_S D(a).
- `T : TopologicalSpace.Closeds ...` and its carrier equality specify precisely the
  complement of the restricted union. The negated existential says that there are no
  chart i, coordinate r, and chart point y mapping to the point's projection in Y
  with t_{ir}(y) in V_{ir}. This is the pullback of the complement of the union of the
  images of the coordinate inverse opens. Chart inclusions are injective, so this also
  agrees with computing coordinate inverse images inside each restricted chart.
  The existential T only packages this specified closed set; it supplies no arbitrary
  replacement for the canonical reduced scheme.
- `(Scheme.IdealSheafData.vanishingIdeal T).subschemeι` is the reduced induced closed
  subscheme inclusion from the dependency. Its composite with `pullback.snd` is the
  canonical map to D(a). `IsFinite` of exactly that composite states the requested finiteness.
  In particular, no reduction of an arbitrary chosen closed subscheme is substituted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, whose fields
  are nonemptiness and domain section rings on nonempty opens.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsProjective` and its parent `IsHProjective`; read the published
  source with `scompile.py --source`, since that extracted module is absent locally.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (available through the public imports).
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`, its structural
  projection, and `AlgebraicGeometry.AffineSpace.reindex`. Read `coord`, `homOfVector`,
  `reindex`, and `reindex_appTop_coord`: the reindex function pulls back the unique
  target coordinate to the specified source coordinate.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`; the conclusion
  uses its `vanishingIdeal`, `subscheme`, and `subschemeι` construction. Read its complete
  signature, docstring, and the vanishing-ideal construction in Mathlib.
- `def-weil-pbc-scheme-conventions` fixes no declaration; the recorded note identifies
  the morphism conventions, including `AlgebraicGeometry.IsFinite` from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- Proof imports retain `Sheaf.AlgebraicGeometry.ProjectiveFiniteGeometricFibres`
  (`isFinite_of_isProjective_of_finite_geometricFibres`),
  `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange` (`projective_base_change`),
  `Mathlib.RingTheory.Localization.Away.Basic` (the localization-away interface), and
  `Mathlib.RingTheory.QuasiFinite.Basic` (finite-algebra finite discrete spectrum).
  The other stated proof dependencies are already reached through the public imports.

Edge cases checked before writing:

- The integral hypothesis excludes the zero base and the empty base scheme as intended.
- Y can be empty, charts can be empty, and the finite cover can have an empty index type
  when Y is empty. No `Nonempty ι` is added; the empty product of coefficients is 1.
- Dimensions are at least 1 exactly as stated; no extra dimension restrictions are added.
- A chosen V can be the whole affine line; its closed complement is empty and the proof
  chooses the polynomial 1. Degree-zero polynomials and zero chart quotient rings are
  included, so empty reduced complements and empty fibres remain allowed.
- Over a field any nonzero a gives the full base; for a general integral base the conclusion
  permits a proper nonempty principal shrink. No geometric reducedness assumption is added.
- `u` is arbitrary for the ring and schemes, `v` is arbitrary for the finite chart index,
  and `ULift.{u}` puts finite coordinate types into the scheme's universe.

Searches for an existing statement (2026-10-15):

- `msearch.py`, leanfinder: "A projective scheme has finite reduced complement of dense
  affine coordinate opens after shrinking an integral affine base". Eight hits concern
  `Proj`, its affine covers, finite type and properness. None states this shrinking lemma.
- `msearch.py`, loogle: "AlgebraicGeometry.AffineSpace.map, AlgebraicGeometry.IsFinite".
  Zero hits; no matching theorem.
- `msearch.py`, leansearch: "Projective coordinate complement finite after shrinking an
  integral affine base". Service unavailable (Internal Server Error); recorded as unavailable.
- `msearch.py`, grep: "coordinate.*boundary|boundary.*coordinate|finite.*of.*projective".
  The 25 returned hits concern projective objects, measures and unrelated finite constructions;
  none matches the statement.
- `rg` on upstream WeilConjectures and project `lean/Sheaf` with the same coordinate-boundary
  patterns found unrelated Kummer boundaries, cocycle boundaries and a downstream generic-open
  argument, not an existing coordinate-complement finiteness theorem. Searching the exact
  blueprint id and proposed declaration in the upstream-name index and both source trees
  found no declaration. Direct reading of Mathlib AffineSpace found the canonical `reindex`
  projection, so no helper notion or duplicate coordinate definition is needed.

Validation: `scompile.py ND lem-fin-projective-coordinate-boundary` compiled the module cleanly
under the default file limit. Explicit `Scheme.{u}` annotations resolve category inference in
closed-set and set carrier types. Every universe and variable is bound (`autoImplicit false`).
The only proof is `sorry`; the docstring carries all five proof steps from the DAG.


## Second reading by ND

Read the complete node, its five proof steps, the original blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/lem-fin-projective-coordinate-boundary.md`, and
all seven statement dependency records. The source is a standalone blueprint lemma,
not a Stacks lemma with additional standing assumptions. Also read Stacks schemes.tex
Lemma 01J3 and Definition 01J4 (reduced closed subschemes), morphisms.tex Definition
01W8 and Lemma 01WF (H-projectivity and its base change). The blueprint explicitly
uses the DAG's H-projective convention, as the Lean does.

Object/hypothesis/conclusion inventory and correspondence:

1. Integral Noetherian affine base S = Spec A: `(A : Type u) [CommRing A]`,
   `[IsNoetherianRing A]`, `[IsIntegral (Spec (CommRingCat.of A))]`. PASS.
   Read Mathlib's actual IsIntegral fields (nonempty and domain sections), and
   IsNoetherianRing / isNoetherianRing_iff_ideal_fg; these give the node's notions.
2. Projective Y over S: `{Y : Scheme.{u}}`, `f : Y ⟶ Spec ...`, `[IsProjective f]`.
   PASS. Read the published canonical Projective module with `scompile.py --source`:
   IsProjective extends IsHProjective and QuasiCompact, and IsHProjective is a finite
   projective-space closed embedding over the base. No field or smoothness assumption.
3. Finite affine open cover: `(ι : Type v) [Finite ι] (U : ι → Y.affineOpens)` and
   `(hcover : (⨆ i : ι, (U i).1) = ⊤)`. PASS. No disjointness, nonemptiness,
   irredundancy or selected chart is required.
4. Positive chart dimensions: `(m : ι → ℕ) (hm : ∀ i, 1 ≤ m i)`. PASS.
5. Closed S-embeddings into affine m-space: `e i` has domain `(U i).1.toScheme`
   and target `AffineSpace (ULift.{u} (Fin (m i))) (Spec ...)`; `[he : ∀ i,
   IsClosedImmersion (e i)]` and `hover` specify closedness and compatibility with f.
   PASS. Read Mathlib's IsClosedImmersion and AffineSpace / over / SpecIso signatures:
   these are precisely the closed embeddings and affine spaces in the dependency nodes.
6. Coordinate maps t_ir: the composite `e i ≫ AffineSpace.reindex
   (fun _ : ULift.{u} (Fin 1) ↦ ULift.up r) (Spec ...)`. PASS.
   Read the body `homOfVector ... (coord S ∘ i)` and reindex_appTop_coord:
   it pulls the unique line coordinate back to coordinate r. No arbitrary map replaces t.
7. Dense opens in the full affine line, one for every coordinate: dependent family `V`
   of `.Opens`, and `hV : ∀ i r, Dense (V i r : Set (AffineSpace ...))`. PASS.
8. A nonempty principal shrink: `∃ a : A, Nonempty (PrimeSpectrum.basicOpen a) ∧ ...`.
   PASS. The inclusion is exactly `Scheme.Opens.ι ... (PrimeSpectrum.basicOpen a)`;
   the shrink is chosen after all charts, embeddings and opens have been supplied.
9. Ambient restricted Y: `pullback f` of that inclusion. PASS: this is Y ×_S D(a),
   with `pullback.fst` the map to Y and `pullback.snd` the map to D(a).
10. The specified closed complement: `∃ T : TopologicalSpace.Closeds ...` with carrier
    equal to `{x | ¬ ∃ i r y, (U i).1.ι y = pullback.fst ... x ∧ t_ir y ∈ V i r}`.
    PASS. The existential describes exactly membership in the union of the images of
    coordinate inverse opens; its negation gives the complement pulled back to Y'.
    Injectivity of chart inclusion identifies this with the restricted chart formulation.
    T packages the closedness of this exact set; it is not an unconstrained replacement.
11. Reduced induced closed subscheme and finiteness over the shrink:
    `IsFinite ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ pullback.snd ...)`.
    PASS. Read the dependency's complete reduced_induced_closed_subscheme theorem,
    including residue-field vanishing, reducedness, range and uniqueness; also the real
    Mathlib vanishingIdeal and subschemeι constructions and IsFinite definition.
    This uses the canonical radical vanishing ideal and its reduced subscheme, with
    finiteness of the specified structural map, rather than an arbitrary closed scheme.

Proof-interface check: read ProjectiveFiniteGeometricFibres and ProjectiveBaseChange
signatures and docstrings. The former requires projectivity, a locally Noetherian compact
base and finite geometric fibres; the five-step proof supplies these after localization.
The latter gives projectivity of pullback.snd. Proof imports retain these modules and the
localization-away and finite-algebra-spectrum interfaces. No new dependency module or
new definition node is delivered; no missing helper notion was found.

Edge cases: an integral base is nonempty and excludes the zero ring, as intended.
Y and charts may be empty. An empty index type is allowed precisely when the covering
condition forces Y empty; the coefficient product is then 1. Dimension zero is excluded
only by the source's m_i ≥ 1, not by an added Lean restriction. The affine-space encoding
itself supports Fin 0. V may be the whole affine line; its complement and the reduced
subscheme may be empty, including zero quotient rings and constant monic polynomials.
No characteristic or geometric reducedness condition is present. Ring/scheme universe u
and independent finite-index universe v are arbitrary; ULift places finite coordinate
sets in u. The base and schemes share Mathlib's Scheme universe convention, without an
extra equality of independent universes. All binders and both universes are explicit.

Independent searches, using wording different from the first reading:

- LeanFinder: "A projective scheme with finite affine coordinate charts has finite reduced
  complement of dense coordinate opens after localization". Eight Proj/affine-cover and
  finite-type/properness hits; no coordinate-complement shrinking theorem.
- Loogle: `AlgebraicGeometry.AffineSpace.reindex`. Ten hits, including reindex,
  reindex_over and reindex_appTop_coord; confirms the existing canonical coordinate
  projection used here, with no duplicate helper definition needed.
- LeanSearch: "The reduced complement of dense coordinate opens of a projective scheme
  is finite after shrinking the base". Service returned Internal Server Error;
  recorded as unavailable, not negative evidence.
- Wrapper grep: `projective.*(complement|shrinking)|dense.*affine.*open.*finite`:
  zero hits. Direct rg over upstream WeilConjectures, project lean/Sheaf and Mathlib
  AlgebraicGeometry for `coordinate.*(complement|boundary)|dense.*coordinate` and the
  exact theorem name found unrelated boundary/coboundary material and the downstream
  GenericOpenImmersionConstructibility proof outline, not an existing equivalent theorem.

No mathematical or Lean mismatch was found. No statement correction, new node,
dependency repair, or source change is needed. Kept the worker's Lean and node unchanged;
this second-reading evidence is the only addition. The node lean.statement was checked
by exact string comparison against the source signature; lines are at most 100 characters.
There is one named theorem with whole proof `sorry`, no definitions, local notation or
private copies; module and declaration docstrings name the source and blueprint id,
and the theorem docstring carries all five DAG proof steps.

Validation after the second reading: scompile.py compiled the delivered module cleanly
in the authorized private overlay (2.2 seconds); no errors or warnings were emitted.
