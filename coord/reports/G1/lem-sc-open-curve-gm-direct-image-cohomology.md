## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` states
`AlgebraicGeometry.Etale.bijective_openCurve_gm_directImage_cohomology`, with a single
`sorry` proof. No definitions, dependency modules, new nodes or corrections are needed.

Hypothesis and clause correspondence:
- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Cbar over k: `[Cbar.Over (Spec (.of k))]`.
- Connected curve (nonempty, dimension exactly one, separated and finite type):
  `[IsConnectedCurve (Cbar ↘ Spec (.of k))]`, extending the recorded `IsCurve`.
- Smooth and proper: `[Smooth (Cbar ↘ Spec (.of k))]` and
  `[IsProper (Cbar ↘ Spec (.of k))]`.
- Finite set of closed points: `(S : Finset Cbar)` and
  `(hS : ∀ p ∈ S, IsClosed ({p} : Set Cbar))`.
- C = Cbar minus S and its inclusion: `(j : C ⟶ Cbar) [IsOpenImmersion j]` and
  `(hj : Set.range j.base = (↑S : Set Cbar)ᶜ)`. An open immersion identifies C
  with the indicated open subscheme, including its restricted structure sheaf.
  This permits any isomorphic presentation of that open subscheme, without choosing
  an extra structure morphism on C.
- G_m on C's small etale site: `C.gmSheaf`, the existing sheaf of units.
- j_*G_m: `(lowerStar AddCommGrpCat.{u + 1} j).obj C.gmSheaf`.
- Every nonnegative degree q <= 2: `(q : ℕ) (hq : q ≤ 2)`.
- The NATURAL map from cohomology on Cbar to cohomology on C is explicitly
  `fun x ↦ Sheaf.H.map (adjunction.counit.app C.gmSheaf) q
  (cohomologyMap j _ q x)`. The adjunction is
  `upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j`.
  `Function.Bijective` says that this additive group homomorphism is an isomorphism;
  it does not assert merely the existence of an unrelated abstract group isomorphism.

Dependency declarations read and used:
- `def-sc-curves`: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.IsCurve` and `AlgebraicGeometry.IsConnectedCurve` (full
  signatures and docstrings read). The latter includes the nonempty and
  dimension-one clauses of the dependency node, which its primary record alone
  does not express; this is an existing declaration, not a new definition.
- `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar` and `upperStarLowerStarAdjunction`.
- `def-sc-gm-torsor`: its additional recorded declaration
  `AlgebraicGeometry.Scheme.gmSheaf`, actually defined in
  `WeilConjectures.AlgebraicGeometry.Sites.Gm` (the primary Torsor module's
  generic torsor signature/docstring was also read).
- `def-weil-pbc-etale-cohomology`: read `Etale.cohomology` and
  `Etale.rightDerivedGlobalSections` in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
  Its lean.note explicitly records the source's `CategoryTheory.Sheaf.H F q`
  encoding for curve statements and the stage-3 identification with
  `(Etale.cohomology _ T q).obj ((DerivedCategory.singleFunctor _ 0).obj F)`.
  This statement uses that established Ext encoding, also used by the existing
  canonical `Etale.cohomologyMap`, rather than redefining cohomology or the map.
  Mathlib `CategoryTheory.Sites.SheafCohomology.Basic` defines `Sheaf.H` as
  Ext from the constant integer sheaf and `Sheaf.H.map` on coefficient maps.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion`
  in `Mathlib.AlgebraicGeometry.OpenImmersion`, the recorded mathlib_match.
- Additional map API: `Etale.cohomologyMap` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.
  The full statement/docstring of `Etale.map_counit_cohomologyMap` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap` identifies the
  displayed composite with the Leray edge map. Its injectivity lemmas do not
  give the item's bijectivity statement, so this is not an existing match.

Edge cases checked before writing: S may be empty (j then identifies the full
curve); q = 0 is included, as are q = 1 and q = 2; no positive-degree assumption
or nonempty-boundary assumption is added. Empty Cbar and zero-dimensional
connected schemes are excluded by the dependency's connected-curve definition,
not by new hypotheses. No restriction on the field characteristic is made.
A finite collection of closed points has closed union, hence an open complement.
The image/complement equality does not require a choice of decidable equality
on the entire point space. All universes/variables are explicitly bound.

Sources: local Stacks TeX is not present on this machine; read the authoritative
[Stacks Section 59.68](https://stacks.math.columbia.edu/tag/03RH), especially
Lemma 59.68.2's strict-henselization stalk computation and Lemma 59.68.3's Leray
argument, and [Tag 03RM](https://stacks.math.columbia.edu/tag/03RM).
The section uses the generic-point immersion; the node applies its local
stalk argument to the finite open complement, as its proof explicitly states.
No counterexample or statement fault was found. The theorem docstring carries
both DAG proof steps with their helper-node IDs.

Searches (2026-10-11):
- msearch leanfinder: "open immersion curve direct image multiplicative group
  etale cohomology comparison": eight open-immersion section-map hits, none
  giving this statement.
- msearch loogle: "CategoryTheory.Sheaf.H, IsIso": zero hits; unknown identifier
  IsIso in the search service.
- msearch grep: "Leray|cohomology.*lowerStar|lowerStar.*cohomology" in
  CategoryTheory: zero hits.
- msearch leansearch: "Leray edge map cohomology direct image sheaf": service
  unavailable (Internal Server Error), not a mathematical no-match verdict.
- rg on source WeilConjectures: `gmSheaf`, `cohomologyMap`, `map_counit`,
  `Leray`, and `lowerStar`: found the existing sheaf, comparison and counit APIs
  above; found only general injectivity or clopen-comparison lemmas, not this
  open-curve G_m bijectivity statement.
- rg for the exact item ID in source WeilConjectures: no match.
- rg in lean/Sheaf for `gm.*[Cc]ohom|[Cc]ohom.*gm|directImage|cohomologyMap`
  and `gmSheaf.*[Bb]ijective|[Bb]ijective.*gmSheaf|open.*edgeMap|edgeMap.*open`:
  no declaration of the item; generic direct-image material is unrelated.

Validation: scompile on the server succeeded in 2.2 seconds, with no warnings
or errors. The final delivery dry run is recorded by deliver2.py.

## Second reading by G1

I independently read the node statement, its Stacks source place (Section 59.68,
discussion preceding Tag 03RM), and the Lean declaration.

Object and hypothesis correspondence:

- The algebraically closed base field is rendered by `{k : Type u} [Field k]
  [IsAlgClosed k]`.
- The proper smooth connected curve is `Cbar : Scheme.{u}` with
  `[Cbar.Over (Spec (.of k))]`, `[IsConnectedCurve (Cbar ↘ Spec (.of k))]`,
  `[Smooth (Cbar ↘ Spec (.of k))]`, and `[IsProper (Cbar ↘ Spec (.of k))]`.
  `IsConnectedCurve` supplies the source's connected, separated finite-type,
  one-dimensional curve conditions.
- The finite set of closed points is `(S : Finset Cbar)` with
  `hS : ∀ p ∈ S, IsClosed ({p} : Set Cbar)`.
- The open complement and its inclusion are rendered by
  `(j : C ⟶ Cbar) [IsOpenImmersion j]` and
  `hj : Set.range j.base = (↑S : Set Cbar)ᶜ`; this identifies C with the
  complement, including its induced scheme structure, without an extra map.
- The coefficient sheaf is the existing `C.gmSheaf`, and its direct image is
  `((lowerStar AddCommGrpCat.{u + 1} j).obj C.gmSheaf)`.
- The quantified degree is `(q : ℕ) (hq : q ≤ 2)`.

The conclusion is exactly the node's natural comparison map: Lean maps
`x : Sheaf.H ((lowerStar ... j).obj C.gmSheaf) q` by
`cohomologyMap j _ q`, then applies `Sheaf.H.map` to the counit of
`upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j`; `Function.Bijective`
expresses that this map is an isomorphism. Quantifier order and all three
low degrees are unchanged.

Edge cases checked: `S = ∅` is allowed; q = 0, 1, and 2 are included; no
characteristic or nonempty-boundary assumption is present; connected-curve
hypotheses exclude empty and zero-dimensional cases exactly as the dependency
does; all universes are tied to the scheme and coefficient category.

Searches were repeated with LeanFinder (`open immersion curve direct image
multiplicative group etale cohomology`), Loogle (`CategoryTheory.Sheaf.H,
IsIso`), LeanSearch (service unavailable), and repository/Mathlib `rg` searches
for `gmSheaf`, `cohomologyMap`, `lowerStar`, `Leray`, and direct-image
cohomology. They found only generic APIs and unrelated comparison theorems;
no declaration states this result. The existing declarations used by the file
were checked against their dependency nodes.

No mismatch was found. The worker module already renders every object,
hypothesis, and conclusion of the node, has no hollow definitions or extra
assumptions, and compiled cleanly with `scompile.py`. No source, node, or Lean
changes were required in this second reading.
