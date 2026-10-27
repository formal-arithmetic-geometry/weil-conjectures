## Worker report

The delivery states `AlgebraicGeometry.exists_hilbert_chart_gluing_projectivity` in
`Sheaf.AlgebraicGeometry.HilbertChartGluingProjectivity`. There is exactly one theorem,
with `sorry` as its whole proof, and no new definitions. Only the item's `lean` field
changes. The theorem docstring carries all thirteen steps of the accepted proof.

Source read: Grothendieck, Bourbaki Expose 221, primary PDF
https://www.numdam.org/article/SB_1960-1961__6__249_0.pdf, proof of Theorem 3.2,
printed pp.260--265 (PDF pages 12--17), especially the finite-type immersion before
Lemma 3.7 and properness/projectivity immediately afterwards. The Hilbert specialization
is on printed p.265. Also read the current blueprint unit's `_section.md` in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
The item's more explicit ideal-descent and all-test-scheme formulation is preserved.

Hypothesis and clause correspondence:

- Noetherian base S: `S : Scheme.{u}`, `[IsLocallyNoetherian S]`, `[CompactSpace S]`.
  These are exactly locally Noetherian and quasi-compact; S need not be separated.
- The nonnegative dimension is `n : ℕ`. The closed embedding is
  `i : E.left ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)` with `[IsClosedImmersion i]`.
  `E : Over S` and `hi` assert that this is the specified embedding over S.
- A numerical polynomial is `P : NumericalHilbertPolynomial`, the recorded rational
  polynomial with integer values on every integer, including zero and unrealizable P.
- `F : Subfunctor (properHilbertPresheaf E.hom)` and the exact iff `hF` identify F
  with the constant-P locus: membership is precisely
  `HasProjectiveFibreHilbertPolynomial E.hom i T I.1 P.1` for every T and every proper
  flat finitely presented family I. F is not an arbitrary presheaf, and there is no
  arbitrary pullback map. `Subfunctor.toFunctor` inherits the existing ideal-comap maps.
  The exact iff uniquely determines its sets; all restriction maps are inherited.
  Every closed family in E_T is automatically proper over T, since E is closed in
  projective space. Thus use of the proper Hilbert presheaf adds no hypothesis and
  excludes no family. Properness supplies quasi-compactness/quasi-separatedness, so
  its `LocallyOfFinitePresentation` is exactly finite presentation here. The recorded
  fibre-polynomial definition uses residue fibres; its docstring identifies this with
  the geometric-fibre polynomial, invariant under residue-field extension.
- The ambient target is `G : Over S`, `[IsHProjective G.hom]`, with the recorded
  finite-projective-space convention, not a different projectivity predicate.
- For EVERY affine open `U : S.affineOpens`, `YU U : Over U.1.toScheme` is the chart.
  `jU U : (Over.map U.1.ι).obj (YU U) ⟶ G` is its composite into G. Its canonical
  adjoint `(Over.mapPullbackAdj U.1.ι).homEquiv (YU U) G (jU U)` is the original
  U-morphism into G_U. `hU` requires exactly that adjoint to be an immersion,
  locally of finite type and quasi-compact. Thus this is finite type INTO G_U.
- `eU U` is `RepresentableBy (YU U)` for the restriction
  `(Over.map U.1.ι).op ⋙ F.toFunctor`. Its `homEquiv` and `homEquiv_comp` supply the
  natural representing bijections for ALL U-schemes, without Noetherian restrictions.
- Agreement on every common open restriction is `hcompat`. Any two presentations T
  over U and T' over V identified over S by a have the same induced map to G, after
  contravariant transport by `F.toFunctor.map a.hom.op`. Because U and V are open
  subobjects of S, this tests exactly the functor on their overlap. Conversely an
  arbitrary scheme over U intersect V provides this test with identity underlying
  isomorphism. Naturality handles every other presentation. Neither intersections
  nor test schemes are assumed affine, and no chosen gluing map is assumed.
- The returned `Y : Over S` and `e : F.toFunctor.RepresentableBy Y` give the global
  natural representing bijections; `j : Y ⟶ G` is an S-map.
- `κ U` with `IsPullback (κ U).left (YU U).hom Y.hom U.1.ι` provides the canonical
  isomorphism YU with Y times_S U. The equation `κ U ≫ j = jU U` says its restriction
  is the given immersion. The following equation for every T and g says that these
  identifications preserve the GIVEN local representing bijections. The next clause
  proves uniqueness of any chart arrow a preserving them; together with the pullback
  square, this is precisely uniqueness of the representing chart isomorphisms.
- `((eU U).homEquiv (𝟙 (YU U))).1.1` is the actual chart universal ideal. The first
  ideal clause identifies it with `comap (baseChangeMap E.hom (κ U))` of the global
  identity family's ideal. The next clause states uniqueness of the global ideal
  with those restrictions, among ALL quasi-coherent ideals. Thus the local ideals
  actually glue, not merely their abstract source schemes. The clause for all T and g
  says every represented family is the ideal pullback of the identity family. That
  family belongs to F, hence is flat, finitely presented and has polynomial P.
- BEFORE the DVR hypothesis, the returned data already satisfy `IsImmersion j.left`,
  `LocallyOfFiniteType j.left`, `QuasiCompact j.left`. Finite type of Y over S is
  also recorded at this point. The final conditional conclusion is deliberately
  inside the existential: the SAME Y, j, representation and ideals have already been
  obtained without invoking the DVR assumption. This spells out the node's last clause.
- The condition in that final implication quantifies over every `R : Type u` with
  `CommRing`, `IsDomain`, `IsDiscreteValuationRing`, every `K : Type u` with `Field`,
  `Algebra R K`, `IsFractionRing R K`, and every `b : Spec (.of R) ⟶ S`. It requires
  `Function.Bijective` of F's map along the over-S arrow induced by
  `Spec.map (CommRingCat.ofHom (algebraMap R K))`. Domain is F(Spec R), codomain is
  F(Spec K) with structure map generic inclusion followed by b. There is no DVR
  finite-type or dominance condition. The explicit `rfl` in `Over.homMk` merely
  supplies the commuting triangle defining this canonical over-category arrow.
- Given DVR bijectivity, the final conjunction states `IsClosedImmersion j.left`,
  `IsHProjective Y.hom`, `IsProper Y.hom`, `IsSeparated Y.hom`, and finite type
  as `LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom`.
- There is no assumption `Flat E.hom`, and no flatness of the ambient space occurs
  anywhere in the signature. The arbitrary all-test-scheme and DVR quantifiers use
  universe u, the same scheme-size convention as the recorded dependency interfaces;
  no independent smaller test universe is introduced.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; quasi-compactness of S is `CompactSpace S`.
- `def-sfb-projective-fibre-hilbert-polynomial`:
  `Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial`,
  `AlgebraicGeometry.NumericalHilbertPolynomial` and
  `AlgebraicGeometry.HasProjectiveFibreHilbertPolynomial`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective` (the upstream definition, not the retired duplicate).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, with `QuasiCompact` from the recorded
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` interface.
- `def-pc-representable-functor`: `Mathlib.CategoryTheory.Yoneda`,
  `CategoryTheory.Functor.RepresentableBy` (the data form of `IsRepresentable`).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, with `IsSeparated` from its Separated import.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, and its recorded immersion specialization
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `AlgebraicGeometry.IsImmersion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, together with the universal-property predicate
  `IsPullback`, and the standard `Over.pullback`/`Over.mapPullbackAdj` interface.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`, in the proper-family predicate.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, in that same predicate.
- `def-sfb-proper-hilbert-presheaf`: `Sheaf.AlgebraicGeometry.ProperHilbertPresheaf`,
  `AlgebraicGeometry.IsProperHilbertFamily` and `AlgebraicGeometry.properHilbertPresheaf`.
- `def-sc-discrete-valuation-ring`: its mathlib_match, `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (no lean record required).
- `def-weil-field`: its mathlib_match `Field`, `Mathlib.Algebra.Field.Defs`.

Already stated proof dependencies are imported without `public`: the DVR criterion,
projective-implies-proper, closed-immersion products, relative gluing, scheme gluing and
the pointwise ring-hom criterion. Remaining Mathlib-leaf proof dependencies are supplied
by these imports and the statement imports (Yoneda, Noetherian, immersion, properness,
flatness, finite presentation, ideal sheaves and base change). The proof-only structural
locality node has no recorded declaration, so no module is invented for that proof
prerequisite in this statement-only delivery.

Edge cases checked before and after writing: empty S; empty test scheme T (one empty
family for every P, since the fibre condition is vacuous); empty Hilbert component on
nonempty tests; zero polynomial and the empty family; unrealizable numerical polynomial;
n=0; nonseparated Noetherian S; non-Noetherian and non-quasi-compact test schemes; nonflat
ambient E/S; all characteristics. No positivity, dimension, nonemptiness or genus
hypothesis is inserted. For an empty S, the affine-open indexing and the ideal restriction
uniqueness remain meaningful. Testing on arbitrary overlaps avoids the false assumption
that intersections of affine opens in an arbitrary Noetherian scheme are affine.

Searches for the complete statement (all through prescribed msearch.py):

- LeanFinder: `Glue affine local representing Hilbert schemes and finite type immersions,
  use DVR bijectivity to obtain a projective representing scheme`. Eight hits: generic
  Proj, valuative criterion and scheme gluing/relative gluing. No combined statement.
- LeanSearch: `Hilbert functor affine charts gluing projective scheme DVR valuative
  criterion`. Eight hits: general valuative criterion definitions and properness API.
  No theorem about representing Hilbert charts and universal ideals.
- Loogle: `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.IsProper`. Zero hits.
- Mathlib grep: `Hilbert|hilbert|relativeGluing`, subdirectory AlgebraicGeometry.
  Twenty hits, chiefly RelativeGluing and SmallAffineZariski; no Hilbert-chart theorem.
- Project/source rg: `Hilbert|hilbert`, `HasProjectiveFibreHilbertPolynomial`,
  `polynomialHilbert|projectiveHilbert|hilbertPolynomialPresheaf`,
  `ChartGluing|chart_gluing|hilbert_chart`; inspected the existing proper-Hilbert,
  fibre-polynomial and projective-Hilbert-representability modules. The latter is the
  parent theorem; it does not state this conditional chart-gluing lemma. Other chart
  matches concern Proj module sheaves or projective bundles, not Hilbert charts.
- Exact item-id search in `lean/WeilConjectures`: no match. DAG concept search in
  `dag/nodes/sec-six-functors-basics` found the existing Hilbert definitions used here.

No new nodes, dependency interface repairs, statement correction or STATEMENT-DISPUTED
finding is needed. The extensional subfunctor presentation uses existing Mathlib notions
and fully pins both the family set and its maps; it introduces no new notion to define.

## Second reading by Q09

I reopened the node and the written signature and checked each clause in the correspondence
above. This is a second pass by the assigned worker; the independent review is the
maintainer's delivery review, as specified in the dispatch brief (no other agents started).
The first compile exposed a ring-category constructor shorthand and the incorrect `Y`
named argument to `Over.homMk`; these were replaced by explicit `CommRingCat.ofHom` and
explicit source/target `U`/`V` objects. No mathematical change was needed.

The second pass specifically checked the direction of F's DVR map and of the map in the
overlap condition; the finite-type requirement is on the adjoint chart map INTO G_U;
the returned pullback squares plus representation compatibility imply the requested
unique isomorphisms; the ideal restrictions use canonical `baseChangeMap` and actual
ideal `comap`; and the DVR condition occurs only after all pre-DVR conclusions. The
subfunctor's exact membership iff excludes extra or missing families. The data and
conclusions match the node without changing its statement or dependencies.

Validation: `scompile.py Q09 lem-sfb-hilbert-chart-gluing-projectivity` passed for the
complete delivered file, both its sandbox check and its library-module check, with no
compiler errors or warnings. `deliver2.py ... --no-push` printed
`OK (dry run): commit b3ecbc484b9 passes the preflight and compiles; nothing pushed`.
Local consistency inspection confirms only `lean` changes in the node, the recorded
49-line signature is verbatim from the file, there is one `sorry`, and the maximum Lean
line width is 91. The wrapper reported shared compile waiting; the per-file 60-second
compiler limit was unchanged. There was no timeout and no bypass of any gate.
