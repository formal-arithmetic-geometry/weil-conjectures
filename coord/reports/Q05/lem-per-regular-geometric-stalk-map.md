## Worker report

The delivery states `AlgebraicGeometry.regular_geometric_stalk_map` in
`Sheaf.AlgebraicGeometry.RegularGeometricStalkMap`. Its only theorem proof is
`sorry`; the docstring reproduces all five proof steps of the DAG node, including
the precise flatness descent and quotient argument. No definitions, dependency
repairs, new nodes, or statement corrections are needed. The node changes only
in `lean`; its natural-language statement and accepted proof split are unchanged.

Hypothesis and clause correspondence:

- Schemes and morphism g:Y→X are `{Y X : Scheme.{u}} (g : Y ⟶ X)`.
- Local Noetherianity of both schemes is `[IsLocallyNoetherian Y]` and
  `[IsLocallyNoetherian X]`.
- Regularity is exactly `hg : IsRegularSchemeMorphism g`, the recorded definition:
  flatness and regular fibres after every finite residue-field extension. It does
  not impose local finite presentation, smoothness, or excellence.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `barY : Spec (.of Ω) ⟶ Y`. The geometric point of X is the literal composite
  `barY ≫ g`, so the two points use exactly the same Ω.
- The rings A and C are the recorded `Scheme.strictHenselizationRing (barY ≫ g)`
  and `Scheme.strictHenselizationRing barY`. These are the small affine pointed
  neighbourhood colimits, not arbitrary strictly henselian rings.
- The canonical ring map h is written without a new helper definition as
  `(Spec.preimage (Scheme.strictHenselizationMap g barY)).hom`.
  `Scheme.strictHenselizationMap` is the existing unique pointed morphism from
  functoriality. The fully faithful spectrum functor's preimage gives exactly
  its contravariant ring map. The characterizing equations of
  `Scheme.strictHenselizationMap_existsUnique` say that it lies over g and
  respects the compatible geometric-point evaluations into Ω; these are the
  prescribed residue embeddings. No arbitrary map, residue-field equivalence,
  localness hypothesis, or flatness hypothesis is supplied by the caller.
- Local-ring structures are the two existential binders in the conclusion.
  These bind the actual Prop structures used to form the maximal ideal, rather
  than requiring the caller to assume localness. There are no `let` binders.
- Noetherianity of A and C is the first and second `IsNoetherianRing` conjunct.
- Flatness of h is the `RingHom.Flat` conjunct for this canonical ring map.
- The extended ideal m_A C is
  `(IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing (barY ≫ g))).map h`.
  The final `IsRegularLocalRing` conjunct applies to C modulo that explicit ideal,
  asserting both locality and regularity of the closed fibre.
- The final sentence excluding excellence and finite type is respected by the
  absence of either assumption. There is also no separatedness, quasi-compactness,
  characteristic, finite-dimensionality, or closed-point restriction.

Recorded dependency declarations read and used:

| DAG dependency | Module and declaration |
| --- | --- |
| def-per-regular-scheme-morphism | `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`: `AlgebraicGeometry.IsRegularSchemeMorphism` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| pqf-def-locnoeth | `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian` |
| def-weil-geometric-point | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; inline geometric point as recorded; `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` explains its residue embedding |
| def-weil-pbc-strict-henselization-limit | `WeilConjectures.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing` and `Scheme.strictHenselizationScheme` |
| lem-weil-pbc-strict-henselization-functoriality | `Sheaf.Paper.StrictHenselizationFunctoriality`: `AlgebraicGeometry.strictHenselizationFunctoriality`; its already published packaging `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`: `Scheme.strictHenselizationMap_existsUnique`, `Scheme.strictHenselizationMap` |
| def-weil-pbc-flat-ring-map | `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, whose module action is induced by the actual ring map |
| def-weil-regular-scheme | `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, and the node's recorded ring clause `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` |

Statement dependencies are exposed through public imports (including their
public import closures). All already stated proof dependencies are imported,
including affine stalk localization, Noetherian localization, affine strict-local
comparison, strict-henselization Noetherianity and faithful flatness, transitivity
of flatness, `Module.flat_iff_strictHenselization`, chart maximal ideals, fibre stalk
quotients, strict-henselization quotients, and strict-henselization regularity.
The latter proof-only modules have ordinary imports. No cycles were introduced.
The existing ring maps in `SmoothGeometricStalkAlgebra` and
`StrictHenselizationTensorFinite` were read; no duplicate of those definitions is
introduced, and no smoothness or finite-map theorem is used to replace this node.

Sources opened in the supplied Stacks checkout:
`etale-cohomology.tex` Tag 04HX, `lemma-describe-etale-local-ring`;
`more-algebra.tex` Tag 06LJ, `lemma-henselization-noetherian`, Tag 06LN,
`lemma-henselization-regular`, and Tag 07QM, `lemma-dumb-properties-henselization`;
`flat.tex` Tag 05VL, `lemma-flat-up-down-henselization`;
`algebra.tex` Tag 05WS, `lemma-quotient-strict-henselization`.
They support exactly the five-step assembled proof: ordinary stalks are
Noetherian; strict henselizations remain Noetherian; flatness over the ordinary
base stalk is equivalent to flatness over its strict henselization; maximal ideals
extend as prescribed; the closed fibre is a strict henselization of the ordinary
regular local fibre ring.

Edge cases checked before writing:

- Empty Y has no geometric point, so the universally quantified theorem is
  vacuous in exactly that case; a morphism from Spec Ω to the empty scheme is
  not artificially provided. No nonemptiness of either scheme is assumed.
- For an identity morphism, the canonical map is the identity up to its unique
  pointed characterization and the quotient is the residue field, regular local.
- Over a field, the source strict local ring is its selected separable closure;
  the extended maximal ideal is zero. The conclusion reduces to regularity of
  the appropriate geometric strict local fibre, as it should.
- Nonclosed scheme points and arbitrary algebraically closed Ω are allowed.
  No rationality or algebraicity of Ω over the residue field is assumed.
- Arbitrary characteristic and nonexcellent locally Noetherian schemes are
  retained. Regular morphisms not locally of finite type are retained.
- The one common universe is the existing geometric-point/strict-henselization
  API's universe; Ω and both schemes may all be represented in a common larger
  universe. No independent test universe creates vacuous finite-field tests.
- The ring quotient is nonzero: locality of the canonical map places the
  extended maximal ideal inside the target maximal ideal. The statement does
  not claim the zero ring is regular local.

Searches actually run:

1. `msearch.py` LeanFinder, query: “For a regular morphism of locally Noetherian
   schemes, the canonical map on geometric strict local rings is flat and its
   closed fibre is regular local”. Eight hits on smoothness, including
   `AlgebraicGeometry.IsSmooth` and `IsSmoothOfRelativeDimension`; none gives this
   strict-henselization theorem for regular morphisms.
2. `msearch.py` Loogle, query: `"StrictHenselization", "Flat"`. Zero hits.
3. `msearch.py` grep, query: `strict.*hensel|hensel.*regular`, subdirectory
   `RingTheory`. Zero Mathlib hits.
4. `msearch.py` LeanSearch, query: “A regular morphism induces a flat map of
   geometric strict local rings with regular closed fibre”. Eight hits including
   `AlgebraicGeometry.Flat.stalkMap`, `RingHom.Flat`, and
   `RingHom.Flat.localRingHom`; none states the geometric strict-local conclusion.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
   `regular.*geometric.*stalk`, and `regular.*strictHensel`, followed by
   `strictHensel.*[Ff]lat|[Ff]lat.*strictHensel|regular_geometric_stalk_map`.
   The relevant project hit `smooth_geometric_stalk_algebra` requires smoothness;
   its map construction was read, but its theorem is not the regular-morphism
   statement. Other hits are strict-henselization structural flatness or
   completion flatness, not the desired closed-fibre theorem.
6. Exact-name search for `regular_geometric_stalk_map` in
   `dag/lean_names_upstream.json` and both Lean source roots returned no declaration;
   literal `grep -rn` for this item in `lean/WeilConjectures` returned no match.
7. `rg` searches for canonical map and evaluation names found the already
   published `StrictHenselizationCanonicalMap` interface and the two ring-map
   interfaces described above. They are reused through the fully faithful
   spectrum preimage; no additional definition node is necessary.

Validation: `scompile.py Q05 lem-per-regular-geometric-stalk-map` compiled this
module both in its sandbox and at its intended library module path, cleanly
(1.5 and 2.0 seconds respectively). All variables and universes are explicitly
bound and auto-implicit variables are disabled. No statement dispute or source
fault was found. The prescribed delivery dry run and push are recorded by the
delivery tool. Independent mathematical review is the maintainer's responsibility
under this dispatcher's current brief.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
