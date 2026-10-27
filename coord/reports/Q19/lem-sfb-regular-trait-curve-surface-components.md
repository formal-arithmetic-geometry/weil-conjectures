## Worker report

The module `Sheaf.AlgebraicGeometry.RegularTraitCurveSurfaceComponents` states
`AlgebraicGeometry.regular_trait_curve_surface_components`. Its only theorem has proof
`sorry`; it introduces no definitions. The node is unchanged except for its `lean` record.

Hypothesis and conclusion correspondence:

- The DVR is `R : Type u` with `[CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The specified uniformizer is `π : R` with
  `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`. Nonzeroness follows from the DVR
  condition and is therefore not an extra hypothesis.
- The base `S` is exactly `Spec (.of R)`, and the structural morphism is
  `g : T ⟶ Spec (.of R)`. The fraction and residue fields named in the prose are represented
  intrinsically: `g.fiber (genericPoint (Spec (.of R)))` and
  `g.fiber (IsLocalRing.closedPoint R)`. The residue field at the generic point of a DVR's
  spectrum is its fraction field, and that at its closed point is its residue field.
  No separately chosen field or compatibility data are needed by the statement.
- Properness and flatness are `[IsProper g]` and `[Flat g]`.
- Noetherianity is `[IsNoetherian T]`, which extends both `IsLocallyNoetherian T` and
  `CompactSpace T`. Regularity is `hregular : IsRegularScheme T`, the dependency's exact
  locally Noetherian plus regular-stalk predicate, not a private affine or stalk predicate.
- Reducedness of the special fibre is `[IsReduced (g.fiber (IsLocalRing.closedPoint R))]`.
- `hdim` asserts `ringKrullDim (T.presheaf.stalk x) ≤ 2` for every ambient point.
  `hclosed` quantifies over every special-fibre point, assumes its singleton is closed in
  that fibre, and asserts dimension two for the ambient stalk at its image under `fiberι`.
  Closedness is taken in the fibre, exactly as in the node.
- `∃ (n : ℕ) (U : Fin n → T.Opens)` gives a finite family of actual open subschemes.
  `IsClosed (U i : Set T)` makes them clopen; the next clause makes distinct members
  disjoint; `(⨆ i, U i) = ⊤` makes them cover. These are a finite disjoint open-subscheme
  decomposition, so their canonical inclusions identify their disjoint union with `T`.
- Each piece satisfies `IsIntegral (U i).toScheme`, `IsRegularScheme (U i).toScheme`,
  and `topologicalKrullDim (U i).toScheme = 2`. Integral includes nonemptiness.
  The two existential point clauses say that the images of the generic and special fibre
  projections each meet `U i`. No fibre is silently required to be connected.
- `Z ∈ irreducibleComponents (g.fiber ...)` and `IsGenericPoint ξ Z` quantify over exactly
  the generic points in the node. Their ambient point is `g.fiberι ... ξ`.
- `∃ hdomain : IsDomain (...)` followed by `@IsDiscreteValuationRing ... inferInstance
  hdomain` asserts the ambient stalk is a DVR, including the domain requirement which
  Mathlib makes a parameter to the DVR class.
- The actual ring map `R → 𝒪_{T,x}` is `(Spec.preimage (T.fromSpecStalk x ≫ g)).hom`.
  Full faithfulness of `Spec` makes this the structural map on germs. Its value at `π`
  is asserted nonzero and its singleton span is asserted equal to the maximal ideal.
- `∃ e : (𝒪_{T,x} ⧸ Ideal.span {image π}) ≃+* (g.fiber ...).residueField ξ` renders the
  final quotient identification. The equation on every element `a` says its class goes
  to the fibre-projection stalk image followed by the fibre's residue map. Thus this is
  the canonical identification, not an arbitrary abstract isomorphism of fields.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and the
  uniformizer convention `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`, and
  `Scheme.ΓSpecIso`; full faithfulness of `Spec` supplies `Spec.preimage`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, whose documented
  stalkwise equivalent is `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, using
  `AlgebraicGeometry.IsRegular` from `WeilConjectures.AlgebraicGeometry.Regular`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and `Scheme.Hom.fiberι`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, `IsIntegral`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`.
  Its imported `Mathlib.AlgebraicGeometry.Stalk` supplies the canonical `Scheme.fromSpecStalk`.

The modules of all stated proof dependencies are imported with ordinary `import`:
`RegularNormalDecomposition`, `OpenImmersion`, `RationalFunctionsGenericStalks`,
`Flat.TorsionFree`, `Separation.Basic`, `Dimension`, `Spectrum.Prime.Topology`,
`AffineScheme`, `KrullDimension.Zero`, `FibreStalkQuotient`, and the upstream DVR `TFAE`.
The docstring follows all five proof steps and names the nodes supplying the respective
normal decomposition, torsion-freeness, dimension comparison, field stalk, and DVR arguments.

Edge cases checked before writing:

- The empty scheme is allowed: no nonemptiness binder, the component family may have
  `n = 0`, its supremum is the empty open and hence the top open of the empty scheme, and
  all fibre-point clauses are vacuous. For a nonempty scheme the cover forces `n > 0`;
  each piece is nonempty because it is integral.
- Disconnected families and disconnected special fibres are allowed. No component is
  required to be geometrically integral, nodal, or projective.
- The dimension bound alone does not force dimension two: the closed special-fibre
  dimension hypothesis is retained. For example `Spec R → Spec R` is excluded by it.
- A field is excluded as the base by the DVR class, so generic and closed points have the
  intended distinct meanings. The uniformizer cannot be zero in a DVR.
- At a vertical generic point reducedness makes the fibre stalk a field; ambient
  flatness prevents the uniformizer image from being zero. Dropping either assumption
  would invalidate the corresponding asserted clause; neither is dropped.
- `u` is explicitly bound and shared by `R` and `T`; scheme fibres stay in that universe.
  Both automatic-implicit options are disabled. There are no unrelated test universes.

Searches made on 2026-10-24:

- `msearch.py`, LeanFinder: "A proper regular flat scheme over a DVR with reduced special
  fibre decomposes into clopen integral regular surfaces and has DVR stalks at the generic
  points of its special fibre". Eight hits, including `WeierstrassCurve.IsGoodReduction`,
  `IsIntegral`, `IsReduced`, `Flat`, `IsSmoothOfRelativeDimension`, and valuative-square
  constructions. None state this combined trait result.
- `msearch.py`, Loogle: `IsRegularLocalRing, IsDiscreteValuationRing`. Zero hits.
- `msearch.py`, LeanSearch: "Proper flat regular trait schemes reduced special fibre
  integral clopen components and vertical DVR stalks". Eight hits: reducedness and flat
  stalk tests, integral-scheme instances, and proper restriction. None is this theorem.
- `msearch.py`, grep: `IsRegularScheme|IsRegularLocalRing|IsDiscreteValuationRing`, restricted
  to Mathlib `AlgebraicGeometry`. Seven hits in elliptic-curve reduction/L-functions and
  `OrderOfVanishing`; they use DVRs rather than establish this conclusion.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`: component/regular and vertical-DVR
  patterns, the complete node id, and the proposed declaration name. No existing exact
  theorem. The related `NodalTraitRegularization` has stronger nodal/projective input,
  and its conclusion lacks this lemma's meeting-fibres, uniformizer, and quotient clauses.
  `RegularNormalDecomposition` supplies only the first proof step, not the trait claims.
  The proposed name also has no entry in `dag/lean_names_upstream.json`.

Sources opened: local Stacks `properties.tex`, `lemma-normal-Noetherian` (033M) and
`lemma-dimension` (04MU); `algebra.tex`, `lemma-characterize-dvr` (00PD), including
condition (4). The statement is the assembly described in the node, not a changed unit
statement. No new nodes, dependency repairs, statement corrections, or disputes are needed.

Validation: `scompile.py Q19 lem-sfb-regular-trait-curve-surface-components` compiled the
delivered module in both sandbox and library modes, each in 2.2 seconds, with no errors
or unexpected warnings. `deliver2.py --no-push` then passed the server preflight and
per-file compilation (`OK (dry run)`, commit `078fb01682c`).

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
