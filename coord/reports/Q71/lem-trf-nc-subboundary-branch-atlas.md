## Worker report

The module `Sheaf.TraceFormula.NCSubboundaryBranchAtlas` states
`AlgebraicGeometry.Scheme.IdealSheafData.nc_subboundary_branch_atlas`, with one
postponed theorem proof and no new definitions. The DAG statement is unchanged.

Hypotheses and clauses, in their source order:

- Regular locally Noetherian X: `_hX : IsRegularScheme X` and
  `[IsLocallyNoetherian X]`, using the recorded scheme predicate.
- B normal crossings: `_hB : B.IsNormalCrossingsDivisor`.
- D a reduced closed subscheme contained in B: `D : X.IdealSheafData`,
  `[IsReduced D.subscheme]`, and `_hDB : B ≤ D`. Ideal inclusion reverses
  subscheme inclusion. Ideal-sheaf data supplies the canonical closed subscheme,
  rather than introducing an arbitrary immersion or an extra presentation.
- The support component condition is the recorded
  `IsUnionOfIrreducibleComponents D B`, including the empty union.
- The explicit stronger neighborhood hypothesis is `_hneighborhood`. It quantifies
  over every geometric point, represented by `x` and `ι : κ(x) →+* Ω`, where
  `Ω : Type (max u v)` is an arbitrary algebraically closed field. It supplies
  a regular Noetherian V, an etale e, a point w, and a residue-field embedding
  satisfying `ιV.comp (e.residueFieldMap w).hom =
  ι.comp (X.residueFieldCongr he).hom.hom`. This is exactly the pointed lift,
  including compatibility on residue fields, not merely an underlying lift.
  At every z it requires a full regular parameter list t and a sublist a
  whose product generates the B stalk ideal on an affine open via the germ map.
- The first conclusion supplies W, e, `IsAffine W`, `Etale e`,
  `IsRegularScheme W`, and `IsNoetherian W`, and the same pointed-lift equation.
  `IsAffine W` means canonically W ≅ Spec Γ(W, ⊤) (`W.isoSpec`); thus its global
  sections are the ring A in the node's affine presentation. No affine chart
  is assumed for the entire original X.
- Parameters are `t : Fin d → Γ(W, ⊤)`. Their entire germ list at w satisfies
  `IsLocalRing.IsRegularSystemOfParameters`. `hr : r ≤ d` and `hs : s ≤ r`
  express precisely `0 ≤ s ≤ r ≤ d`, with natural-number nonnegativity intrinsic.
- `D.comap e = ofIdealTop (Ideal.span {∏ j : Fin s, ...})` and the analogous
  B equation for `Fin r` are equalities of ideal sheaf data, hence the two
  scheme-theoretic equations. They include empty products.
- The evaluations of all r displayed factors at w are explicitly zero.
- At every z, a sublist a of a full regular parameter list q contains exactly
  the vanishing displayed coordinate germs. Pairwise distinctness for distinct
  vanishing coordinate indices is stated explicitly. This is exactly the
  uniform distinct-members condition, including points where some coordinates
  are units.
- The chart branch formula is `D.ncBranchCount (e z) = Nat.card {j : Fin s //
  W.Γevaluation z (...) = 0}`; this evaluates zero in κ(z).
- For every integer k ≥ 1, the chart inverse image is the union over all
  `J : Finset (Fin s)` of cardinality k of the support of the ideal generated
  by the selected coordinates. These supports are precisely the closed
  intersections V(t_j : j ∈ J). The indexing set is finite, even though the
  union is expressed using indexed-set-union notation.
- Presentation independence: for every x and n, `D.HasNCBranchChart x n`
  implies `n = D.ncBranchCount x`. This quantifies over every presentation
  in the recorded definition, including zero-length presentations.
- Etale invariance is `(D.comap e).ncBranchCount w = D.ncBranchCount (e w)`
  for every scheme W, etale e, and w, rather than only the constructed charts.
- Each positive integer branch level is `IsClosed` in X.
- Quasi-compactness is `CompactSpace X`, the open-cover finite-subcover property.
  The final clause produces a natural-number bound for all points.

Recorded statement-dependency declarations used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.NormalCrossingsDivisor` (also publicly imported by
  NormalCrossingsBranchCount): `Scheme.IdealSheafData.IsNormalCrossingsDivisor`.
- `Sheaf.AlgebraicGeometry.UnionOfIrreducibleComponents`:
  `AlgebraicGeometry.IsUnionOfIrreducibleComponents`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount`:
  `Scheme.IdealSheafData.HasNCBranchChart`, `Scheme.IdealSheafData.ncBranchCount`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; the ideal sheaf's canonical closed
  immersion is provided by `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.

All available recorded proof-dependency modules are imported privately. The proof
node `lem-trf-parameter-product-strict-local-branches` has neither a Lean record
nor a Mathlib match, so there is no module to import for that proof-only node;
it is explicitly named in the theorem's complete seven-step proof docstring.
The proof-only Mathlib matches are imported from OpenImmersion, Etale, Flat,
Spectrum.Prime.Topology, Ideal.GoingDown, and Morphisms.UniversallyOpen.

Sources read: ILO VIII 4.1.2 and 4.1.6--4.1.8, printed pp.117--118, in the
local PDF; Stacks etale.tex `definition-normal-crossings` (0BSF) and
`definition-strict-normal-crossings` (0BI9), including the adjacent component
criterion; current blueprint `lem-trf-local-term-locality.md`.

Edge cases checked before writing: X empty permits bound zero and vacuous atlas;
D empty and s=0 give the unit ideal and zero branch count; B empty permits r=s=0;
a zero-dimensional regular stalk permits d=r=s=0; k>s gives an empty union; a
coordinate that is a unit at a different chart point is omitted from its local
parameter sublist. No nonemptiness or positive dimension hypothesis is added.
The geometric field universe `max u v` includes fields of the scheme's universe
and arbitrary larger universes; there is no equality of site universes imposed.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: "Simultaneous normal crossings subboundary affine etale parameter
  charts, geometric branch count, closed branch count levels and boundedness on
  a quasi compact scheme". Eight hits: Scheme.Etale, normalizationOpenCover,
  ExistsHomHomCompEqCompAux.range_g_subset, IsEtale, IsSmoothOfRelativeDimension,
  Scheme.Hom.toNormalization, Algebra.IsStandardSmoothOfRelativeDimension.
  exists_etale_mvPolynomial, and Scheme.Hom.isOpenMap-related affine-limit
  result. These are etale/normalization tools, not the present theorem.
- Loogle: `"normalCrossings"`: zero hits.
- Mathlib grep: `normalCrossing|normal_crossing|ncBranchCount|subboundary`:
  zero hits.
- LeanSearch: "Normal crossings subboundary affine etale parameter atlas with
  closed branch count levels": eight hits concerning etale objects, etale
  loci, affine opens, normalization covers and subscheme covers; no match.
- rg on project Sheaf and WeilConjectures using the same normal-crossing and
  branch patterns found the recorded definitions, CoordinateMaximalBranchStratum
  and downstream consumers such as NCMaximalBranchBlowup. The coordinate theorem
  assumes a global coordinate presentation and does not construct simultaneous
  charts for a reduced union of components. No duplicate theorem was found.
- The exact item id has no match in WeilConjectures; the proposed declaration
  name has no existing match in either project root.

No statement dispute, correction, new node, or dependency-interface repair is needed.
The first server compile passed for both sandbox and library module paths.

## Second reading by Q71

The dispatcher forbids starting other agents; this section records a second pass
by the same worker, with the node and the module open. Independent review remains
the maintainer's role as specified in the worker brief.

Checked every hypothesis and conclusion against the unchanged node. In particular,
checked the direction of `B ≤ D`, the residue-field composition direction, the full
parameter list at w versus its first r and s entries, and distinctness only for
coordinates vanishing at each other point. Checked both product equations are
scheme-theoretic, and that the finite-union clause uses generated ideals (closed
intersections), not products (unions). Checked the all-presentations conclusion
and arbitrary-etale invariance are separate from the existential atlas. Checked
integer levels, the empty union, and conditional quasi-compact boundedness.
No mathematical mismatch was found. Added direct public imports for the recorded
Mathlib and regular-parameter interfaces and expanded the docstring to carry all
seven original proof steps and their dependency identifiers.
