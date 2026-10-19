## Worker report

The module `Sheaf.AlgebraicGeometry.StableModificationFinitePresentationSpread`
states `AlgebraicGeometry.exists_stable_modification_finite_presentation_spread`.
Its sole theorem has proof `sorry`; no definitions or auxiliary theorems are added.
The item's mathematical statement is unchanged. Its statement dependencies gain the
already landed `def-trf-multipointed-curve`, as allowed by brief-stage2 §5.

Clause-by-clause correspondence:

- Integral finite-type integer base: `T : Scheme.{u}`, `[IsIntegral T]`, and
  `t : T ⟶ Spec (.of (ULift.{u} ℤ))` with `[LocallyOfFiniteType t] [QuasiCompact t]`.
  The lift of the integers permits every scheme universe and represents the same base.
- The generic point is the canonical `genericPoint T`. The function field is
  `T.functionField`; `[Algebra T.functionField L] [IsSepClosure T.functionField L]`
  fixes the separable closure and its specified inclusion.
- The centred valuation ring and the required agreement at the generic point are
  precisely `v : RiemannZariski.ValuationPoint T L η`, where `η` is the composite
  of `Spec.map` of the field inclusion with `T.fromSpecStalk (genericPoint T)`.
  Its `V` is a valuation subring of `L`, its `centre` is the supplied map, and its
  `fac` is the required generic equality. A valuation subring of a field has that
  field as its fraction field, including the height-zero case `V = L`.
- `P : MultipointedCurve T` and `Y : MultipointedCurve (Spec (.of v.V))` are the
  two prescribed multipointed curves. Their fields `flat_X`, `flat_D` express
  flatness, `lfp_X/lfp_D`, `qc_X/qc_D`, `qs_X/qs_D` express full finite presentation,
  `pure_X/pure_D` assert pure fibre dimensions 1 and 0, and `closed` and `comm`
  give the closed marking over the base. `Scheme.IsPureDimension` quantifies over
  all irreducible components and uses `topologicalKrullDim` of their subspaces.
- The given maps are exactly `fX : Y.X ⟶ pullback P.x v.centre` and
  `fD : Y.D ⟶ pullback P.d v.centre`. Their `[IsProper]` instances assert properness.
  `hX` and `hD` say that they are morphisms over `Spec V`, as required for maps
  between the displayed relative curves (Temkin §1.2).
- `hmark` says that the maps commute with markings after projection to `P.X`.
  Their other components already agree by `hX`, `hD`, and the source marking's
  `comm`. Pullback hom-extensionality makes this exactly commutation with the
  marking of the base-changed target, with no separatedness assumption.
- `hXη` and `hDη` assert `IsIso` of the canonical `pullback.map` along
  `Spec.map (CommRingCat.ofHom v.V.subtype) : Spec L ⟶ Spec V`.
  These are the given maps on the fibres over `Spec L`, not arbitrary isomorphisms.
- The conclusion's `U : RiemannZariski.QuasiModel T L η` is an integral scheme
  with separated, locally finite-type and quasi-compact map to `T`, a specified
  generic map from `Spec L`, and the specified generic factorization.
- The existential `l : Spec V ⟶ U.X` satisfies both `l ≫ U.map = v.centre` and
  `Spec.map ... ≫ l = U.generic`, exactly the two required compatibilities.
- `Y₀ : MultipointedCurve U.X` is the descended pair; `gX` and `gD` have the
  displayed fibre-product targets and `IsProper` conclusions. `hgX`, `hgD` give
  their base compatibility, and the following marking equality is compatibility
  of the pair, by the same pullback hom-extensionality argument as for `hmark`.
- The next two `IsIso (pullback.map ...)` clauses base change along
  `U.X.fromSpecResidueField (genericPoint U.X)`. Thus they assert isomorphisms
  on the actual generic residue-field fibre of `U`, not merely after extension to `L`.
- `eX : pullback Y₀.x l ≅ Y.X` and `eD : pullback Y₀.d l ≅ Y.D` are the required
  isomorphisms, in the node's direction. Their first two equations say they are over
  `Spec V`. The third equation identifies their markings after projecting to `Y₀.X`.
  The other projection agrees from those base equations and the two marking
  commutation equations, so this is exactly compatibility with closed immersions.
- The last two equations identify each descended map, after pullback and projection
  to the original `P.X` or `P.D`, with the prescribed `fX` or `fD`. The other
  projection agrees by the previously stated base equations and `l ≫ U.map = v.centre`.
  Hence pullback hom-extensionality identifies the complete maps, including the
  canonical iterated-pullback comparison, not only their underlying point maps.
- No semistability, stability, nonempty marking, separatedness of either curve,
  or properness of either structural morphism occurs in the statement.

Dependency declarations read and used:

- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, through the existing
  pure-dimension and multipointed-curve definitions.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, through `MultipointedCurve`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint`, through the
  existing generic-scheme interface and canonical generic points.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, through `MultipointedCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, through
  `MultipointedCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`:
  `AlgebraicGeometry.RiemannZariski.GenericScheme`, `QuasiModel`, `ValuationPoint`
  (their complete field lists and docstrings were read).
- Newly cited existing node: `Sheaf.TraceFormula.MultipointedCurve`,
  `AlgebraicGeometry.MultipointedCurve`, and its existing pure-dimension interface
  `Sheaf.AlgebraicGeometry.PureDimension`, `Scheme.IsPureDimension`.

The five already recorded nontrivial proof modules are imported without `public`:
`DescendClosedImmersion`, `DescendFlatFinitePresentation`, `EventuallyProper`,
`ProperLimitNoetherian`, and upstream `AffineTransitionLimit`. The pure-relative-
dimension finite-stage node has no recorded declaration and is named in the proof
plan but cannot yet be imported. Mathlib proof leaves are available through the
import closures. No new missing statement interface was needed.

Edge cases checked by reading the fully expanded types: empty markings and empty
fibres impose no component existence in `Scheme.IsPureDimension`; height-zero
valuation rings are allowed; an already-isomorphic pair is allowed; neither curve
must be separated or proper over its base; mixed and positive characteristic are
allowed. All scheme, field and valuation types use the same arbitrary universe `u`,
as do the existing dependency interfaces. No index-universe restriction is added.

Searches (all performed before writing the module):

- `msearch.py ... leanfinder`: "Finite presentation descent of a proper modification
  of a multipointed curve over a valuation ring to a finite type quasi-model":
  8 hits, including `ValuativeCriterion.existence`, `IsProper.of_valuativeCriterion`,
  and `LocallyOfFinitePresentation`; none states simultaneous marked descent.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsProper,
  AlgebraicGeometry.LocallyOfFinitePresentation`: 0 hits.
- `msearch.py ... leansearch`: "A proper generic isomorphism of marked curves over
  a valuation ring descends to a finite presentation model": 8 hits, primarily
  fpqc isomorphism descent and finite-presentation facts, no match.
- `msearch.py ... grep`: `multipointed|stableModification|finite_presentation_spread`
  in Mathlib AlgebraicGeometry: 0 hits.
- `rg` of `Multipointed|multipointed|MultiPointed|finite_presentation_spread|stable_modification`
  in upstream `WeilConjectures` and side `lean/Sheaf`: upstream has no match;
  the side library has the already reused `MultipointedCurve`, its finite-type
  model theorem, Temkin stable-modification predicate, and modification definitions.
  None gives the prescribed proper pair's finite-presentation descent. Exact item-ID
  search in upstream `WeilConjectures` also has no match. The DAG has the existing
  `def-trf-multipointed-curve`, so no second definition is introduced.

The exact proposed full theorem name was also searched in `dag/lean_names_upstream.json`,
upstream `WeilConjectures`, and the side library: no collision. The UTC record date
was checked with `date -u +%F`.

Source checked online because the PDF is absent locally:
https://arxiv.org/html/0707.3953v3, §1.2, §3.1, Remark 3.1.1(ii), and the second
paragraph of the proof of Theorem 1.5. These confirm the exact relative-curve notion
and the approximation step. The four proof steps are carried in full as a natural-
language plan in the theorem docstring. No statement correction or dispute is needed.

## Second reading by Q52

A separate second pass over the node and completed signature checked every clause
against the correspondence above. This is the dispatcher's worker self-check;
the maintainer performs the independent review, and no subagent was started.

In particular I checked the three easy-to-miss points directly: the generic
isomorphisms in the conclusion are over `κ(genericPoint U.X)` rather than just `L`;
the two isomorphisms over `Spec V` preserve the marking and both supplied maps;
and the marking/source maps really are morphisms over the base, not unrestricted
scheme morphisms. The projection equations are equivalent to the full square
identities by pullback hom-extensionality; none is a tautological extra conclusion.
The additional landed definition node is only a dependency bookkeeping addition,
not a mathematical change. No mismatch was found in this pass.
