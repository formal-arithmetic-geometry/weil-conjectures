## Worker report

The module `Sheaf.SixFunctors.TraceFormula.SmoothSelfProductComponentRank` states
`AlgebraicGeometry.exists_smooth_selfProduct_component_rank`. Its only theorem proof is
`sorry`. The helper `Scheme.Hom.geometricIrreducibleComponentCount` gives real data: the
`ENat.card` of `irreducibleComponents` of the actual pullback along the canonical
`Scheme.fromSpecAlgebraicClosureResidueField` geometric point. It defines the count
introduced in the item's own statement, rather than an independent missing notion.
At a generic point this is precisely the node's rho. A finite count is represented by
an equality to the cast of a natural number, so an infinite fibre count cannot satisfy
it. No new node, dependency repair or statement correction is needed.

Hypothesis and clause correspondence:

- `S Y : Scheme.{u}` are the schemes; `[IsAffine S]`, `[IsLocallyNoetherian S]`, and
  `[IsIntegral S]` express the affine Noetherian integral base. Affine schemes are
  quasi-compact, so no extra quasi-compactness hypothesis is needed. `IsIntegral`
  includes nonemptiness, reducedness and irreducibility, for both S and Y.
- `hS : ∀ s, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed ...` is exactly
  normality in the local-ring sense specified by the node, not an extra condition
  on global sections.
- `f : Y ⟶ S`, `[Smooth f]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and
  `[QuasiCompact f]` are respectively the named morphism and its smoothness,
  separatedness and finite type. `IsSeparated` literally means that
  `pullback.diagonal f` is a closed immersion.
- `η : S`, `ξ : Y`, `hη : IsGenericPoint η Set.univ`, and `hξ : ...` name the two
  generic points. The geometric fibres use their residue fields, which are canonically
  the function fields for integral schemes; no alternate function-field object is made.
- `∃ N : ℕ, 0 < N ∧ f.geometricIrreducibleComponentCount η = (N : ℕ∞)` expresses
  that N is the positive finite original count. The helper forms the base change to
  `AlgebraicClosure (S.residueField η)` using the existing canonical geometric point.
- W is always exactly `pullback f f`, the projection always `pullback.fst f f`, and
  the diagonal always `pullback.diagonal f`. `IsNoetherian W` and the pointwise
  domain/integrally-closed conjunction express all stated properties of W.
- `m : ℕ`, `C : Fin (m + 1) → W.Opens`, injectivity of C, and equality of the range
  of its underlying sets with `irreducibleComponents W` enumerate each irreducible
  component exactly once. The use of opens plus `IsClosed` supplies the clopen
  subscheme structure, and `IsIntegral (C i).toScheme` supplies nonemptiness and
  integrality. Local normality is repeated explicitly at all points of each C_i.
  The normal integral components are disjoint and cover W, as follows from this
  exhaustive irreducible-component enumeration and local normality.
- For every i, the four morphism predicates on `(C i).ι ≫ pullback.fst f f` give
  smooth, separated, finite type projections. `DenseRange` is the exact stated
  definition of dominant. The count equality assigns their actual counts to `r i`.
- `Set.range (pullback.diagonal f) ⊆ C i ↔ i = 0` gives the unique distinguished
  component containing the whole diagonal image. The equations `r 0 = 1`,
  `∑ i, r i = N`, and `i ≠ 0 → 1 ≤ r i ∧ r i < N` give all three numerical clauses.
- `GeometricallyIntegral (((C 0).ι ≫ pullback.fst f f).fiberToSpecResidueField ξ)`
  is geometric integrality of the ordinary generic fibre, as a scheme over κ(ξ).
- The existential δ is a map to C_0 with `δ ≫ (C 0).ι = pullback.diagonal f` and
  `δ ≫ π_0 = 𝟙 Y`. Thus it is the actual diagonal factor and a section, not an
  arbitrary point or an independently chosen section.
- The last universal quantifier ranges over every `B : Y.Opens` with
  `IsAffineOpen B` and `(B : Set Y).Nonempty`. There is a generic point b of B,
  explicitly asserted by `IsGenericPoint b Set.univ`; no existence is assumed.
  Each C_{i,B} is exactly `pullback π_i B.ι`. Its first projection is an open
  immersion, its source integral (hence nonempty) and locally normal, and its second
  projection smooth, separated, locally of finite type and quasi-compact. Its count
  at b equals the same `r i`, supplying the asserted equality of generic counts.
- The final δB maps B into `pullback π_0 B.ι`. Its first-projection equation is
  `δB ≫ pullback.fst ... = B.ι ≫ δ`, identifying it with the restriction of the
  same diagonal section; its second-projection equation makes it a section over B.
- There is no surjectivity assumption and no geometrically integral generic-fibre
  assumption on f. All binders and the single universe u are explicit; no auxiliary
  field universe excludes residue fields. `set_option autoImplicit false` is active.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, opens and stalks;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, `IsAffineOpen` (transitively
  imported by the geometric modules).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace` (the quasi-compact part of
  `IsNoetherian`, also automatic for affine schemes).
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` (including its nonempty
  field); `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  with `IsDomain` on stalks. This is the recorded inline normal-domain interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, using the recorded
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.IsClosedImmersion` notion.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`,
  `snd`, `diagonal`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies their existence.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `fromSpecResidueField`; `WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField`:
  `Scheme.fromSpecAlgebraicClosureResidueField`, whose full construction is read.
- `Mathlib.Topology.Sober`: `IsGenericPoint`;
  `WeilConjectures.AlgebraicGeometry.FunctionField` imports Mathlib `Scheme.functionField`
  and records its integral-scheme clause. The residue-field geometric fibre is used
  directly, because the function field at a generic point is canonically that residue
  field, rather than the general component-product carrier.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  `Mathlib.Topology.Irreducible`: `irreducibleComponents`;
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiberToSpecResidueField`.

The recorded proof modules that already have declarations are imported without
`public`: `Sheaf.TraceFormula.SmoothComponentPureTranscendental`
(`exists_geometricallyIntegral_connectedComponent`) and
`Sheaf.TraceFormula.GeometricFibreComponentCountBaseChange`
(`geometricFibreComponentCount_baseChange`), as well as the applicable Mathlib
properness, openness and upstream `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`
and `SmoothFiber` modules. Unstated proof-only nodes (smooth normal ascent, normal
locally finite component decomposition, field-extension components) do not provide
an import yet and do not supply data for this stage-2 statement. They remain proof
steps in the complete nine-step declaration docstring.

Edge cases checked before writing: for Y=S and f the identity, N=1 and m=0,
so the strict-decrease clause is empty and the unique component is the whole
self-product. A non-surjective nonempty affine open immersion Y into S also has
N=1 and fits with no added surjectivity. For a finite separable extension L/K,
Spec(L tensor_K L) splits into the distinguished L factor and other field factors;
the degrees over L are the r_i, summing to [L:K], and every other r_i is positive
and smaller than N. Empty S and empty Y are excluded by the node's integrality;
empty affine B is excluded by its explicit nonempty condition. No fixed characteristic,
dimension, geometric integrality or algebraic closedness is imposed on S or Y.

Searches actually run with `msearch.py`:

- LeanFinder: `smooth self product normal integral base diagonal component geometrically
  integral generic fibre component counts decrease`. Eight hits: standard smooth
  relative dimensions, smooth finite-type approximation and the nonintegrality of affine
  space morphisms. None states the self-product decomposition or count theorem.
- Loogle: `"GeometricallyIntegral", "pullback"`. Two hits, the two factor-order
  instances making a product integral when a whole factor is geometrically integral.
  They assume the generic geometric-integrality property this node produces only for
  one component, so neither is a match.
- Mathlib grep in AlgebraicGeometry: `geometric.*[Cc]omponent|diagonal.*[Cc]omponent|selfProduct`.
  Four hits: geometric reducedness with finite components and three implementation
  references to diagonal-component chart ranges in `AffineTransitionLimit`. I read the
  latter; these are auxiliary opens in a limit argument, not the normal self-product
  decomposition or generic component-count result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for normal/component and
  geometric/component combinations, self-product names, count definitions, and the
  exact item id. No identical theorem or existing named count was found. The searches
  did locate the upstream canonical algebraic-closure geometric point, which is reused.

Source checked online: https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf,
Lemma 4.3(i)-(ii), printed page 10. It identifies the graph component and its count one,
and bounds the remaining counts. The node's more explicit positivity, sum and
restriction clauses follow the nine-step split; all are retained in Lean.

No STATEMENT-DISPUTED issue or node fault found.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
