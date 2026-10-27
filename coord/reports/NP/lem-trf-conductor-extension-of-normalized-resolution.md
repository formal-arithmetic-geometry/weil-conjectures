## Worker report

The delivery states `lem-trf-conductor-extension-of-normalized-resolution` in
`Sheaf.AlgebraicGeometry.ConductorNormalizedResolutionExtension`. The original
statement and proof are unchanged. Its statement dependencies gain only the new
definition node `def-trf-smooth-normalized-resolution-rule`.

The module supplies three postponed theorems, all realizing clauses of this node:
`rationalConductor_geometry`, `rationalConductor_smoothBaseChange`, and
`conductor_normalizedResolution_extension`. Their docstrings give the corresponding
node proof steps. All proofs are `by sorry`; all definitions have real data. The
preparation's scheme and structure morphism are the specified normalized blowup and
its composite to Spec ℚ, with only their property fields taken from the geometry theorem.
The final theorem asserts existence of the extension with its entire prepending
specification, rather than choosing an arbitrary tower in a definition.

Hypothesis and conclusion correspondence:

- Every reduced finite-type ℚ-scheme, including finite disjoint unions: the existing
  `RationalResolutionInput` has `scheme`, `structureMap : scheme ⟶ Spec (.of (ULift ℚ))`,
  `reduced`, `finiteType`, and `quasiCompact`. Universes are explicit; ULift fixes only
  the universe of ℚ. No connectedness, separation, dimension, irreducibility or
  nonemptiness hypothesis is imposed.
- Every normal member: `NormalRationalResolutionInput` is the subtype with
  `∀ x, IsDomain (X.scheme.presheaf.stalk x) ∧ IsIntegrallyClosed (...)`.
- Given rule N: the main theorem binds `N : SmoothNormalizedResolutionRule
  NormalRationalResolutionInput (fun X ↦ X.val.scheme)`. Its `tower` assigns the existing
  `QENormalizedResolutionTower`, a based finite `Monoscheme.NormalizedTower` with
  coherent ideal modules, nonempty nowhere dense zero schemes, and regular last level.
  Despite the QΕ name, this existing tower type accepts ANY scheme and assumes no
  quasi-excellence hypothesis.
- N's smooth comparisons: `comparison` uses the existing
  `QENormalizedResolutionComparison`, for each `h` and proof `Smooth h`. Its `pulled`,
  `initial`, `lift`, `base`, `cartesian`, `centers`, and `arrows` specify recursive
  scheme pullback and the actual extended ideal. Its `unit_isIso` and the existing
  `NormalizedContraction.deleted` jointly delete exactly unit stages and only
  isomorphisms. `keptCenter`, `keptMap`, `adjacent` and the monotone surjective index
  retain the other ideals in their original order.
- N's identity/composition laws: `identityIndex`, `identityMap`, `compositionIndex`,
  `compositionMap`. HEq records equality of maps whose domains are transported along
  the index equations; it is actual map equality, not merely existence of an isomorphism.
- N deletes no stage for a surjective map: `surjective_no_deletion` asserts injectivity
  of the already surjective contraction index. N(∅) trivial: `empty` gives length zero
  for every input with `IsEmpty (base X)`.
- ν and the normalization cokernel: use existing `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, `conductorCokernel`, and `conductorIdeal`.
  The latter uses `Scheme.IdealSheafData.ofIdeals` on affine module annihilators of
  the cokernel's sections, the recorded annihilator construction, not a replacement.
- D_X coherent, nowhere dense, and unit iff normal:
  `RationalConductorGeometry.coherent`, `.nowhereDense`, `.unit_iff`, asserted for each
  input by `rationalConductor_geometry`.
- P(X) normal, reduced, finite type: `.normal`, `.reduced`, `.finiteType`, `.quasiCompact`.
  `conductorPreparedRationalInput.scheme` is definitionally
  `(conductorIdeal X.scheme).normalizedBlowup`; its rational structure map is
  `(conductorIdeal X.scheme).normalizedBlowupMap ≫ X.structureMap`.
- H_N(X) is the conductor arrow followed by N(P(X)), omitting exactly a unit conductor:
  `IsRationalConductorResolutionExtension` has `levelIndex`, `stageIndex`, `length`,
  `levelValue`, `stageValue`, `before`, `after`, `tailIso`, `tailArrow`, and `tailCenter`.
  Indices are shifted by `rationalConductorStageCount X`, the explicit classical
  conditional 0 for unit conductor and 1 otherwise. Its length equation permits no
  additional stages. `unitBase` transports the entire tail through P(X) → X when
  D_X is unit; `conductorStage` specifies exactly the initial conductor ideal and
  normalized blowup arrow in the nonunit case, with all base identifications included.
- H_N is a finite normalized tower with coherent nonempty nowhere dense centers,
  regular last level, and H_N(∅) trivial: the existential H in the main theorem has
  `SmoothNormalizedResolutionRule` type, whose tower and empty fields supply exactly
  these assertions.
- For EVERY smooth h:Y → X, D_Y = D_X O_Y: the first conjunct of
  `rationalConductor_smoothBaseChange`, with no quasi-compact hypothesis on h.
- Canonical P(Y) ≅ P(X) ×_X Y with smooth induced map: the same theorem gives the
  unique k with `IsPullback k P(Y)→Y P(X)→X h ∧ Smooth k`. An `IsPullback` is precisely
  the canonical isomorphism to the chosen fibre product with both projections fixed;
  uniqueness characterizes the comparison, rather than selecting an unconstrained map.
- Resulting H comparisons, ordered ideals, identities, composition, and no contraction
  for surjective h: all fields of the existential H's smooth rule, just as for N above.
  In particular unit arrows are explicitly isomorphisms; a proper invertible center is
  retained even when its normalized blowup happens to be an isomorphism.

Dependency interfaces read and reused:

- `Sheaf.AlgebraicGeometry.NormalizedBlowup`:
  `Scheme.IdealSheafData.normalizedBlowup`, `.normalizedBlowupMap`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, via the regular-last
  clause of `Monoscheme.NormalizedTower.IsDesingularization`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` on every stalk, as prescribed by `def-weil-pbc-normal-ring`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` for finite type, via `RationalResolutionInput`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, via the conductor and normalized-blowup definitions.
- `Sheaf.TraceFormula.ConductorSmoothBaseChange`: `conductorCokernel`, `conductorIdeal`,
  and proof dependency `conductor_smooth_base_change`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `RingedSpace.IsCoherent`, the finite-type and finite-type-kernel predicate, used for
  the ideal module. The quasi-coherent/finite-type conjunction does not replace coherence.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the fibre product;
  `IsPullback` states its universal property with the prescribed two projections.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Sheaf.AlgebraicGeometry.QENormalizedResolutionRule`:
  `QENormalizedResolutionTower`, `QENormalizedResolutionComparison`, `.levelMap`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`:
  `NormalizedTower`, `IsNormalizedBlowup`, `NormalizedContraction`,
  `NormalizedTower.IsDesingularization`.
- `Sheaf.AlgebraicGeometry.NormalizedTowerDescentData`: `NormalizedTower.toFirst` and
  `.HasNowhereDenseCenters`.
- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `RationalResolutionInput`.

The stated proof dependencies are imported, including the normalized-blowup calculus,
Mathlib Noetherianity and pullback-surjectivity modules. Definition and theorem signatures
and docstrings were read in full for the non-Mathlib dependencies; the relevant Mathlib
predicates and fibre-product signatures were also read. The source PDF was read directly
at printed pp.90–94 (PDF pages 96–100). It distinguishes centers as data, recursive
normalized transforms, cartesian pullbacks, unit-stage contraction and synchronization
by disjoint unions, as used here.

Edge cases checked before finalizing the statement:

- Empty input: stalkwise normality is vacuous, conductor is unit, and preparation is the
  empty normalized blowup. Both N.empty and H.empty require zero length. No `Nonempty`
  hypothesis on schemes excludes this case.
- Normal X: D_X is unit and the length is exactly the N(P(X)) length; `unitBase` retains
  the base identification P(X) ≅ X rather than pretending it is definitional equality.
- Nonnormal cusp: nonunit conductor produces exactly one added stage, with its actual
  ideal, followed by the tail. A length-zero tail is allowed if preparation is regular.
- Smooth inclusion of the normal locus of a nonnormal X: the conductor becomes unit,
  and the initial stage is deleted only after its arrow becomes an isomorphism.
- Proper invertible center: its blowup may be an isomorphism, but it is not deleted
  because the criterion is unit ideal, not isomorphism alone.
- Disconnected inputs and varying smooth relative dimensions: admitted without
  synchronization by separate components or an equidimensionality hypothesis.
- Surjective smooth maps, including the empty identity: injectivity of the contraction
  index means every stage survives; no nonempty-scheme hypothesis is needed.
- Identity and two successive smooth maps: both count/index and actual-map equations
  are present; deleting unit ideals in two passes preserves the same ordered survivors.

Searches: the required msearch leanfinder, loogle and Mathlib grep queries were run for
both the extension and the missing rule; leansearch was also run for the rule. Complete
machine search results are included in the new node's `mathlib_searches`. LeanFinder
returned relative-normalization declarations only; Loogle `"conductor", "blowup"` and
both Mathlib grep searches returned zero hits. LeanSearch returned smooth-morphism and
relative-normalization declarations, not a rule. `rg` over both project trees found
`OrdinaryResolutionRule`, `QENormalizedResolutionRule`, `QEConductorNormalizedResolutionExtension`,
`MonoschemeToricRealization`, `NormalizedTowerDescentData` and regular/toric variants,
which were read and reused wherever their interfaces apply. The upstream item-ID search
had no match. DAG concept grep and `tools/blueprint_refs.py search 'smooth normalized'`
found no existing node for this smooth rule (the blueprint reference search returned
zero matches). The quasi-excellent conductor extension assumes regular functoriality on
all quasi-excellent inputs and is not the present statement about arbitrary N on only
normal finite-type inputs with smooth functoriality.

There are no statement corrections, disputed clauses or dependency repairs.
Both delivered modules compiled cleanly through scompile.py, including dependency order,
against the live published build. No global build or direct repository write was used.

## New nodes

`def-trf-smooth-normalized-resolution-rule` records exactly the missing smooth input-rule
notion in `Sheaf.AlgebraicGeometry.SmoothNormalizedResolutionRule`. It defines the normal
subtype of the existing rational finite-type input and a smooth rule on an arbitrary
family, using the existing based tower, cartesian comparison and ordered contraction
interfaces. Source: ILO VIII 2.2.5–2.2.9 and 2.3.2–2.3.5. Its dependency node references
are exactly the four notions named in its TeX statement. The existing regular rule is
stronger in its allowed morphisms; the existing toric rule has a smaller input family.
Neither can serve as the hypothesis on the arbitrary N of this item. The new rule
copies no tower, ideal, blowup, normality or contraction definition. The item's conductor
prepending specification is specialized to the actual finite-type rational preparation;
the similarly named quasi-excellent specification has an incompatible input type and
would force additional property interfaces. Every helper remains attached to the
owning conductor-extension node, and the new node is directly cited by the item.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
