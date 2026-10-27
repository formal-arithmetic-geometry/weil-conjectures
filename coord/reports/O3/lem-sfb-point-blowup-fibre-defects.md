## Worker report

This is a stage-2 delivery, not a repeat of Q10's accepted stage-1 split. The current
item has a fourteen-step proof plan and reviewed split, but no Lean declaration.
The earlier stale-dispatch report confused these stages. The natural-language item
statement and its existing proof plan are preserved.

`Sheaf.AlgebraicGeometry.PointBlowupFibreDefects` states the item in three named
sorry-only theorems in namespace `AlgebraicGeometry.SurfacePointBlowup`:
`point_blowup_fibre_geometry`, `point_blowup_component_defects`, and
`point_blowup_inseparable_defects`. The accompanying definition module provides
canonical maps and a finite strict-transform-chain relation. There are no proved
helper theorems, no axioms and no hollow definitions.

Hypothesis and clause correspondence:

- A DVR R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Its trait is `Spec (.of R)`. The residue field is
  written canonically as the residue field of this spectrum at
  `IsLocalRing.closedPoint R`; this is canonically R/m. No independently chosen
  fraction field is needed in these statements: K is Frac(R) and is not used in
  any conclusion. A uniformizer is `(π : R) (hπ : Irreducible π)`, equivalent to
  generating the maximal ideal by `irreducible_iff_uniformizer`.
- The given family is `(f : X ⟶ Spec (.of R))`. Flat and finite type are `[Flat f]`,
  `[LocallyOfFiniteType f]` and `[QuasiCompact f]`. The regular scheme hypothesis
  is `hregular : IsRegularScheme X`, including local Noetherianity, and pure
  dimension two is `hpure : X.IsPureDimension 2`. No integrality, separatedness,
  excellence, connectedness, perfection or projectivity hypothesis is added.
- A closed point of the special fibre is represented by `p : X`,
  `hp : IsClosed ({p} : Set X)`, and `hs : f p = IsLocalRing.closedPoint R`.
  Since the special fibre is a closed subscheme, this is equivalent to being a
  closed point of that fibre. Its field l is literally `X.residueField p`.
- The blowup centre is `pointIdeal p hp`, the existing `vanishingIdeal` of the
  singleton closed set. Its blowup and map are the recorded global blowup, with
  no chosen thickening or arbitrary replacement morphism. `family f p hp` is
  its composite with f. The exceptional curve is its scheme-theoretic fibre
  `exceptional p hp`, with the existing `fiberι` and `fiberToSpecResidueField`.
- Regularity is the first conjunct of `point_blowup_fibre_geometry`. The next
  conjunct gives an isomorphism to `ProjectiveLine (Spec (X.residueField p))`
  commuting with the structural map to Spec(l), so it is an l-isomorphism.
- The exceptional coefficient assertion gives `∃ d : ℕ, 1 ≤ d ∧ HasOrder f p π d`
  and coefficient d at every exceptional generic point. `HasOrder` is exactly
  membership in m^d and nonmembership in m^(d+1). Since ideal powers decrease,
  this states the displayed maximum in the node. `coefficient` uses the existing
  `Ring.ord`, the length of O/(π), which on the ambient generic DVR is its
  normalized valuation. No order or valuation is postulated as extra data.
- Strict-transform coefficient and function-field invariance is
  `point_blowup_component_defects`. It quantifies a reduced integral closed
  component `IsSpecialComponent f i` and every `TransformChain R f g i j r`.
  It asserts that the final transform is a special-fibre component, takes its
  generic point to a generic point, makes the canonical `r.residueFieldMap`
  bijective, and preserves `coefficient`. The residue fields at generic points
  are precisely the function fields; the map is the canonical map of the
  actual iterated strict transform, not an arbitrary abstract field isomorphism.
- For coefficient greater than one, the same theorem produces a point z of
  the scheme-theoretic special fibre above that generic point whose actual
  local ring is not reduced (`_root_.IsReduced`, the ring predicate). For
  every later closed special-fibre centre `j t` on the transformed component,
  it asserts coefficient greater than one at every new exceptional generic
  point. The chain relation includes length zero and every finite succession
  of canonical reduced-point blowups, so persistence is not restricted to a
  single additional blowup.
- `point_blowup_inseparable_defects` uses the recorded
  `Algebra.IsSeparableExtension` with the canonical `residueMap f p hs` as
  algebra structure, negated. Finiteness of l/k follows from the existing
  hypotheses, so it is not assumed separately. The theorem asserts that the
  original exceptional curve and every finite strict transform are not
  geometrically reduced over the original residue field k. These morphisms
  are `exceptionalToResidue f p hp hs` and its composite with r.
- Every later closed centre on that strict transform has an injective ring
  map `φ : l →+* κ(j t)`. The equation with `j.residueFieldMap` identifies this
  with the canonical l-structure of the transformed curve; the equation with
  `residueMap` makes it an inclusion over the original k. The new exceptional
  curve is again not geometrically reduced over k. Thus the field containment
  is compatible with the original extension, not an unrelated abstract embedding.
- Nodal geometric fibres near x are `IsNodalNear f {p}`: an open neighbourhood
  whose morphism is flat and locally finitely presented, with reduced pure
  one-dimensional geometric fibres and the existing ordinary-double-point
  completion condition at every nonsmooth closed geometric-fibre point. This
  definition imposes no connectedness. A nonsmooth fibre centre is expressed
  by absence of a smooth open neighbourhood of p in the total family; under
  the flat finite-presentation hypotheses this is equivalent to nonsmoothness
  in its fibre. The theorem gives `HasOrder f p π 2`.
- A smooth fibre centre is existence of such a smooth neighbourhood. Under the
  nodal-near hypothesis its order is one. Separability, expressed using the
  same recorded extension predicate and canonical residue map, implies
  `IsNodalNear (family f p hp) (Set.range (exceptionalι p hp))`, so the
  neighbourhood contains the entire exceptional curve. Smooth inseparable
  centres are covered by the third theorem, which needs no nodality or
  smoothness assumption and still gives a non-geometrically-reduced exceptional
  component. No characteristic or perfectness restriction is present.
- `GeometricallyConnected (pointIdeal p hp).blowupMap` includes nonempty
  connected geometric fibres (Mathlib uses `ConnectedSpace`, which includes
  `Nonempty`), independently of the nodal and separable implications. It says
  this about q, not about the family over the trait.
- Properness is `IsProper` of q. Flatness and finite presentation of the new
  family are stated by `Flat`, `LocallyOfFinitePresentation`, `QuasiCompact`
  and `QuasiSeparated`. Projectivity is the implication from `IsHProjective f`
  to `IsHProjective (family f p hp)`, exactly the recorded finite-projective-space
  convention; it is not an extra hypothesis on all families.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`
  and `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `GammaSpecAdjunction`: `Scheme.ΓSpecIso` for the canonical trait-to-stalk map.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FiniteType`, `.QuasiCompact`,
  `.FinitePresentation`, `.QuasiSeparated`, `.Proper`, `.Smooth`: `Flat`,
  `LocallyOfFiniteType`, `QuasiCompact`, `LocallyOfFinitePresentation`,
  `QuasiSeparated`, `IsProper`, `Smooth`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme` (local
  Noetherianity plus the published stalkwise `IsRegular`).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`;
  `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr`, `Scheme.Γevaluation`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `IdealSheafData.vanishingIdeal`.
- `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformMap`, `strictTransformToSource`, `IdealSheafData.strictTransform`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`:
  `ProjectiveLine.TwistData` and the existing `ProjectiveLine` construction.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.RingTheory.AdicCompletion.Basic`/`.Algebra`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, its two variables.
  These enter through the existing `IsGeometricOrdinaryDoublePoint` from
  `Sheaf.AlgebraicGeometry.ProjectiveNodalTower`, not a new completion predicate.
- `WeilConjectures.FieldTheory.SeparableExtension`: `Algebra.IsSeparableExtension`.
- `Mathlib.RingTheory.OrderOfVanishing.Basic`: `Ring.ord`;
  `Mathlib.RingTheory.Length`: `Module.length`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected` and `.Reduced`:
  `GeometricallyConnected`, `GeometricallyReduced`.

The module imports the available module-format proof dependencies. The following
proof-only imports cannot be used by this module-format delivery and are omitted:
`Sheaf.AlgebraicGeometry.SmoothPointEtaleImmersion` and
`Sheaf.AlgebraicGeometry.NodalFamilyEtaleSourceLocality` are legacy non-module
files (server import of the latter was tested and rejected). No declaration from
them occurs in a delivered signature or definition. Their proof-plan steps remain
in the docstrings; their actual imports can be added on module migration. The
proof-only node `lem-sfb-dvr-nodal-chart-blowup-calculus` has no recorded
declaration to import. The two flat-base-change nodes have no `lean` field,
but their closed upstream audit records name `blowupFlatBaseChange` and
`blowupFlatBaseChangeIso` in `WeilConjectures.Blowup.FlatBaseChange`; those
full signatures and docstrings were read and the module is imported explicitly.
No missing proof result is an extra premise or a hollow definition.

Edge cases checked: disconnected regular total spaces; components meeting only
the generic fibre; imperfect fields and inseparable closed-point extensions;
smooth inseparable centres with multiplicity one; nodal nonsmooth centres with
multiplicity two; multiple fibre components and later centres at intersections;
centres off a component; a zero-length chain; empty geometric fibres away from
the designated point; arbitrary same-universe geometric test fields. The
hypothesis giving p excludes an empty original surface. No hypothesis forces
later families to be nodal, connected, reduced or separable. `HasOrder` is not a
length of O/(π) in the original two-dimensional local ring: length is used only
for the divisor coefficient at component generic points. Their distinction is
essential.

Searches: `msearch.py` LeanFinder on the regular-surface exceptional coefficient
and on finite point-blowup sequences returned elliptic-reduction/valuative-criterion
results, not this statement. Loogle queries `IsDiscreteValuationRing, Ideal.blowup`
and `Ring.ord, IsGenericPoint` returned no match. LeanSearch on ideal order found
`Ring.ord`, reused for generic coefficients; LeanSearch on iterated strict
transforms returned only generic properness/flatness results. Mathlib grep for
`blowup|Blowup` in AlgebraicGeometry returned zero hits; grep for order/chain names
returned only a DVR maximal-ideal coheight lemma. Project and DAG searches for
`SurfacePointBlowup|TransformChain|IsNodalNear`, maximal-ideal orders, iterated
strict transforms and the item's id found no existing complete statement or
point-transform-chain definition. `blueprint_refs.py search 'blowup transform chain'`
and `'point blowup'` found no blueprint match. Exact machine search responses are
copied into the new node's `mathlib_searches`. The existing nodal-geometric-fibre
predicate was rejected because it additionally requires nonempty connected
fibres; the existing projective nodal curve predicate additionally requires
projectivity and geometric connectedness. Only its ordinary-double-point helper
is used. No STATEMENT-DISPUTED flag or statement correction is needed.

Validation: both delivered Lean files compiled separately through `scompile.py`
against the live published build, without errors or warnings. The dry-run and
final delivery checks are recorded by the delivery wrapper.

## New nodes

`def-sfb-surface-point-blowup-data` records the canonical reduced-point ideal,
trait-element germ, exact maximal-ideal order, generic divisor coefficient via
`Ring.ord`, canonical residue maps, exceptional scheme and its maps, reduced
special-fibre components, finite iterated strict transforms, and nodal geometry
near a specified subset. Source: resolve.tex 0AGQ/0AGR, divisors.tex 080E,
models.tex 0CDC/0CDD and the item's explicit divisor and persistence calculations.
Every datum is constructed from existing blowup/fibre/strict-transform/length
constructions; the inductive relation has genuine zero and canonical successor
constructors. No surface geometry assertion is assumed inside a definition.
Searches above found no existing node carrying this combined interface. The
ordinary-double-point and pure-dimension definitions are reused. The ancestor
command returns `None`, as already recorded by the accepted stage-1 split;
the new record retains this null ancestor and the exact created-item chain.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
