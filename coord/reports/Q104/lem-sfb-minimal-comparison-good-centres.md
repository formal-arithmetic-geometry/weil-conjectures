## Worker report

The module Sheaf.AlgebraicGeometry.MinimalComparisonGoodCentres states
AlgebraicGeometry.minimal_comparison_good_centres, with exactly one postponed proof (`sorry`).
It adds no definitions, axioms, auxiliary theorems, or restrictions on the residue characteristic.
The statement and proof of the DAG node are unchanged. Three already-landed definition nodes
are added to stmt_deps to reuse their existing interfaces.

Clause-by-clause correspondence:

- DVR R: `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
- Fraction field K: `[Field K] [Algebra R K] [IsFractionRing R K]`.
  S is `Spec (.of R)`; its canonical closed point is `IsLocalRing.closedPoint R`.
  The field k is represented canonically by
  `(Spec (.of R)).residueField (IsLocalRing.closedPoint R)`, canonically isomorphic
  to R's residue field. No arbitrary field action is introduced.
- The two S-schemes are `T₁ T₂ : Over (Spec (.of R))`.
  Their integrality is `[IsIntegral T₁.left]` and `[IsIntegral T₂.left]`.
- Regularity is `hregular₁` and `hregular₂ : IsRegularScheme ...`, including
  local Noetherianity as required by the recorded dependency.
- Dimension two is `hdim₁` and `hdim₂ : topologicalKrullDim ... = 2`.
- Projectivity is `[IsHProjective Tᵢ.hom]`, exactly the blueprint convention.
  Flatness is `[Flat Tᵢ.hom]`. Finite presentation is
  `[LocallyOfFinitePresentation Tᵢ.hom]` together with projectivity: H-projectivity
  gives properness, hence quasi-compactness and quasi-separatedness, so this is
  finite presentation, not merely its local variant.
- Each `hnodalᵢ` quantifies over every algebraically closed field Ω in the scheme
  universe and every map `g : Spec Ω ⟶ S`. The geometric fibre is the actual
  `pullback Tᵢ.hom g`. `Nonempty` records nonemptiness, `IsReduced` records
  reducedness, and `.IsPureDimension 1` records pure dimension one. For each
  closed nonsmooth point, the conclusion is `IsGeometricOrdinaryDoublePoint`:
  the maximal-ideal-adic completion of the actual stalk is ring-isomorphic to
  `MvPowerSeries (Fin 2) Ω / (X 0 * X 1)`. Smoothness is existence of a smooth
  open neighbourhood for the fibre projection. No connectedness is imposed.
- Smooth generic fibres are the two `[Smooth (pullback.snd ...)]` binders
  for the canonical fraction-field map induced by `algebraMap R K`.
- The fixed K-isomorphism is `α`, an isomorphism of the two objects obtained
  by `Over.pullback` along that fraction-field map. Thus it is over K.
- The finite sequence is `A : OrdinaryBlowupTower T₁.left`. It records the
  length, levels, initial isomorphism, actual transition composites, centre
  ideals and isomorphisms from successor levels to their canonical blowups.
  `p`, `hp`, `hcentre`, `hspecial` specify each centre as a closed point,
  its ideal as exactly `SurfacePointBlowup.pointIdeal`, and its image as the
  closed point of S. This is the reduced closed special-fibre point, without
  an extra regularity, smoothness, separability, or thickness assumption.
- The terminal scheme W is `A.level (Fin.last A.length)`; its S-map is
  `A.toBase (Fin.last A.length) ≫ T₁.hom`. The second projection `q₂` is
  a morphism in `Over S`, enforcing that it is an S-morphism.
- `hgeneric` says the base change of `q₂` equals the base change of the actual
  tower composite followed by `α.hom`. No arbitrary generic lift is used.
- Existence of a comparison is furnished by the given A, centres, q₂ and
  hgeneric, rather than redundantly assumed separately.
- `hminimal` quantifies over every ordinary tower B, all its reduced closed
  special point centres, and every second S-map inducing that same α. Its
  conclusion `A.length ≤ B.length` is precisely minimum length among all
  pairs. Competitors need not already have good centres or nodal stages.
- The conclusion ranges over `j : Fin A.length`. Its first conjunct gives
  an open neighbourhood smooth for the actual stage map to S. This expresses
  membership in its relative smooth locus without assuming finite presentation
  of intermediate stages as an extra input (it is a consequence of blowup geometry).
- The second conjunct uses `.hom.Finite` on the canonical residue map,
  i.e. finite generation of the centre residue field as a module over k.
- The third conjunct is `Algebra.IsSeparable` for the algebra structure induced
  by that same canonical map. Its definition uses separability of each element's
  minimal polynomial, precisely the polynomial notion of the recorded dependency.
  Finiteness is stated separately, so this says a finite separable field extension.

Dependency declarations read and used:

- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`.
- Mathlib.Algebra.Algebra.Defs: `Algebra`; Mathlib.RingTheory.Localization.FractionRing:
  `IsFractionRing` and the canonical `algebraMap`.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsIntegral`, `IsReduced`.
- Sheaf.AlgebraicGeometry.IsRegularScheme: `AlgebraicGeometry.IsRegularScheme`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `AlgebraicGeometry.IsHProjective`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: `LocallyOfFinitePresentation`.
- WeilConjectures.Blowup.Gluing: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, `Hom.residueFieldMap`.
- Mathlib.FieldTheory.Separable: `Polynomial.Separable`, `IsSeparable`, `Algebra.IsSeparable`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `Limits.pullback`.
- Sheaf.AlgebraicGeometry.PureDimension: `Scheme.IsPureDimension`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth` and the smooth-locus convention.
- Mathlib.RingTheory.AdicCompletion.Basic and Mathlib.RingTheory.MvPowerSeries.Basic:
  `AdicCompletion`, `MvPowerSeries`, through the existing ordinary-double-point definition.
- Newly cited, already-landed def-trf-ordinary-resolution-rule:
  Sheaf.AlgebraicGeometry.OrdinaryResolutionRule, `OrdinaryBlowupTower`, `.toBase`.
  This structure is general over an arbitrary scheme; only other structures in the
  module concern rational resolution inputs. No rationality assumption is inherited.
- Newly cited, already-landed def-sfb-surface-point-blowup-data:
  Sheaf.AlgebraicGeometry.SurfacePointBlowupData, `SurfacePointBlowup.pointIdeal`
  and `SurfacePointBlowup.residueMap`.
- Newly cited, already-landed def-trf-projective-nodal-tower:
  Sheaf.AlgebraicGeometry.ProjectiveNodalTower, `IsGeometricOrdinaryDoublePoint`.
  The stronger connected-nodal-tower predicates are not used.

Proof dependency imports are plain imports: RegularPointBlowupGeometry,
PointBlowupFibreDefects, Morphisms.ProjectiveImpliesProper, Mathlib Proper,
ClosedPointField, and NormalModificationCodimensionOne. The remaining four
proof nodes (nodal-trait-finite-singular-charts, regular-trait-curve-surface-components,
birational-cartier-geometric-reduction, delete-untouched-point-blowup) currently
have no recorded Lean module, so no import can yet be added for them. They are
not statement dependencies and no declaration of theirs is needed to state this item.

Edge checks: length zero gives an empty `Fin` and a vacuous conclusion; initial and
terminal levels still exist. The initial isomorphism permits any presentation of
T₁, rather than requiring definitional equality. Empty geometric fibres are explicitly
excluded; disconnected fibres and all residue characteristics are allowed. Competitors
include nonsmooth centres and inseparable centre residue fields, so minimality is not
restricted to the desired conclusion. No generic fibre isomorphism is assumed for q₂
beyond its specified equality with α composed with the tower's generic map.
Closed special-fibre points are closed in the total scheme, since the special fibre
is a closed subscheme. All universe variables and term variables are bound explicitly;
both autoImplicit options are disabled.

Searches (2026-10-24):

- msearch.py leanfinder, "A minimum length comparison of regular nodal curve models
  over a discrete valuation ring blows up only smooth points with finite separable
  residue fields": 8 hits on WeierstrassCurve minimality, none about surface-centre
  comparisons.
- msearch.py loogle, `"AlgebraicGeometry", "blowup"`: 0 hits.
- msearch.py grep, `minimal.*blow|blow.*minimal|semistable|nodal`, AlgebraicGeometry:
  0 hits.
- msearch.py leansearch, "minimal length point blowup sequence regular nodal surfaces
  smooth separable centres": 8 hits on smoothness and Weierstrass minimality, no match.
- rg over lean/WeilConjectures and lean/Sheaf for the item id: no match. Concept
  searches for nodal, pointBlowup, blowup towers, minimum length and minimal comparison
  found CommonMarkedNodalModel (whose proof discusses this argument, but whose statement
  is a different common-model existence result), SurfacePointBlowupData, and the general
  OrdinaryBlowupTower. The latter two interfaces are reused, not duplicated.
- Read the actual dependency declaration signatures and docstrings, including the
  definitions of the local ring completion and the ordinary double point. Read the
  source proof of Stacks resolve.tex lemma-birational-regular-surfaces and
  lemma-factor-through-contraction. This item is explicitly an agent refinement,
  not a verbatim assertion of either Stacks lemma. No statement fault found.

Validation uses only the prescribed scompile.py and deliver2.py wrappers.

## Second reading by Q104

The dispatcher explicitly requires this worker to run without other agents. This
section records a separate rereading by this worker; the maintainer supplies the
independent review. I checked the node against the completed signature: both models
retain integrality, regularity, dimension two, H-projectivity, flatness and finite
presentation. Nonempty reduced pure-dimensional nodal fibres are explicit and do not
require connectedness. Smooth generic fibres, the fixed K-isomorphism, both S-projections,
the generic compatibility and minimum over all competitors are present. Each centre
ideal equals the reduced point ideal. The conclusion separately records smoothness,
finiteness and separability using the canonical map from the same trait residue field.
The zero-length case is included. A draft accidentally used the general separability
predicate available only through a private proof import; this was replaced with
Mathlib's `Algebra.IsSeparable`, the direct finite algebraic separability notion.
No node statement correction or new definition node is needed.
