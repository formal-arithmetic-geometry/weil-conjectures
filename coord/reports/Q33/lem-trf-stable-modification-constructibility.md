## Worker report

The module `Sheaf.TraceFormula.StableModificationConstructibility` states
`AlgebraicGeometry.stable_modification_constructibility`.  It introduces an integral,
Noetherian base scheme `S`, a point `η` with `IsGenericPoint η Set.univ`, multipointed
curves `X` and `Y`, a morphism `f : Y.Hom X`, and the hypothesis
`f.IsEtaModification (S.fromSpecResidueField η)`.  The latter is the recorded canonical
notion of a pair of proper maps, each an isomorphism over schematically dense opens
and after the generic-fibre base change.

The conclusion supplies two subsets `Cₛ Cₜ : Set S`, both with
`Topology.IsConstructible`.  For every `s : S`, membership in `Cₛ` is rendered by
`((MultipointedPair.ofCurve Y).baseChange (S.fromSpecResidueField s)).IsSemistable`.
This uses the existing semistability predicate, which expands to the nodal completed
local-ring condition, etale marking, and smooth marked points on the ordinary fibre.
The existing predicate itself takes its chosen algebraic-closure geometric fibre. This retains the etale and smooth marking
conditions over the residue field exactly. Membership in `Cₜ` is rendered by the
conjunction of the same semistability
condition and `MultipointedPair.HasGeometricStability` for the base-changed source and
target pairs.  The comparison morphism is the canonical `Over.pullback` map induced by
`f.curve`; the source and target are the canonical base-changed slice objects. Thus
its stability clause is exactly the absence of a
contracted projective-line component with at most two special points.

The dependency declarations used are:

- `AlgebraicGeometry.IsIntegral` from `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.MultipointedCurve` from `Sheaf.TraceFormula.MultipointedCurve`.
- `AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`, as used by
  `AlgebraicGeometry.MultipointedCurve.Hom.IsEtaModification`.
- `CategoryTheory.Limits.pullback` and `Orgogozo.geometricPoint` for the recorded geometric
  fibre construction.
- `AdicCompletion` from `Mathlib.RingTheory.AdicCompletion.Basic` and `MvPowerSeries`
  from `Mathlib.RingTheory.MvPowerSeries.Basic` occur in the existing ordinary-double-point
  predicate; they are reused without redeclaration.
- `AlgebraicGeometry.Etale` and `AlgebraicGeometry.Smooth` occur through the existing
  `MultipointedPair.IsSemistable` predicate.
- `Topology.IsConstructible` from `Mathlib.Topology.Constructible`.
- `AlgebraicGeometry.MultipointedPair`, `MultipointedPair.baseChange`,
  `MultipointedPair.ofCurve`, `MultipointedPair.IsSemistable`, and
  `MultipointedPair.HasGeometricStability` from
  `Sheaf.AlgebraicGeometry.SemistableMultipointedPair`.
- `AlgebraicGeometry.MultipointedCurve.Hom.IsEtaModification` from
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification`.

Edge cases checked: the marking may be empty; smooth geometric fibres satisfy the
semistability predicate vacuously at nonsingular points; the stable predicate counts
distinct special points on the component; empty fibres are handled by the
existing predicates; and no properness, generization stability, or global
semistability hypothesis is added beyond `hf` and the displayed fibrewise clauses.
The `η` generic-point binder is retained explicitly as required by the source statement.

Searches made:

- `msearch.py ... leanfinder "The semistable and stable geometric fibre loci of a proper modification of multipointed curves are constructible"`:
  only general constructible-image and base-change hits; no marked-curve theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.isConstructible_image, AlgebraicGeometry.Etale"`:
  zero hits; no match.
- `msearch.py ... grep "constructible.*(semistable|stable|nodal|exceptional)|exceptional.*component" Mathlib/AlgebraicGeometry`:
  zero hits.
- `msearch.py ... leansearch "The semistable and stable fibre loci of a proper modification of a multipointed relative curve are constructible"`:
  eight hits, including `Topology.IsLocallyConstructible`, general specialization/
  generization criteria for constructible subsets and properness definitions; no match.
- `rg` over `WeilConjectures/` and `lean/Sheaf`: no declaration for this constructibility
  theorem; the closest existing declarations are the reusable geometric predicates listed
  above.

The item statement is unchanged. Its statement dependencies gain the already landed
`def-trf-semistable-multipointed-pair` and `def-trf-multipointed-curve-modification`, since
these supply the existing predicates used in the signature. No new nodes or dependency
modules were needed. The generic isomorphism is taken along the canonical residue-field
point `S.fromSpecResidueField η`.

Available proof dependencies are imported with ordinary imports: FlatFibreEtaleNeighbourhoods,
SmoothAtPointFibreCriterion, ReducedInducedClosedSubscheme, SemistableMarkedBaseChange,
GenusZeroSmoothProperLine and ProjectiveLineGenusZero, plus Mathlib's immersion theorem.
Mathlib Noetherian and constructibility modules supply the remaining Mathlib leaves.
The three geometric proof nodes with no recorded declaration (nodal-open-locus,
contracted-component-generic-data and nodal-normalization-adjunction) cannot yet be imported;
their precise role is retained in the seven-step proof docstring.

Source checked directly: [Temkin §1.2 and Lemma 5.1(ii)](https://arxiv.org/pdf/0707.3953v3),
printed pp. 2 and 34. The paper's modification definition requires both the target open and
its source inverse image to be schematically dense, as in the reused predicate; its geometric
exceptional-component condition matches the existing stability predicate. The proof of
Lemma 5.1(ii) treats semistability and then exceptional components by constructibility.
The node's shorter phrase about schematic density only explicitly names the target open.
The reused interface also asks that its source inverse image be schematically dense,
as the paper does. Under the present hypotheses this is equivalent: a proper map
isomorphic on the generic fibre is an isomorphism over a target open containing that
fibre (the finite-presentation isomorphism-locus criterion). Enlarge the supplied
isomorphism open by this open. Its source inverse image contains the entire generic
fibre, which is schematically dense since the source is flat over the integral base.
Thus this interface does not impose a new mathematical restriction.

The module compiled cleanly with `scompile.py`, with the single theorem's proof `sorry`.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
