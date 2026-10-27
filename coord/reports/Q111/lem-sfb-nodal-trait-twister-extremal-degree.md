## Worker report

The module `Sheaf.AlgebraicGeometry.NodalTraitTwisterExtremalDegree` states
`AlgebraicGeometry.nodal_trait_twister_extremal_degree`. Its only theorem has proof
`sorry`. No definition or auxiliary theorem is added. The node's statement, dependencies,
proof, and source are unchanged; only its `lean` record is supplied.

Source read: Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and Maps*,
arXiv:0810.2340, Section 3.3, proof of Proposition 10, printed p.16,
https://arxiv.org/pdf/0810.2340. The source chooses an extremal component union and counts
its boundary zeros. As the already reviewed node explains, its extension to singular total
spaces and persistent nodes uses the six-step section-specialization argument, rather than
assuming that individual vertical components are Cartier. The declaration docstring carries
all six steps, the relevant node names, and the Stacks source tags. The source's original
vertical-divisor argument is not imposed as an extra hypothesis.

Hypothesis and conclusion correspondence:

- A DVR R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`, using the exact Mathlib class extending local PID with
  nonzero maximal ideal. No completeness or excellence is imposed.
- Its fraction field is `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`.
  The generic point is `Spec.map (CommRingCat.ofHom (algebraMap R K))`.
- The named family is `{X : Scheme.{u}} (f : X ⟶ Spec (.of R))`, with
  `[IsProjective f] [Flat f] [LocallyOfFinitePresentation f]`. Projectivity supplies
  quasi-compactness and quasi-separatedness, so local finite presentation is equivalent
  here to finite presentation. The projective class is the project's existing one.
- Nonempty connected nodal geometric fibres are exactly `hnodal :
  HasNodalGeometricFibres f`. Reading that definition verifies that `ConnectedSpace`
  includes nonemptiness, the geometric dimension is one, and nonsmooth completed stalks
  have the two-variable node ring. It quantifies over every algebraically closed field
  and every geometric base point in the scheme universe.
- Reducedness and pure dimension one, as in the recorded reconstruction family's
  hypotheses, are `hgeometric`. There are no markings, dualizing data, positivity
  conditions, total-space smoothness, integrality, normality, or Cartier components.
- The invertible module is `(T : X.Modules) [T.IsInvertible]`, with the recorded
  `Scheme.Modules.IsInvertible` definition, not a new line-bundle predicate.
- Generic triviality is `hgeneric : Nonempty (...)`, an isomorphism between the actual
  `tensorPullback` of T to `pullback f (Spec.map ...)` and its structure module.
- The algebraic closure of the residue field is `(Ω : Type u) [Field Ω]
  [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsAlgClosure (IsLocalRing.ResidueField R) Ω]`. The closed geometric point is the
  spectrum of the composite of `IsLocalRing.residue R` with this algebra map.
- Any geometric closed fibre is represented by `(C : Scheme.{u}) (i : C ⟶ X)
  (p : C ⟶ Spec (.of Ω))` and `hC : IsPullback i p f` of that composite spectrum map.
  This accepts every cartesian model of the specified fibre, including the chosen
  `Limits.pullback`; `hC.isoPullback` identifies it canonically with that chosen model.
  It neither restricts C by an independent hypothesis nor replaces it by an unrelated
  curve. Its line restriction is precisely `(Scheme.Modules.tensorPullback i).obj T`.
- The first alternative is `Nonempty (... ≅ SheafOfModules.unit C.ringCatSheaf)`.
- The second alternative chooses `S : Finset (irreducibleComponents C)`. `S.Nonempty`
  says the subcurve is nonempty (each irreducible component is nonempty).
  `(⋃ Z ∈ S, Z.1) ≠ Set.univ` says it is proper. C is Noetherian, so every reduced
  component union occurs in this representation. A finite component union is closed
  and has its unique reduced induced closed-scheme structure, already provided by the
  project's vanishing-ideal subscheme construction. Thus using its component set rather
  than adding a redundant choice of the same reduced scheme is exactly the node's Y.
  No connectedness of this subcurve is imposed.
- The intersection `(⋃ Z ∈ S, Z.1) ∩
  ⋃ Z : irreducibleComponents C, ⋃ (_ : Z ∉ S), Z.1` is the set Y intersected with
  its reduced complementary component union. On a nodal curve those intersection
  points are exactly its boundary nodes, one point per node, without self-nodes internal
  to either side. `Set.ncard` is k_Y. Its strict positivity also excludes the infinite
  set convention `ncard = 0`; geometric finiteness follows independently from nodality.
- The degree sum is `∑ Z ∈ S, markedNodalComponentDegree Ω
  (C.reducedNormalizationComponent Z) ... ... ((tensorPullback i).obj T)`.
  The two maps supplied to this existing helper are the canonical reduced-component
  inclusion and its composite with p. Unfolding the helper gives `Modules.degree Ω`
  of the pullback to the component's function-field normalization, with the induced
  Ω-structure. This is the degree convention in the node, not the degree on a possibly
  singular total-space divisor. The component normalization is constructed by the
  existing `reducedNormalizationComponent` and `Scheme.normalization` interfaces.
- The last two clauses are `(boundary.ncard : ℤ) ≤ normalizedDegreeSum` and
  `0 < boundary.ncard`, exactly `deg_Y(T|C) >= k_Y > 0`. Positivity over naturals or
  over integers is equivalent here.

Recorded statement dependency interfaces read and used:

- Mathlib `RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  full class signature and its local PID/nonfield docstring.
- `Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction`:
  `AlgebraicGeometry.exists_nodal_log_canonical_reconstruction`, its complete signature
  and fourteen-step docstring. Only its unmarked family hypotheses are used; the
  theorem is not turned into an assumption. Its public family/degree/normalization
  interfaces supply `HasNodalGeometricFibres`, `Scheme.IsPureDimension`,
  `markedNodalComponentDegree`, and `Scheme.reducedNormalizationComponent`.
  Their defining modules were opened as well (`NodalGeometricFibres`,
  `MarkedNodalDualizingDegrees`, and `ReducedNormalization`).
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree`, the existing difference of coherent Euler
  characteristics, used by `markedNodalComponentDegree`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, local triviality with the structure
  module on a neighbourhood of each point.

All stated proof dependencies are imported with plain imports (statement dependencies
use public imports). The recorded declarations include projective properness in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, Euler constancy and geometric
base-change equality in `Cohomology.DirectImage.BaseChange`, upper semicontinuity in
`Cohomology.DirectImage.Semicontinuity`, and flat-base-change cohomology in
`Cohomology.EulerChar`; `degree_weighted_irreducible_components`,
`nodal_normalization_adjunction`, `proper_curve_bundle_pullback_degree`,
`curve_section_degree_nonneg_and_pos`, `Scheme.smooth_connected_curve_local_rings`,
and `projective_base_change` are imported from their recorded Sheaf modules.
`Curve.RiemannRoch` supplies the degree/divisor formulas listed by the degree-base-change
node in addition to its main `EulerChar` module. No proof dependency is omitted.

Edge cases checked before writing: the empty geometric fibre is excluded by the existing
connected-space condition, and the empty subcurve by `S.Nonempty`; the full subcurve is
excluded separately. For an irreducible special fibre there is no nonempty proper subset,
so only triviality can occur, as the nonzero-section/total-degree-zero proof implies.
For two components meeting at one node, normalized degrees (1,-1) admit the positive
component as Y, and the inequality is sharp. With several intersection nodes they are
counted separately, while self-nodes contribute nothing to this cut. The trivial line
satisfies the first alternative. Disconnected proper subcurves are allowed. Empty branch
sets on individual normalized components cause no problem in proof step 6. No change of
characteristic, singular total-space condition, or generic smoothing condition appears.
Universes and every variable are explicitly bound; no file-local notation or instance,
let-binder, or hidden chosen geometric object is used.

Searches performed for an existing statement (all through the prescribed logged wrapper,
plus direct searches in the read-only project):

- LeanFinder: “A generically trivial line bundle on a flat proper nodal curve over a
  discrete valuation ring is trivial on the special fibre or has degree on a proper
  subcurve at least its number of boundary nodes”. Eight results, all concerning
  Weierstrass reduction/minimality/discriminants, not this theorem.
- LeanSearch: “line bundle trivial on generic fibre nodal curve trait subcurve boundary
  degree”. Eight results about trivial topological vector bundles and their
  trivializations; no algebraic nodal-trait theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.degree, IsDiscreteValuationRing`.
  Zero hits; the service reports the project-local degree name unknown. This is not
  treated as evidence that the project's degree is missing; its source was read directly.
- Mathlib grep: `twister|Twister|[Ss]ubcurve|boundaryNodes` in AlgebraicGeometry.
  Zero hits.
- Project grep of WeilConjectures and Sheaf with the same expression and the item id:
  existing nodal-subcurve geometry and the downstream balanced-limit proof plan occur,
  but no statement of this lemma. In particular the downstream balanced-limit module
  already defines a closed-point, component-degree and boundary notation. It is not
  imported here (it consumes this lemma), and none of those definitions is duplicated:
  the statement is written with existing primitive maps, component degree, and set unions.
- Further grep for `nodal_trait_twister_extremal_degree` in Mathlib, WeilConjectures,
  and Sheaf, and for `twister|extremal` in `dag/lean_names_upstream.json`: no declaration.
  Searches and source inspection found all the necessary notions; no new node or
  dependency-interface repair is needed.

No statement dispute or node correction is required.

## Second reading by Q111

No second worker was started, as required by the dispatcher brief. The maintainer's
independent review is the independent reading. In a fresh worker rereading, the node and
file were checked together: the DVR and fraction field, all three family properties,
nonempty connected reduced pure nodal geometric fibres, invertibility and generic
triviality, the residue-field algebraic closure and cartesian closed fibre, both
alternatives, nonempty proper component union, normalized degree sum, and positive
boundary count all have the correspondences above. No marking, positivity, smooth generic
fibre, Cartier-component assumption, or connected-subcurve restriction was introduced.
No mathematical mismatch was found in this rereading.
