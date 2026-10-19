## Worker report

This is an existing-declaration delivery. All three predicates introduced by
`rem-dl-a1-conventions` already exist, so no module or new definition is delivered.
The primary declaration is
`AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant` in
`WeilConjectures.DeligneLaumon.AffineLine.Defs`, lines 62–76 of the source read.
That module also defines `AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`
(lines 78–103) and publicly imports `WeilConjectures.WeilSheaf.Defs`, which
publicly imports `WeilConjectures.WeilSheaf.Category` and hence
`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse` (lines 333–345).
All three full names are recorded in `lean.declarations`.

Read the complete item, its source
`main-20261015/blueprint/sec-deligne-laumon-a1/sk-d-dl-a1-setup/rem-dl-a1-conventions.md`,
and every statement-dependency node, including its recorded Lean signature and
source docstring. The live `AffineLine.Defs` source was confirmed with
`scompile.py --source`. The upstream representation-equivalence module is
absent from the older local checkout, so its current declaration was read with
`scompile.py --source WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation`.
Its closed audit names `AlgebraicGeometry.WeilGroup.exists_equivalence_fundamentalRep`;
absence of a separate `lean` record does not mean this prerequisite is unstated.

Clause and hypothesis matching:

- The finite field is the parameter `{k₀ : Type u} [Field k₀] [Finite k₀]`.
  The prime is `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
  Schemes carry `[U.Over (Spec (CommRingCat.of k₀))]`, and the open immersion
  also carries `[j.IsOver (Spec (CommRingCat.of k₀))]`. These are precisely the
  finite-field and coefficient-prime assumptions. The specified `q` is its
  cardinality and does not occur separately in the three new predicates.
  The general existing predicates specialize to a dense open of the affine
  line; density is not an extra requirement for the meanings of the predicates.
- `A₀` is the existing `AlgebraicGeometry.affineLine k₀`; `A` is its
  `Scheme.Hom.geometricFiber`. A prime on `A₀` denotes a second copy, with no
  separate notion to define. `ProjectiveLine.affineChart (Spec (.of k₀))`
  is the standard inclusion used literally in `IsUnramifiedAtInfinity`.
  The affine-space and standard-chart dependencies supply these conventions.
- Cohomology is geometric and Frobenius is geometric: the existing `WeilSheaf`
  carrier is an adic sheaf on the geometric fibre, and its Weil structure is
  `Fr*F ≅ F`, with `Fr` the geometric Galois Frobenius. Neither arithmetic
  Frobenius nor a sheaf on the arithmetic fibre is substituted. The four
  cohomology constructions are supplied by the recorded cohomology dependency;
  this node does not define another cohomology functor.
- Punctual purity means the dependency's `SfIsPunctuallyPureOfWeight`: its body
  is `∀ y α, SfPunctualEigenvalue ... F y α →
  ‖iota α‖ = (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)`.
  Replacing the equality in that condition with `≤` is exactly the punctual
  bound mentioned by this conventions node. It is not a claim that this
  inequality defines the finite-filtration predicate `SfIsMixedOfWeightsAtMost`.
  The coefficient embedding `iota` and real weight `w` belong to this existing
  weight convention, not to the three independent predicates being attached.
- Twists use the existing Tate construction; `tateTwist_weight_shift` gives
  `w - 2 * n`. At `n = -1` this is `w + 2`. This node introduces neither a
  new twist nor an additional twist theorem.
- Irreducible lisse is literally
  `F.IsLisse ∧ ¬ IsZero F ∧ ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ F),
  Mono i → G.IsLisse → IsZero G ∨ IsIso i`.
  The first two conjuncts are lisseness and nonzeroness. Quantifying over
  monomorphisms from lisse Weil sheaves is exactly quantifying over lisse Weil
  subsheaves. `IsZero G` is the zero subsheaf, and `IsIso i` says that its
  inclusion is all of `F`. There is no `Simple F` assumption in the category
  of all constructible Weil sheaves. The representation interpretation is the
  separately recorded exact fibre equivalence and its canonical Weil action.
- The explanatory nonsimplicity paragraph uses the existing extension by zero,
  its restriction counit, its inside/outside stalk formula, and conservative
  geometric stalks. It adds no fourth definition or theorem to this definition
  node. In particular the positive-rank component qualification in the node is
  retained: the chosen point must not lie in a component of rank zero.
- `j_*F` means ordinary direct image, furnished by the recorded
  `qbarCurveOrdinaryPushforward` and the retained `curveWeilMiddleExtension`
  realization. Boundary inertia invariants and the perverse characterization
  belong respectively to `lem-wf-boundary-stalk-invariants` and
  `lem-dl-a1-curve-intermediate-extension`. The latter's
  `qbarCurveIntermediateExtension` states perversity, absence of boundary
  subobjects/quotients, the unique normalized comparison, naturality and Weil
  compatibility. No use is made of the derived category of Weil sheaves to
  interpret that perverse intermediate extension.
- Unramified at infinity is the existing `IsUnramifiedAtInfinity F j`.
  Writing `ι` for the standard chart, it asks for an open `W` with
  `ι ⁻¹ᵁ W = j.opensRange` and `ι.opensRange ⊔ W = ⊤`, and a Weil sheaf
  `G` on `W` with `G.IsLisse` and `Nonempty (j'^*G ≅ F)`. The preimage equality
  identifies the affine part with `U₀`; the covering condition includes the
  unique missing point at infinity, so `W` is exactly `U₀ ∪ {∞}`. The map
  `j'` is the canonical open-immersion lift of `j ≫ ι` through `W`, not an
  arbitrary restriction map. The isomorphism is in the Weil-sheaf category.
  This definition also makes sense without an explicit `F.IsLisse` binder:
  a restriction of the lisse extension is lisse. The item only uses it on
  lisse `F`. Its inertia interpretation is supplied by the separately stated
  `lisse_extension_iff_trivial_inertia`, applied to that open curve.
- Geometric constancy is literally `∀ V, ConnectedSpace V → ∃ n : ℕ,
  Nonempty ((V.ι)^*ᵃ[l].obj F.obj.carrier ≅
  ⨁ fun _ : Fin n ↦ ProEtale.AdicSheaf.unit l V.toScheme)`.
  Here `V` ranges over the opens of the geometric fibre, the pullback forgets
  the Weil structure, and the finite biproduct of units is precisely the
  finite direct sum of the constant adic coefficient sheaf required by the
  node's last sentence. It requires no Frobenius-equivariant trivialization.
  For connected `U`, taking `V = ⊤` says its geometric monodromy is trivial;
  the Frobenius module may be any invertible operator.

Presentation conventions: these existing three definitions use the upstream
adic-sheaf realization of constructible Weil sheaves, its canonical geometric
algebraic closure, and `PadicAlgCl l`. The item's existing inertia theorem,
canonical fundamental representation and Tate-weight theorem use this same
realization. The recorded fixed-pair constructible-heart interface is retained
for the cohomological/perverse clauses and the arbitrary coefficient-closure
weight predicate. Choosing a model of the two algebraic closures is not an
extra mathematical hypothesis, and no comparison between a derived category
of Weil sheaves and fixed pairs in a geometric derived category is asserted.
This record attaches existing sheaf predicates; it does not supply a new
transport functor between these two Lean presentations.

Dependency declarations read and used for the clause matching (module; name):

- `Sheaf.Paper.FiniteFieldFiber`; `WeilConjectures.FiniteFieldDatum`,
  `.geometricFiber`, `.CoefficientDatum`.
- `Mathlib.AlgebraicGeometry.AffineSpace`; `AlgebraicGeometry.AffineSpace`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`;
  `AlgebraicGeometry.ProjectiveLine.TwistData` (and the standard chart in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`).
- `Sheaf.Paper.CommonStageCompactWeilCohomology`;
  `WeilConjectures.commonStageCompactWeilCohomology`,
  `adicOrdinaryCohomology`, `adicCompactCohomology`, with the publicly retained
  ordinary/compact coefficient and Weil-complex interfaces.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`;
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.SfWeilSheafComplex`; `WeilConjectures.sfWeilComplex`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilFrobeniusPullback`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`;
  `AlgebraicGeometry.Scheme.LisseIntegralSheafOfUniverses`, retaining
  `Sheaf.Paper.LisseAdicSheaves` and its rational/algebraic interfaces.
- `Sheaf.Paper.AdicPunctualWeights`;
  `WeilConjectures.SfPunctualEigenvalue`, `SfIsPunctuallyPureOfWeight`.
- `WeilConjectures.WeilSheaf.TateTwist`;
  `AlgebraicGeometry.WeilSheaf.cyclotomicUnit`, `tateTwistSheaf`,
  `AlgebraicGeometry.WeilComplex.tateTwist` (the latter is not used as a
  replacement for a fixed-pair complex).
- `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift`;
  `AlgebraicGeometry.WeilSheaf.tateTwist_weight_shift`.
- `Sheaf.Paper.GaloisLisseRepresentations`;
  `AlgebraicGeometry.Scheme.galois_lisse_representations`.
- `Sheaf.Paper.CanonicalWeilFundamentalRepresentation`;
  `AlgebraicGeometry.WeilGroup.canonicalFundamentalRep`.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation`;
  `AlgebraicGeometry.WeilGroup.exists_equivalence_fundamentalRep` (closed audit).
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`,
  `openImmersionLowerShriekUpperStarAdjunction`, `openImmersionLowerShriekAdjunction`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`;
  `AlgebraicGeometry.Etale.openImmersionLowerShriekCompUliftSheafFiberIso`,
  `isZero_uliftSheafFiber_openImmersionLowerShriek_obj`.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`;
  `AlgebraicGeometry.Scheme.isConservative_pointSmallEtale`, together with
  `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms`
  (`Mathlib.CategoryTheory.Sites.Point.Conservative`),
  `CategoryTheory.JointlyReflectMonomorphisms.mono_iff`
  (`Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`) and
  `AddCommGrpCat.mono_iff_injective` (`Mathlib.Algebra.Category.Grp.EpiMono`).
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary`;
  `AlgebraicGeometry.WeilGroup.BoundaryChart.boundaryStalkEquivInvariants`
  and its Frobenius compatibility (the primary recorded finite-local-constancy
  lemma alone is weaker; the record lists the full comparison as well).
- `Sheaf.Paper.CurveIntermediateExtension`;
  `WeilConjectures.qbarCurveIntermediateExtension`.
- `Sheaf.Paper.QbarCurveOrdinaryImage`;
  `WeilConjectures.qbarCurveOrdinaryPushforward`, `qbarCurveShiftedOrdinaryImage`.
- `Sheaf.Paper.LisseExtensionInertia`;
  `AlgebraicGeometry.WeilSheaf.lisse_extension_iff_trivial_inertia`.

Edge cases checked by reading the definitions: the zero sheaf is geometrically
constant with `n = 0` and extends as zero, but fails irreducible lisse through
`¬ IsZero F`. A rank-one constant geometric sheaf with a nontrivial Frobenius
scalar remains geometrically constant. A constant higher-rank sheaf is judged
irreducible using Frobenius-stable subspaces, not just geometric constancy.
On disconnected geometric fibres the definition quantifies over every
connected open, so it does not impose a common rank on different components.
When `j` is the whole affine line, the only possible `W` is the projective
line; extension at infinity is still a substantive condition (e.g. a
nontrivial Artin–Schreier local system is ramified there). A Kummer local
system on the punctured line can fail it as well. No characteristic is
excluded except the specified `l = char k₀`. The universe `u` is arbitrary.

Searches (2026-10-18):

- `msearch.py ... leanfinder "Lisse Weil sheaf geometrically constant unramified
  at infinity irreducible lisse"`: eight results concerning formally
  unramified morphisms and unramified algebra loci; none matches.
- `msearch.py ... loogle "AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant,
  AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity,
  AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse"`: no Mathlib hits,
  unknown first identifier.
- `msearch.py ... grep
  "IsGeometricallyConstant|IsUnramifiedAtInfinity|IsIrreducibleLisse"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "geometrically constant lisse Weil sheaf
  irreducible unramified at infinity"`: eight hits, including generic
  constant-sheaf predicates and number-field infinite-place ramification;
  none defines these Weil-sheaf predicates.
- `rg -n` for the three predicate names in upstream `WeilConjectures` and
  project `lean/Sheaf`: exact upstream definitions in `AffineLine/Defs.lean`
  and `WeilSheaf/Category.lean`; the project's dense-open theorem already
  consumes the upstream irreducible-lisse predicate.
- `grep -rn "rem-dl-a1-conventions"` in upstream `WeilConjectures`: the exact
  irreducible-lisse definition has this blueprint tag. The node's own
  `lean_candidates` independently names all three definitions found above.

Validation: the sandbox scratch probe imports only
`WeilConjectures.DeligneLaumon.AffineLine.Defs` and checks all three fully
qualified declarations with `autoImplicit false`. It passed `scompile.py`
against both sandbox and published-library environments without warnings.
The scratch probe is not a delivered module. The delivery tool independently
checks all three names again. No statement correction, new node, dependency
repair, proof, or additional sorry is introduced. No statement dispute found.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
