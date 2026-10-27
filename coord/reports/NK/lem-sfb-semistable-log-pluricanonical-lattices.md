# Semistable logarithmic pluricanonical lattices

## Worker report

The module `Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices` states
`AlgebraicGeometry.semistable_log_pluricanonical_lattices`. Its only postponed
proof is this named theorem. Three real helper definitions expose the actual
restriction of tensor-power sections, the homogeneous algebra laws, and the
fundamental-class normalization of the generic comparison. They are parts of
this node's canonical comparison, not new independent notions. No new DAG nodes
or dependency repairs are required. The original node is unchanged except for
`lean`.

The earlier worker's claim that the assignment was superseded confused stages:
N5's reviewed landing is explicitly a stage-1 split and supplies no Lean record.
The node still requires this stage-2 statement. N5's proof and dependency records
are retained verbatim.

### Hypotheses and objects

| Node clause | Lean rendering |
| --- | --- |
| DVR R, fraction field K | `R K : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]`. |
| S = Spec R | `Spec (.of R)` throughout. |
| Generic base inclusion | `η : Spec (.of K) ⟶ Spec (.of R)` and `hη : η = Spec.map (CommRingCat.ofHom (algebraMap R K))`. This equation introduces a name for the prescribed morphism; it adds no restriction on R or K. |
| Two projective flat finitely presented families | `P Q : MultipointedCurve (Spec (.of R))`, with `[IsHProjective P.x] [IsHProjective Q.x]`. `MultipointedCurve.flat_X`, `lfp_X`, `qc_X`, `qs_X` encode flatness and finite presentation; projectivity supplies the required separatedness. |
| Nonempty connected one-dimensional nodal geometric fibres | `hPnodal`, `hQnodal : HasNodalGeometricFibres ...`. This exact existing predicate includes `ConnectedSpace` (hence nonempty), dimension one, and the completed nodal local-ring condition over every algebraically closed field. |
| Reduced pure one-dimensional geometric fibres | `hPgeom`, `hQgeom` assert `IsReduced (pullback ... t) ∧ (...).IsPureDimension 1` for every geometric point. |
| n disjoint sections, n may be zero | `n : ℕ`, `p`, `q` are isomorphisms from the coproduct of `Fin n` copies of the base to the marking schemes. `hp`, `hq` fix their structure morphisms. The actual closed immersions `P.i`, `Q.i` identify these with disjoint sections. Conversely disjoint sections give exactly this presentation. |
| Sections in the relative smooth locus | `hPsmooth`, `hQsmooth`, evaluated on every point of the marking schemes. |
| Canonical dualizing line and Cartier divisor conventions from reconstruction, without positivity | `D`, `E : MarkedNodalDualizingDegreesData ...` are arbitrary normalized representatives of the canonical data supplied by the recorded reconstruction theorem's unconditional existential. No positivity, stability, normality, or smooth-generic hypothesis occurs. The data include the actual Cartier marking ideals, canonical dualizing modules and fundamental classes. |
| L_i = omega_i(D_i) | `markedNodalLine P D.omega` and `markedNodalLine Q E.omega`, literally omega tensor the dual of the actual marking ideal. |
| Any K-isomorphism of generic curves | `v : pullback P.x η ≅ pullback Q.x η`, with `hv` asserting it is over Spec K. |
| Sending sections according to a permutation | `d` is a K-isomorphism of the generic marking schemes, with `hd` and `hmarks` the structure and marking squares. Each marking is a split union of n copies of Spec K, so its K-isomorphisms are exactly permutations; this neither assumes an extension of v nor adds a labeling constraint. |

The common scheme/field universe follows the existing scheme and reconstruction
interfaces. It excludes no geometric case: fraction fields and algebraic closures
of rings in this universe have representatives in the same universe. All universes
and variables are explicitly bound; automatic implicit binders are disabled.

### Conclusions, canonical maps, and algebra operations

The conclusion supplies a line isomorphism `c` between the pullback by `v.hom` of
the actual second generic line and the actual first generic line. It requires
`IsNodalLogGenericComparison P Q D E η v c`.

This predicate is not a bare existence of a line isomorphism: it pulls back the
existing `nodalLogFundamental` maps and compares them through the canonical
`relativeDifferentialsPullbackMap`. The two resulting differential maps on the
common generic curve agree on every `da` over every open. Their source structure
maps are equal by `hv` and the pullback squares; comparison on `da` expresses the
canonical identification without an opaque transport. The base map is localization,
so relative differentials over R and over K agree. On the smooth unmarked generic
locus the log fundamental class is an isomorphism. That locus is dense in every
component of the reduced nodal curve, so this condition fixes c on the whole line.
Thus a nontrivial scalar rescaling cannot give another permitted comparison.
No arbitrary map, existence-choice definition, or additional comparison hypothesis
is used.

`nodalLogPowerRestriction g L m` is the existing `nodalLogPullbackSection` with the
identity comparison on `g*L`. That existing construction applies the actual
`tensorPullbackSection` (the section `1 ⊗ s`) followed by the canonical
`boundaryPullbackPowIso` and the identity tensor-power comparison. Its domain and
codomain are the actual `SectionRingComponent` global sections.

For each `m : ℕ` the conclusion asserts exactly:

1. Injectivity of the restriction for P.
2. Injectivity of the restriction for Q.
3. The image under the normalized generic pullback of `Set.range` of Q's restriction
   equals `Set.range` of P's restriction. This is the displayed u-star image equality,
   with the contravariant direction Q to P.

The three `NodalLogSectionAlgebraLaws` conjuncts apply respectively to P's restriction,
Q's restriction, and generic pullback. They express addition, R-linearity under the
actual structure maps on functions, multiplication of every pair of homogeneous
sections via the recorded `GradedMonoid.GMul.mul`, and the degree-zero
`GradedMonoid.GOne.one`. Multiplication and the unit are the section-ring operations
of `def-sc-invertible-section-ring`, not independently chosen operations. These
clauses assert closure of each image under the R-algebra operations and compatibility
of the equality with those operations. Equivalently they identify the direct sums
of these images as graded R-subalgebras. No finite-generation claim is added.

### Recorded dependencies used

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`, from
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, with its required domain instance.
- `def-pc-field-extension`: `Algebra` and `algebraMap`, from
  `Mathlib.Algebra.Algebra.Defs`; fraction-field localization additionally uses
  `IsFractionRing` from `Mathlib.RingTheory.Localization.FractionRing`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `lem-sfb-nodal-log-canonical-reconstruction`:
  `exists_nodal_log_canonical_reconstruction`, `nodalLogFundamental`,
  `nodalLogPullbackSection`, from
  `Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction`. Its public dependencies
  give the exact `MultipointedCurve`, `MarkedNodalDualizingDegreesData`,
  `markedNodalLine`, `HasNodalGeometricFibres`, and canonical differential interfaces.
  The theorem is stated for arbitrary representatives of its unconditional canonical
  data, so does not require ampleness or invoke its Proj conclusion.
- `def-pc-divisor-line-bundle`: the recorded
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` and the actual
  dual ideal expression from `WeilConjectures.AlgebraicGeometry.EffectiveCartier`.
  `markedNodalLine` uses exactly that expression.
- `def-sc-invertible-section-ring`: `Scheme.Modules.SectionRingComponent`,
  `sectionRingGMul`, `sectionRingGOne`, and `InvertibleSectionRing`, from
  `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`.

All available recorded proof dependencies are imported without `public`: invertible
modules, flatness, depth, depth-two Hartogs, fibre-stalk quotients, flat tensor
injections, Noetherian permanence, flat local depth formula, and the nonzerodivisor
lemma. The common-nodal-model and logarithmic-dualizing-pullback proof prerequisites
are still unstated nodes with no Lean record or module, so have no module to import.
Neither is needed to type the statement. They remain explicit in the docstring's
proof plan, retaining the original DAG proof dependencies unchanged.

### Sources and edge cases

I read the node's full statement, proof, source, statement dependencies, and all
recorded dependency declarations and their docstrings. I read Stacks
`moduli-curves.tex`, `lemma-unique-stable-model` (Tag 0E97), and the N5 split report.
The module retains the source caveat: 0E97 treats smooth unmarked generic curves and
is motivation rather than a citation for this stronger prerequisite. The agent
formulation and de Jong section 3.8 motivation remain explicit. This worker adds
no unsupported assertion that the Stacks theorem already proves the marked case.

- n=0: the marking coproduct is empty, and the actual dual ideal twist is the unit.
  No positivity or nonempty marking is required.
- m=0: `boundaryPullbackPowIso` uses the canonical structure-module comparison;
  `boundaryTensorPowIso` is the identity. Unit and coefficient laws are explicit,
  so arbitrary rescaling in degree zero is excluded.
- Rational unmarked components and unstable tails remain allowed. For the projective
  line with no markings, positive tensor powers of omega have zero global sections,
  and the asserted image equality includes these zero groups.
- Persistent generic nodes are allowed: no total-space integrality or normality
  instance, no smoothness assumption on the generic fibre, and no definition using
  the function field of the total curve appears. The canonical-comparison argument
  uses the dense smooth unmarked locus of a reduced nodal curve, not total normality.
- A nontrivial permutation of markings is covered by d. No ordering or preservation
  of each label individually is imposed.
- Identity generic isomorphisms and identical models give the identity comparison
  between the corresponding normalized representatives, including all tensor powers.
- Blowup sanity checks agree with the node: an unmarked smooth centre has log
  discrepancy one; a marked smooth centre has discrepancy zero; resolving
  xy=pi^e is crepant. None demands stability or a smooth generic fibre.
- Arbitrary residue characteristic is retained. No characteristic restriction or
  smoothness over a perfect field is introduced.

No counterexample, statement correction, or STATEMENT-DISPUTED issue was found.

### Searches

Required wrapper searches were run for this item, rather than inferred from earlier
workers' logs:

- LeanFinder: "Semistable marked curves over a discrete valuation ring have identical
  logarithmic pluricanonical section lattices under a generic isomorphism". Eight
  hits concerned minimal Weierstrass equations/good reduction; none states this node.
- Loogle: `"AlgebraicGeometry", "dualizing"`. Zero hits.
- Mathlib grep: `pluricanonical|semistable.*canonical|canonical.*semistable` in
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: "Log canonical section rings of semistable marked curve models over a
  discrete valuation ring are invariant under changing the model". Eight hits,
  chiefly Weierstrass integral/minimal models, plus unrelated structure-sheaf and
  surjective-on-stalks results. No match.
- Read-only project/upstream ripgrep for the item id, `pluricanonical`, semistable
  canonical/lattice variants and proposed helper names. No existing statement or
  helper was found. A reference to the node in `StablePointedIsomFinite.lean` is
  a proof-plan reference, not a declaration. The recorded section-ring and nodal
  reconstruction interfaces were reused rather than copied.

### Validation

The prescribed `scompile.py NK lem-sfb-semistable-log-pluricanonical-lattices`
compiled the module both as a sandbox probe and under its actual library module
name, cleanly: 8.0 s and 10.9 s respectively, no errors or warnings. Definitions
contain real terms and the sole theorem has `sorry`. The prescribed delivery dry run
passed server preflight and compilation (dry-run commit ad16d25caac).

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
