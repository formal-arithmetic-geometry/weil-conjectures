## Worker report

The module `Sheaf.AlgebraicGeometry.GabberAbelianStageToricChart` states
`AlgebraicGeometry.GabberAbelianStage.exists_abelian_stage_toric_chart` with `sorry`.
It presents the local invariant-monoid diagrams by actual structures and prescribed
maps. All supporting definitions have real data; the only postponed theorem is
this node's theorem. No mathematical statement correction is made.

The existential `P : GabberModification.FourthProcedure` is shared between the
absolute modification and the relative local description. The first conjunct is
the simultaneous four-stage choice and output of the recorded absolute theorem.
The second describes only `P.tower`, not a reapplication of the first three stages.

Hypotheses, clause by clause:

- `X S : FineSaturatedLogScheme` uses the recorded fs small-etale-site log structures,
  including local Noetherianity. `[IsNoetherian S.scheme]`, `hS`, `hsep`, and `hlog`
  are the base's Noetherian, quasi-excellent, separated and log-regular hypotheses.
  Its boundary D is the complement of the log triviality locus; the statement
  never uses an additional choice of a closed subscheme structure on D.
- `[IsIntegral X.scheme]` is Mathlib's nonempty integral-scheme predicate.
  `hX : GabberModification.AbelianInput a Z` includes Noetherianity,
  quasi-excellence, separatedness, regularity, log regularity, tame action,
  abelian geometric inertia, strict normal crossings, G-strictness, the equality
  of boundary support with the log triviality complement, and freeness outside Z.
  Thus none of these hypotheses is replaced by an unconstrained predicate.
- `f : EtaleLogHom X S` and `f.IsLogSmooth` use the recorded log-smooth chart
  criterion. `(a.logMap g).CompEq f f` says the action is over S with trivial
  action on S, as equality of actual log composites, for every g.
- Every geometric point `x : Spec Ω → X.scheme`, with Ω algebraically closed,
  has a `LocalModel`; the quantification makes these neighborhoods cover X.

Conclusions, clause by clause:

- `inertia a x` is precisely the subgroup fixing the geometric point. The local
  action is by this subgroup; `inertX` uses its actual subgroup inclusion.
  `point_over`, `toX`, `strictX`, and `etaleX` give the pointed strict inert
  étale neighborhood. `toS`, `strictS`, `etaleS`, and `overS` give the compatible
  neighborhood of S. The final maps are the prescribed ordered comparisons
  `P.comparison`, including the final map back to the global fourth stage.
- `ToricData.N`, `exponent`, and `positive` give the exponent of that inertia.
  `Λ`, `cyclotomic`, `denominators`, `localization`, and `invertExponent` say
  exactly that Λ is a localization of the Nth cyclotomic integer ring with N
  inverted, equivalently a localization of Z[1/N, μ_N]. `rootsOfUnity N Λ`
  is Mathlib's subgroup of units whose Nth power is one.
- `Q`, `fsQ`, and `sharpQ` give a sharp fs base monoid. `LocalModel.baseChart`
  and `baseIsChart` make it a chart of the base neighborhood. `coefficient` and
  `baseMap_spec` normalize the map to Spec Λ[Q] by the actual structural map
  on every monomial, through the global-sections/spectrum adjunction.
- `P`, `coordinates`, `γ`, `injective`, `torsionFinite`, and `torsionUnit` give
  P = Z^t × N^r, the injective group-completion map, and exactly the finite
  invertible torsion subgroup of its cokernel. `ULift` only puts the explicit
  finite-coordinate monoids in the scheme's universe.
- `ToricData.Pbar` is P × N^s, with the actual inclusion `includeP`. The
  character map is `InvariantData.χ`. `ToricConstruction.diagonal` identifies
  the action on every monomial, including coefficient constants, with that
  character. Thus these are eigenvector coordinates, not unrelated characters.
- `invariantMonoid` is the actual multiplicative kernel of the composite
  Pbar → Pbar^gp → Hom(H, μ_N). `originalInvariantMonoid` is its preimage in P.
  These definitions are exactly Rbar = ker χ ∩ Pbar and R = Rbar ∩ P.
  `baseInvariant`, `baseMap`, and `includeOriginal` give the factorization from Q.
  `groupInjective`, `finiteIndex`, and `indexAnnihilator` give the lattice
  inclusion with finite index annihilated by a positive invertible integer.
- `ToricConstruction` identifies the original and enlarged schemes with
  Spec Λ[Pbar]. Their normalized charts are P and Pbar respectively.
  `RigidifiedQuotient`, `quotientAffine`, `quotient_spec`, and `quotientChart_spec`
  identify the invariant log quotient with Spec Λ[Rbar], including its actual
  monomial map and canonical log chart. `construction` is the existing
  `RigidifiedConstruction P.resolution`, so it remembers the actual resolution
  tower and its fs pullback, including ordered centers. This is the fourth
  stage specified by the absolute modification, not an arbitrary resolution.
- `RelativeModel.chartsCover` covers the resolved quotient by affine opens
  `ToricConstruction.Chart`. `ResolvedMonoid.coordinates` identifies Rbar'
  with Z^a × N^b. `groupIso` says that the group map induced by ν is bijective;
  hence it is an isomorphism. `ν_spec` identifies ν with the actual total
  resolution arrow, composed from that tower's arrows, not an arbitrary map.
- `bound : c ≤ b` and the natural number c give 0 ≤ c ≤ b. `retainedMonoid`
  consists of exactly those elements with zero exponent in coordinates j ≥ c.
  Through the displayed coordinates this is exactly Z^a × N^c inside Rbar'.
  `Chart.boundary` says precisely that the retained boundary is the union of
  the first c coordinate divisors. `chart_spec` normalizes its log chart by
  these same monomials, while `fullChart_spec` describes the enlarged log
  structure on the identical underlying resolved scheme.
- `ResolvedMonoid.retained` is ν(R) ⊆ R'. Its `baseMap` is the composite
  Q → R → Rbar → Rbar' with codomain restricted using this exact inclusion.
  `RelativeModel.chart_base` says its ring/scheme map is the actual map to the
  base. Every group map in the diagram is the Mathlib construction
  `Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp h)`
  applied to the displayed monoid map h; no independent group map is assumed.
- `affineSpace` and `affineSpace_over` identify Spec Λ[Rbar'] over Spec Λ[R']
  with Mathlib's affine space indexed by Fin (b-c), with equality of the
  structural projections, not merely an abstract scheme isomorphism.
- `LocalModel.etaleModel` and `strictToric` give the strict étale comparison
  with the ordinary base change of the original toric model over Spec Λ[Q].
  `quotientSquare`, `strictQuotient`, and `etaleQuotientModel` give exactly the
  strict étale neighborhood of the ordinary base change of the resolved
  quotient. `quotient_eq` identifies this quotient map with the map induced
  by the same ordered fourth-stage comparison. `finalSquare` supplies its
  structural map over the localized base.
- `finalIsQuotient` is the existing invariant-log-quotient predicate, including
  invariant rings, orbit fibers and invariant log sections. `finalAffine`
  identifies its scheme with the resolved enlarged quotient. `originalBoundary`
  says its pullback is exactly the inverse image of the original boundary,
  and `P.result` gives that boundary on the modified source. The comparisons,
  identity and composition laws, and independence of enlarged rigidification
  belong to the shared `FourthProcedure`. This identifies the local charts
  and their quotients with the globally glued fourth stage.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure.IsChart`, `EtaleLogHom`,
  `IsSaturatedLogBlowup`, `SaturatedLogBlowupTower`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogSmooth`, using
  `FSLogChart` and its finite invertible torsion and smooth comparison criterion.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, through the existing
  `GabberModification.QuasiExcellent` predicate on every affine open.
- `Sheaf.AlgebraicGeometry.GabberAbsoluteEquivariantModification`:
  `GabberModification.exists_absolute_equivariant_modification` and its public
  `GabberModificationData` provider: `FourthProcedure`, `FourStage`, `AbelianInput`,
  `Rigidification`, `RigidifiedQuotient`, `RigidifiedConstruction`, `Comparison`,
  `Inert`, `Tower.source`, `Tower.map`, and `FourStage.Output`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure`:
  `StrictEtaleLogBlowupProcedure` and `LogBlowupTowerOver`, via the landed
  public provider used by `GabberModificationData`. No dependency repair is delivered.
- `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`:
  `Algebra.GrothendieckGroup.lift` and `Algebra.GrothendieckGroup.of`. Their
  composition is written inline at all seven group-completion maps.
- Mathlib's `CyclotomicRing`, `IsLocalization`, `Monoid.exponent`, `rootsOfUnity`,
  `MonoidAlgebra`, monoid kernels and submonoids, group quotients and torsion,
  affine spectra, and `AffineSpace` are used directly.

The available module-compatible proof dependencies are imported without `public`.
The following old proof providers are unavailable or not module-compatible and
are left as named proof-plan dependencies rather than replaced by copies:
`GabberFixedLocusLogChart`, `InertEtaleQuotientComparison`,
`LocalCyclotomicGroupAlgebraSplit`, `TameInvariantsArbitraryBaseChange`,
`VeryTameLogQuotient`, `ToricMonoidComparison`, `FunctorialFanDesingularization`,
and `FunctorialLogBlowupEtaleDescent`.
The fixed-locus provider was also checked using the live-source wrapper, which
reported it unavailable. The functorial-fan provider's published artifact was
confirmed by the compiler to be non-module. The other unstated proof nodes remain
in the DAG and are named in the proof docstring. None supplies a type needed to
state this item: the existing fourth-stage diagram API suffices. All the node's
original proof and proof_deps fields are preserved.

Edge cases checked against the displayed data and the source:

- Trivial inertia has exponent one; no nontrivial-character or positive-rank
  hypothesis is imposed. The character-kernel definition then gives the entire
  monoid. The ambient acting group is not assumed abelian, only its inertia.
- t, r, s, a, and b may be zero. Empty boundary means the product of its
  coordinate monomials is one, so its zero set is empty.
- c = 0 gives exactly the unit-lattice retained chart; c = b omits no coordinate;
  b = 0 gives affine zero-space. `Fin (b-c)` and zero exponents include all three.
- A saturated tower may have length zero. `towerProjection` starts with the
  identity; it never takes a head of a nonempty list or requires a positive length.
- No flatness of the base map is assumed. The scheme comparisons use actual
  ordinary pullbacks, and strictness and the existing fs pullback construction
  are stated separately. The model and quotient descriptions retain the
  nonflat case justified by Reynolds averaging in the node's proof.
- Geometric points and schemes use universe u, with groups in independent v;
  finite-coordinate monoids are lifted to u. No equality of u and v is imposed.
  X is nonempty because the node assumes integral. An empty base admits no map
  from such X, so the quantified statement covers that case without extra data.

Searches for an existing declaration:

- `msearch.py leanfinder`, query "Tame abelian group invariant monoid toric charts
  log blowup": eight unrelated number-field unit/logarithm results; no match.
- `msearch.py loogle`, query "MonoidAlgebra, rootsOfUnity, Algebra.GrothendieckGroup":
  zero hits.
- `msearch.py grep`, query "invariant.*monoid|toric.*chart|abelian.*inertia" in
  Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py leansearch`, query "invariant monoid character kernel finite abelian
  group toric log blowup": eight hits, including `MonoidHom.mker` and additive
  kernels, which are reused; none states this geometric result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item ID and
  `invariantMonoid|originalInvariantMonoid|ResolvedMonoid|GabberAbelianStage`:
  no declaration of this result or its diagrams. Broader `toric`, `FourthProcedure`,
  and `groupMap` searches found the existing absolute fourth-stage API and the
  reusable `Algebra.ChartResidual.groupMap`. Its exact Mathlib body is now
  written inline, as explicitly permitted by the return, avoiding theorem ownership.
- `blueprint_refs.py search 'invariant monoid'`: zero blueprint nodes. DAG searches
  for the invariant monoid/retained-boundary construction found this item and its
  consumers, not an independent definition of the complete local diagram.

Source read: the local copy of ILO, printed pp.146--148, X 1.8--1.9, including all
four diagrams and the zero-locus argument establishing the dashed monoid arrows.
The theorem's docstring follows the node's twelve proof steps, grouped into seven
paragraphs without changing their dependencies or mathematical content.

## Repair of the returned delivery

H2: removed `lem-trf-chart-face-residual-unit-decomposition` from the added
statement dependencies. All seven uses of its plain `groupMap` helper were
replaced by its exact defining Mathlib expression,
`Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp h)`.
The theorem module import is replaced by the direct Mathlib group-completion
import. This introduces no definition and changes none of the seven maps.
The node's original proof and proof_deps are unchanged; the residual-unit
theorem was not among them, and no proof claim uses it.

Advisory repaired: removed the sandbox copy of the already landed
`def-trf-strict-etale-log-blowup-procedure` node and its identical module.
This packet therefore does not overwrite the owner's lean.by or lean.note.
The existing procedure and modification-data nodes remain cited as providers.

## Second reading by Q90

Read the repaired module against the retained node and the return's clause-by-clause
review. The theorem signature is unchanged, and its 25 recorded declarations remain
the same. The seven changed terms occur in ToricData.injective, torsionFinite and
torsionUnit; InvariantData.groupInjective, finiteIndex and indexAnnihilator; and
ResolvedMonoid.groupIso. Each is definitionally the old groupMap applied to the
same monoid homomorphism, so injectivity, cokernel torsion, finite index, annihilator
and bijectivity retain exactly their previous meanings. No other hypothesis,
coordinate, boundary, comparison, or tower clause changed. Trivial inertia, zero
ranks, c = 0, c = b and b = 0 still have the meanings checked above. The discarded
procedure copy is already in the live library; the packet relies on that provider.
