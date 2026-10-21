## Worker report

This delivery states lem-trf-finite-ring-bundle-section-orientation in
Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation. The four theorem declarations
separate the existence/unique frame gluing, naturality, rank-zero normalization, and
valuation-quotient comparison clauses of this one node. Their proofs are all `sorry`.
All other declarations are concrete compositions of the recorded constructions and their
canonical maps. No node statement is changed, no dependency is replaced, and no independent
notion or new node is introduced.

The source read is main-20261015 orientation-charts proof Step 4, and the ten-step split
proof in this node. The module docstrings carry that proof, including the Hom comparison,
linear trace invariance, degree-zero gluing and projection-at-the-unit calculation.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`. There is no
  nonzero, field or flatness hypothesis. The coefficient universe is the published ordinary
  etale sheaf convention, with schemes in universe u and modules in universe u+1.
- N >= 1 and NA=0: `(N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)`.
- Noetherian S, N invertible: `(S : Scheme.{u}) [IsNoetherian S]` and
  `hS : IsUnit (N : Γ(S, ⊤))`. Opens and overlaps are Noetherian by the concrete instance
  bundleSectionOpenNoetherian, using the existing induced Noetherian topology.
- Ordinary unbounded categories and exact inverse image: DerivedCategoryModule A S and
  ordinaryFinitePullback A f. The latter is the recorded left-derived inverse image,
  canonically the termwise exact inverse image; no D+, constructible or Tor restriction.
- Rank d bundle and zero: `(d : ℕ) (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]`,
  VectorBundleZeroSection.scheme, .π and .zero. This uses precisely the symmetric-algebra
  relative Spec specified in def-asd-vector-bundle-zero-section. Its existing geometry proves
  affineness, finite type and compactifiability via Nagata; thus compactifiability is derived,
  and no extra compactification is assumed or chosen differently from integration.
- omega_pi: bundleSectionOmega is rightDerivedUpperShriek at ordinaryFiniteUnit A S, for
  the exact same chosen compact-support adjunction as vectorBundlePurityAdjunction.
  bundleSectionObject is its inverse image along the recorded zero section.
- Tate A_T(d)[2d]: affineLinearBaseCoefficient A N hA T d, the published ordered tensor of
  d ordinary finite Tate lines each shifted by two. Its zero-fold tensor is ordinaryFiniteUnit.
  This is the standard canonical tensor/shift identification with A_T(d)[2d], not a new twist.
- Affine trivializing opens and linear frames: the normalization quantifies over all
  `(V : S.Opens) (_hV : IsAffine V.toScheme)` and the recorded
  VectorBundleZeroSection.Trivialization S d M V. The inverse frame is the already defined
  vectorIntegrationChart. bundleSectionChartZero is the Cartesian lift of the actual zero
  section, hence the coordinate zero, rather than an arbitrary section.
- The specified coordinate adjunct alpha_p: bundleSectionAffineAdjunct is the Hom-equivalence
  image of affineLinearCompactComparison.inv followed by affineTraceCounit. The compact
  comparison is the published bounded-coefficient comparison in the unbounded category;
  the counit is exactly the specified normalized coordinate tower. Quantification over
  OrdinaryFiniteTwistTransport and OrdinaryFiniteP1Datum is the same normalization convention
  as VectorIntegrationNormalization: normalized data determine the trace, not an extra premise.
- Canonical comparison and restriction maps: bundleSectionComparison uses
  rightDerivedUpperShriekBaseChangeMap, the mate of inverse compact-support exchange,
  and ordinaryFiniteUnitPullback. On the Cartesian inverse-frame/open-base square it is the
  counit-preserving adjunction comparison. bundleSectionPullbackSquare supplies the exact
  section-composition identifications, not a free map.
- Local o_phi is inverse alpha_p restricted by zero: BundleSectionOrientationNormalization
  states the inverse equation. In ordinary notation it says
  `(u^* o.inv);c = (u^*L ≅ L_V);(w^*G_d A ≅ L_V)^(-1);w^*alpha_p`.
  The two coefficient isomorphisms are vectorIntegrationBaseCoefficientPullback and
  bundleSectionChartCoefficient. The comparison c is invertible by exceptional open
  base change, so this equation states precisely the prescribed local inverse orientation.
- Overlaps and all linear frame changes: the same global o satisfies that equation for
  EVERY affine frame, not merely a selected cover. Consequently the local maps, transported
  back by their specified comparisons, are restrictions of the same map; further inverse image
  to any overlap gives equality, including non-affine overlaps and every invertible linear
  transition matrix. No determinant factor occurs. This packages overlap equality with gluing
  rather than selecting matrices and a cover as additional theorem inputs.
- Unique global gluing: finiteRingBundleSectionOrientation concludes `∃! o : ... ≅ ...,
  BundleSectionOrientationNormalization ... o`. Its predicate consists only of those frame
  restrictions. No unrelated auxiliary normalization is part of uniqueness.
- Preservation by every S-linear isomorphism: finiteRingBundleSectionOrientation_naturality.
  h is an isomorphism of the actual total spaces. hp and hz are the structural-map and
  zero-section equations. hlin is the exact linearity condition in the recorded frames:
  every frame chart is carried to a frame chart. Locally this says the coordinate change is
  invertible linear; conversely every linear bundle isomorphism has that property. The
  conclusion uses the canonical counit-preserving comparison over the identity base, with
  its inverse-image identity unitor, and states that it intertwines the orientations.
- d=0 is identity under E ≅ S: finiteRingBundleSectionOrientation_rankZero produces the
  canonical scheme isomorphism with hom π and inv zero, and equates o.hom with
  bundleSectionRankZeroComparison. That comparison uses the rank-zero section square and
  the conjugate of unboundedEtaleLowerShriekId to the identity adjunction. It is the actual
  identity under E=S, not an unconstrained automorphism of the unit.
- Valuation quotient: finiteRingBundleSectionOrientation_valuation uses ell prime, F a finite
  extension of Padic ell, and Scheme.finiteTateCoefficient ell F n. The published indexing
  is O_F/varpi_F^(n+1); n : ℕ therefore covers every positive quotient level, including 1.
  hEll is exactly invertibility of ell; the original hN, hA and hS hypotheses remain.
- gamma and equality with inverse purity: BundleSectionPurityCompatibility supplies p whose INV is precisely
  vectorBundlePurityProjectionMap at the coefficient unit. Therefore p.hom is the specified
  inverse projection, uniquely determined. bundleSectionPurityUnitMap applies the published
  adjunction to p.hom, tensor with vectorBundleIntegration, then the right unitor, and removes
  the source unit by bundleSectionPurityUnitIso. The conclusion is
  `o.inv = bundleSectionCoefficientIso.inv ; zero^*(gamma)`.
  Since o is an isomorphism and the coefficient and source-unit maps are the canonical ones,
  this is exactly `o = zero^*(gamma.inv)` under ordinary Tate identifications. N is arbitrary,
  so the comparison is not restricted to the annihilator chosen in the valuation theorem.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom; Mathlib.RingTheory.Noetherian.Defs:
  IsNoetherianRing; Mathlib.AlgebraicGeometry.Noetherian: IsNoetherian.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategoryModule;
  WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact:
  etaleInverseImageModulesExact; OrdinaryFiniteP1Arrows: ordinaryFinitePullback.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek: rightDerivedLowerShriek and
  rightDerivedLowerShriekOfCompactification; LowerShriekLeftAdjoint:
  isLeftAdjoint_rightDerivedLowerShriekOfCompactification; UpperShriek:
  rightDerivedUpperShriek and rightDerivedUpperShriekAdjunction.
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback: etaleFiniteTwistPullback and its
  coherent pullback/annihilator comparisons, used through OrdinaryFiniteTwistTransport.
- Sheaf.AlgebraicGeometry.VectorBundleZeroSection: scheme, π, zero, zero_spec,
  Trivialization, trivializationMap, trivializationMap_spec, transition_spec.
- Sheaf.AlgebraicGeometry.CompactifiableOverField: the recorded Compactification and
  HasCompactification interfaces; the field-specific existence theorem is not needed,
  since vectorIntegration_geometry and Nagata supply this bundle's compactification.
- Mathlib.AlgebraicGeometry.AffineSpace: AffineSpace and its over projection;
  Sheaf.AlgebraicGeometry.AffineSpaceTopTrace: exists_affineSpaceTopTrace, affineTraceCounit;
  AffineLinearTraceAction: affineLinearBaseCoefficient, affineLinearCoefficientDescent,
  affineLinearCompactComparison. The tower represents the recorded affine space canonically.
- Sheaf.AlgebraicGeometry.VectorBundleIntegration: vectorBundleIntegration;
  VectorBundleIntegrationCharts: vectorIntegration_geometry, vectorIntegrationChart,
  vectorIntegrationChart_isPullback, vectorIntegrationBaseCoefficientPullback.
- Sheaf.Targets.VectorBundlePurity: vectorBundlePurity, vectorBundlePurityAdjunction,
  vectorBundlePurityLower, vectorBundlePurityTwistedPullback, vectorBundlePurityProjectionMap.
- WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange and UpperShriekCanonicalMaps:
  rightDerivedUpperShriekBaseChangeMap and its open invertibility theorem;
  UpperStarIdCoherence: leftDerivedUpperStarCompSectionIso and leftDerivedUpperStarId;
  UpperLowerStar: leftDerivedUpperStarComp.
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons:
  unboundedEtaleLowerShriekId; Mathlib.CategoryTheory.Adjunction.Mates: conjugateIsoEquiv.
  The other stated proof dependencies are imported for the ten-step proof plan.

Edge cases checked before writing: rank zero (identity tower, no coordinates), the empty
scheme (no Nonempty assumption on bases or covers), zero coefficient ring (no Nontrivial),
N=1 (forces A=0), composite N and non-field coefficients (no primality or flatness assumption),
non-affine intersections (restriction of equal maps is defined on all overlaps), first
valuation quotient level (n=0 in the published n+1 encoding), and arbitrary finite rank.
All universes and variables are explicitly bound, with autoImplicit false. There are no
file-local notations or private copies of the dependency notions.

Searches for an existing declaration:

- msearch.py leanfinder: "Finite ring etale cohomology zero section vector bundle orientation
  normalized affine trace naturality". Eight hits, including SubmersivePresentation.sectionCotangent
  and etaleLocus_eq_compl_support; none state this orientation.
- msearch.py loogle: "CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction". Twelve hits,
  including conjugateEquiv, conjugateIsoEquiv and mate infrastructure; none state the geometric
  assertion, but the canonical conjugate infrastructure is reused.
- msearch.py grep in AlgebraicGeometry: "sectionOrientation|bundleSectionOrientation|zeroSection.*[Pp]urity".
  Zero Mathlib matches.
- rg in lean/WeilConjectures and lean/Sheaf with the same expression and this node's id:
  only unrelated conormal-cone zero-section pullback and PurityVectorBundle.zeroSection helpers.
  The existing VectorIntegrationMate_isIso proves an integration-adjunct property, not this
  node's section-frame gluing, linear naturality, rank-zero and valuation comparison package.

No STATEMENT-DISPUTED flag: the source and the ten-step split support these exact clauses.
No dependency modules, no new nodes, and no statement correction.

## Second reading by Q69

This is an explicit self-check, not an assertion of an independent worker review: the dispatch
brief forbids starting another agent and assigns independent review to the maintainer. I reopened
the node and module, checked all the correspondences above and checked directions of the
inverse-frame square, inverse comparison, affine adjunct and projection inverse. The rank-zero
comparison is explicitly the conjugate to the identity adjunction. The naturality hypothesis
includes linearity in frames, rather than arbitrary scheme isomorphisms. The valuation map is
the canonical projection/integration adjunct, with p.inv fixed to the recorded map. Compiler
repairs changed only how the existing Noetherian-open and inverse-projection interfaces are
supplied; no mathematical hypothesis or conclusion was changed.

Validation: scompile.py is used for every compile; all theorem proofs remain sorry.
