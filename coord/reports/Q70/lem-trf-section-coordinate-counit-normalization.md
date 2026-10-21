## Worker report

This repair replaces the returned packet at immutable head 8129faf75aff. The required
first dry run of the saved packet passed at ab2135a0d21. That mechanical pass did not
resolve the three independent semantic findings; both Lean modules below are new work
on those findings. The packet is rebuilt against current main by deliver2.py.

`Sheaf.Paper.SectionCoordinateCounitNormalization` states four clauses of the same node,
all with proof `sorry`: `affineCoordinateCounit_baseChange`,
`exists_coordinateCounitAdjunction`, `sectionCoordinateCounit_standard`, and
`sectionCoordinateCounit_normalization`. The separate definition module
`Sheaf.Paper.CoordinateCounitArrows` supplies the missing canonical counit arrow and its
explicit Tate/coordinate transport, not a global purity theorem.

Return-point repair:

1. Dropped the saved packet's stmt_dep
   `lem-pur-noetherian-etale-section-specialization`. Added the landed definition owner
   `def-pur-noetherian-section-specialization-arrows`. Every occurrence of family and
   sectionMap now resolves to `SectionComparisonArrows`; `restrictedTheta` uses its
   actual `atOne`. No old NoetherianSectionSpecialization name is used or imported.
2. Removed `Sheaf.Paper.FiniteRingSectionDeformation` and all four saved wrapper defs.
   The statements now use `SectionLocalDualizingComparisons.affineDualizingIso`,
   `affineSectionIso`, `Chart`, `localSourceMap`, `localFamilyMap`, `rawComparison`,
   `restrictionAtOne`, `restrictedTheta`, and `discrepancy`. The chart maps use the
   landed `chartMap` and `chartGeometry` internally. The missing counit transpose and
   its canonical presentation-normalization condition have their own definition node,
   described below. All import paths were recursively searched: 7649 project modules
   visited, with no path to FiniteRingSectionDeformation or
   NoetherianEtaleSectionSpecialization from the final defining/proof imports.
3. The base `S` is general and Noetherian. The affine open is the explicit landed field
   `c.b : c.T ⟶ S`, with `Chart.openB` and `Chart.affineT`. Its local objects are the
   actual pullbacks of the original `sectionInvariant A g s` and `family A g s`, not
   the section invariants of a renamed restricted family. The conclusion is literally
   `(restrictionAtOne ... (rawComparison ...)).hom = restrictedTheta A g s hs c.b`.
   The existential theta is fixed by `theta.hom = restrictedTheta ...`, and the last
   clause asserts `discrepancy ... theta = Iso.refl _`.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- Finite commutative coefficients: `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`.
  Annihilator/invertibility: `N : ℕ`, `hN : 0 < N`, `hA : (N : A) = 0`,
  `[IsNoetherian S]`, `hS : IsUnit (N : Γ(S, ⊤))`. The germ map identifies this with
  invertibility in all local rings. Units on each other base are pulled back by the
  landed `invertibleOnSource`, with no new condition.
- Categories: every object is `DerivedCategoryModule A T`, the ordinary unbounded
  derived category of module-valued sheaves on the small etale site. Inverse images
  are exact etale inverse images extended to these whole derived categories, rendered
  by `ordinaryFinitePullback` or `(upperStar (ModuleCat A) v).leftDerivedFunctor`.
  The latter are the same canonical exact-pullback model. No completed, bounded or
  constructible subcategory occurs. No site universes are identified.
- Tate objects: landed `tateObject A N hA T d` is the actual finite Tate sheaf in
  degree zero, shifted by `2 * (d : ℤ)`. Its first twist is roots of unity extended
  to A; the zeroth is the constant module. `baseTateIso` regroups the existing ordered
  tensor of shifted first twists into this object, using the published pure-tensor
  Tate products. `towerTateIso` uses the existing coefficient descent and root-normalized
  Tate pullback. These are explicit constructions, not arbitrary isomorphisms.
- Dimension and affine model: `d : ℕ`, including zero. The first clause uses the
  existing `affineTraceTower`, `affineTraceProjection`, and their specified coordinate
  isomorphism with `AffineSpace (ULift (Fin d)) S`. The new `standardAdjoint` is that
  same actual counit transpose transported by the fixed isomorphism and its canonical
  exceptional mate. `standardSquare` names the associated well-definedness obligation.
- Counit: `t : OrdinaryFiniteTwistTransport A N hA` and `D` are the existing normalized
  root/pure-tensor transport and Kummer projective-line datum. Their fields fix the
  roots, Chern class, decomposition and actual counit normalization. `towerAdjoint` is
  the exceptional `homEquiv` applied to inverse compact-support comparison, the actual
  ordered tower counit and the coefficient-unit isomorphism, in exactly that order.
  There is no parameter standing for an arbitrary affine orientation.
- Alpha invertibility and arbitrary base change: `affineCoordinateCounit_baseChange`
  concludes `IsIso (CoordinateCounitArrows.towerAdjoint ...)` and universally quantifies
  `T : Scheme.{u}`, `[IsNoetherian T]`, `v : T ⟶ S`. Its equation is pullback(alpha)
  followed by `dualizingComplexBaseChangeMap A (affineTraceMap_isPullback v d)`, equal
  to canonical tower-Tate/unit pullback followed by alpha over T. This is exactly
  beta composed with pulled-back alpha, in Lean composition order. There is no flatness,
  etaleness, finite-type or compactifiability hypothesis on v.
- The affine presentation: `exists_coordinateCounitAdjunction` existentially supplies
  an adjunction of the landed `affineRight`. Its `IsNormalized` condition states that
  `(affineDualizingIso ... adj).inv = standardAdjoint ...`. Thus the supplied data are
  tied to the prescribed ordered counit. Arbitrary adjunctions of the same functors
  could differ by units; the theorem does not assert normalization for those choices.
  Existence is asserted as part of the node, never added as a hypothesis. No definition
  chooses adjunction data from a bare Nonempty theorem.
- Standard pair and the one-fibre: `sectionCoordinateCounit_standard` supplies both
  normalized affine adjunctions over S and X=A1_S. The standard-family object is the
  zero-section pullback of the affine projection over X, precisely the standard Rees
  model in the statement. Its displayed `sectionMap` uses the actual affine Cartesian
  square over the one-section and its zero-section compatibility. The equation for
  `restrictionAtOne (rawComparison ...)` equals that map. In the two Tate coordinates
  this is theta=identity and hence i1*lambda=theta. The scheme identification is exactly
  the standard Rees coordinate map x_j=t*u_j, used again in Chart.reesCoordinates.
- Smooth section: the local theorem binds `g : V ⟶ S`, `[SmoothOfRelativeDimension d g]`,
  `[IsSeparated g]`, `[QuasiCompact g]`, `[HasCompactification g]`, closed `s : S ⟶ V`,
  and `hs : s ≫ g = 𝟙 S`. Smoothness gives locally finite type, so quasi-compactness is
  precisely the finite-type part of compactifiability. The actual Rees projection has
  its required `[HasCompactification ...]`. No geometry bundle is assumed: the landed
  chart definitions insert `chartGeometry` themselves. Its noetherian-domain proofs
  used in the statement are supplied explicitly by that theorem rather than hypotheses.
- Coordinate neighbourhood: `c : Chart d g s hs` records affine T open in S, affine U
  open in V times_S T, its closed lifted section, compatible-section equation, separated
  etale e, over-base equation, and scheme-theoretic Cartesian centres. These are exactly
  the landed centred charts requested by the return. Finite-type and quasi-compactness
  instances of e are derived inside `chartGeometry`, not extra binders. The maps of
  deformations are the actual extended-Rees coefficient maps fixing t and carrying b/t
  to image(b)/t. The standard identification supplies x_j=t*u_j, without inverting t.
- Local orientations: oC has source b* C and oF has source A1(b)* F for the original
  C and F over S. Their hom equalities fix them to `localSourceMap ... adjC` and
  `localFamilyMap ... adjF`. They combine the actual base-change mates, open locality
  and the counit-normalized affine chart map. The existential adjC and adjF satisfy
  the same specified counit condition as the standard pair.
- Lambda and correction: `rawComparison ... oC oF` is the prescribed uncorrected
  comparison, using the family-to-Tate map, inverse Tate pullback, and pullback of the
  inverse source-to-Tate map. `restrictionAtOne` supplies the canonical section
  compositor. Equality to `restrictedTheta A g s hs c.b` gives the actual original
  exceptional fibre map restricted to T. The final `discrepancy = Iso.refl _` is the
  node's equivalent assertion h=1, with the same theta, not a replacement identification.

Dependency declarations read and used:

- `Sheaf.Paper.SectionComparisonArrows`: `family`, `sectionMap`, `atOne`, `Normalized`;
  the final statement uses the first three (atOne inside restrictedTheta).
- `Sheaf.Paper.SectionLocalComparisonData`, namespace SectionLocalDualizingComparisons:
  `tateObject`, `tatePullback`, `affineRight`, `affineDualizingIso`, `affineSectionIso`,
  `noetherianSource`, `invertibleOnSource`, `chartMap`, `rawComparison`,
  `restrictionAtOne`, `restrictedTheta`, `discrepancy`.
- `Sheaf.Paper.SectionCentredChartData`: `Chart`, its actual `reesBase`, `reesOpen`,
  `reesCoordinates`, `chartGeometry`, `localSourceMap`, `localFamilyMap`.
- `Sheaf.AlgebraicGeometry.AffineTraceConstruction`: ordered tower functors, adjunction,
  counit, exchange, right base-change, invertibility and coordinate-space comparison.
- `Sheaf.AlgebraicGeometry.AffineLinearTraceAction`: `affineLinearBaseCoefficient`,
  `affineLinearCoefficientDescent`, `affineLinearCompactComparison`,
  `affineTraceMap_isPullback`. These render the tower's concrete Tate/trace input.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` and `OrdinaryFiniteP1Data`:
  `OrdinaryFiniteTwistTransport`, `OrdinaryFiniteP1Datum`, exact inverse images,
  constant coefficient and shifted line, unit pullback, and normalized actual counits.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`: `finite_etale_torsion_twist_line`;
  its flatness conclusion is the well-definedness obligation `tateFlat`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `finiteEtaleTwistPullbackData`,
  its normalized product `p` and pullback `c`; both use the published finite Tate sheaves.
- `WeilConjectures.SixFunctors.Etale.Derived.Shift`: `derivedTensorShiftIso`;
  canonical derived `singleFunctorObjTensorIso`, `singleFunctorObjUnitIso`, tensor-unit
  and shift-zero comparisons are reused. Their signatures and the positive/signed Tate
  relation were read from the source.
- `SmoothExceptionalBaseChange` and upstream `UpperShriekCanonicalMaps`:
  `dualizingComplexBaseChangeMap`, the actual transpose of pulled-back counit through
  compact-support exchange. `Smooth.Conventions`: `sectionInvariant`.
- Proof imports: `AffineSpaceTopTrace`, `UnboundedEtaleCompactSupportComparisons`,
  Mathlib `Adjunction.Unique`, `SectionReesBaseChangeEtale`, and
  `SectionExceptionalFibreCoherence`; the last two provide the actual Rees and two
  exceptional fibre coherence squares in proof Steps 4--5. The locality and smooth
  base-change interfaces are already defining imports. The remaining finite-type,
  open-immersion-etale and Noetherian proof dependencies use the recorded Mathlib leaves.
- Primitive dependency signatures are the recorded `Scheme`, `SmoothOfRelativeDimension`,
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsClosedImmersion`, `Etale`,
  `AffineSpace`, `HasCompactification`, ordinary `DerivedCategoryModule`,
  `rightDerivedLowerShriek`, `rightDerivedUpperShriekAdjunction`, and exact `upperStar`.
  The finite-type-over-field existence theorem in CompactifiableOverField is not used
  as a field assumption; the recorded node's defining HasCompactification is reused.

Edge cases checked: d=0 uses the zero-fold tensor and identity tower; no positive
relative dimension is required. Empty S, T and U remain admitted; no points or nonempty
cover are selected. A=0 and N=1 are allowed. Finite rings with mixed residue
characteristics are allowed. All Noetherian base changes v, including nonflat and identity
maps, remain quantified. Chart.b need not be identity or surjective. No affine assumption
on original S occurs. All scheme universes are u and coefficients have universe u+1;
autoImplicit is false and every variable is bound. Every definition contains actual data;
only named theorem/well-definedness proofs are `sorry`.

Searches: the saved LeanFinder/Loogle/Mathlib grep/LeanSearch searches remain in
searches.jsonl. New LeanFinder query "Adjoint of the ordered affine space counit and
canonical comparison between tensor powers of shifted Tate lines" returned eight generic
module-adjunction and coordinate hits. Loogle `derivedTensorShiftIso,
singleFunctorObjTensorIso` returned no hits (unknown name in its Mathlib index); the exact
upstream shift and single-tensor declarations were then read and used. Mathlib grep
`affineAdjoint|baseCoefficientTateIso|coordinateCounit` in CategoryTheory returned zero.
LeanSearch for "Canonical Tate tensor comparison for the adjoint of an affine-space
coordinate-tower counit" returned eight generic coalgebra/tensor/comonad hits.
`blueprint_refs.py search 'coordinate counit'` returned zero. DAG and both project source
roots were searched by ordered Tate/coordinate counit and exact declaration names: the
only existing affineAdjoint was owned by the parent theorem module, and no independent
coordinate-counit definition node existed. Existing chart/Tate notions are all reused.

No natural-language statement correction is needed: the returned mismatches were in
its Lean rendering. The node's source statement, proof, proof_deps and all metadata are
retained from current main. Only lean and added landed/new definition stmt_deps change.
No STATEMENT-DISPUTED flag remains.

Validation: scompile.py compiled both delivered modules independently in dependency
order against the live server; helper 30--32 seconds and main module 7--8 seconds. All
errors and the initial line-length warning were repaired. The recursion was changed to
a small typed step and Nat.rec to avoid repeated kernel expansion; no compiler limit or
launcher script was changed. No global build or direct git command was run.

## New nodes

`def-trf-coordinate-counit-arrows` owns the missing canonical transpose and the explicit
ordered tensor/Tate/coordinate transports needed to connect the landed generic affine
adjunction interface to this node's prescribed counit. Its standardAdjoint has exactly
the inverse affineDualizingIso type. `IsNormalized` compares those actual arrows; no
choice of a bare adjunction or orientation appears in a definition. `baseTateStep` and
`baseTateIso` use only real tensor, shift and pure-tensor product data. The two named
well-definedness obligations `tateFlat` and `standardSquare` are stated explicitly in
the new definition node and have full source/proof docstrings. Their definitions do not
choose new data: flatness validates a fixed tensor comparison, and the Cartesian
certificate validates the exceptional mate on a fixed coordinate isomorphism.
The source is the standard affine model in sk-thm-dnc Local construction and
orientation-charts Step 3; all searches and their original tool outputs are recorded in
its mathlib_searches. The parent theorem's helper was unusable here because its module
would create a proof import cycle. All other existing notions retain their landed owners.

## Second reading by Q70

Self-check for this direct dispatcher repair; the maintainer supplies the independent
reading. Read the node, its six proof steps, both modules, the exact landed definition
interfaces and their docstrings, and the two cited blueprint local-construction passages.
Checked each hypothesis and conclusion against the correspondence above. In particular,
checked inverse/hom directions in rawComparison and discrepancy, the two Tate models,
the transpose formula, actual base-change map direction, and the original-versus-local
theta distinction. Found and repaired the three returned faults; no parent theorem or
quarantined specialization import remains. The named theorem proofs are only sorry;
the new definitions' bodies contain no sorry or bare Nonempty choice. The recorded main
signature is copied verbatim from its source, and every declared helper is listed under
its owning node. Final mechanical preflight and per-file compile are run by deliver2.py.

Final dry run: `deliver2.py Q70 lem-trf-section-coordinate-counit-normalization
--no-push` printed `OK (dry run): commit c5081d49079 passes the preflight and compiles;
nothing pushed`. Final self-check confirms both source files have no line over 100
characters; the item's only changed fields from current main are stmt_deps and lean,
with no original dependency removed. Eight declarations are recorded on the new
canonical-arrow definition node and four theorems on the item. The delivery push is
performed only after this passing preflight/compile check.
