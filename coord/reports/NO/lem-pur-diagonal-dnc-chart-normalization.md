## Worker report

The delivery states `lem-pur-diagonal-dnc-chart-normalization` as the declarations
of `Sheaf.Paper.DiagonalDncChartNormalization`. All theorem proofs are `sorry`;
definitions have actual data. The principal equation is
`diagonal_dnc_chart_normalization`; the other recorded declarations state its
restriction, coordinate, integration, exceptional-composition and unit clauses.
The corrected mathematical statement makes its coordinate comparisons explicit.
Already landed supporting nodes are added to `stmt_deps`; no new node or
replacement dependency module is used.

Clause-by-clause correspondence:

- `P : PurityFiniteSetting` contains the algebraic closure of the finite field,
  the prime distinct from its characteristic, arbitrary finite coefficient
  extension, and a positive level. No equality `P.extension = bottom`,
  divisibility condition on the level, or unramifiedness hypothesis is imposed.
  `P.Coefficient` is the prescribed size lift of the actual quotient ring.
- The smooth separated finite-type map of pure dimension `d >= 0` is
  `f` with `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and
  `SmoothOfRelativeDimension d`. The structural map `aY` has the finite-type
  instances. No absolute separatedness is imposed on global X or Y.
- `diagonalDualizing` and `diagonalDualizingObject` are the recorded omega and
  specified theta, not new choices. `diagonalTwist` is A(d)[2d].
  `chartOrdinaryOrientation_spec` records both their exact comparison equation
  and their full published coordinate-counit normalization.
- An affine local map is `h : U -> V` with `IsAffine U`, `IsAffine V` and the
  same relative geometric hypotheses. The arbitrary opens U inside f^-1(V)
  are handled by target-open base change followed by source-open restriction.
  `chartOrientation_open_baseChange` uses the actual smooth base-change mate;
  `chartOrientation_etale_restriction` uses normalized source-etale locality.
  The latter includes every quasi-compact open immersion. Its displayed
  composite-smooth instance follows from etale precomposition and does not
  restrict the mathematical domain. All these maps are ordinary presentations
  of the pro-etale maps by `chartOrdinaryOrientation_spec`.
- W, p and Delta are `pullback h h`, `pullback.fst h h`, and
  `pullback.diagonal h`. C is `Dnc.sourceSection` of this pair.
  `chartDualizingUnit` retains the conversion between the published section
  invariant's tensor unit and the coefficient unit A[0].
- Alpha is `chartDiagonalAlpha`: the actual diagonal base-change mate, its
  section identity, and the comparison-unit maps. Delta is
  `chartDiagonalDelta`, selected from `existsUnique_dncInvariance`, including
  its endpoint normalization. The normal cone and zero section are the
  actual kernel-ideal extended-Rees cone and augmentation, not an abstract
  rank-d projection.
- `chartDiagonalNormalBundle` states finite local freeness and invertibility
  of the canonical symmetric comparison also for rank zero.
  `chartNormalModelRaw` constructs the actual cone-to-conormal-bundle iso by
  relative Spec of the symmetric comparison and homogeneous-normalized Rees
  comparison. `chartNormal_model_exists` fixes the inverse model to this value
  and states preservation of projection and zero; `chartNormalModel` uses that
  uniquely determined witness.
  `chartDiagonalConormal_differentials` uniquely normalizes the degree-one
  differential identification by [y(a)-x(a)] -> da. Taking symmetric relative
  Spec of that identification gives N_Delta = Spec Sym(Omega_U/V) = T_U/V.
- Beta is `chartDiagonalBeta`, with its canonical site and Tate pullback maps.
  `chartNormal_vectorPurity_normalization` states its integration-adjunction
  normalization on every vector-bundle model of this actual normal cone.
  Together with model existence this identifies beta with zero restriction
  of vector-bundle purity and ensures independence of frames; it is not
  merely an unspecified isomorphism to a twist.
- `chartDiagonalAssembly` is alpha inverse, then delta, then beta, in that
  order. `diagonal_dnc_chart_normalization` equates it to the specified theta_h.
  The two restriction equations above give Lj*theta_f = theta_h and agreement
  of the assemblies on every further common affine refinement.
- `chartCoordinateDifferences` is the actual vector y_i-x_i on W, based at p.
  `chartCoordinateDifferences_neighbourhood` asserts the existence of an open
  neighbourhood of the whole diagonal on which this map is etale and its
  zero square is Cartesian. It does not assert that the zero fibre on all W
  has no other etale components. The canonical conormal differential formula
  fixes its ordered normal coordinates and their signs.
  `chartCoordinateDifferentialFrame` uniquely specifies the ordered frame of
  Omega_U/V by the actual pulled-back coordinate differentials. Taking its
  symmetric relative Spec gives the claimed trivial normal bundle.
- `chartStandardSection P U d (h ≫ aV)` is the actual ordinary-etale standard
  pair invariant D_d, and its comparison image is the common target below.
  `chartSectionEtaleRestriction` constructs restriction from pullback composition,
  the exact/derived comparison, and `tensorMateEtalePrecompLocalityIso` evaluated
  at the coefficient tensor unit. It does not use any purity orientation.
- `chartSourceCoordinateComparison` has domain the actual `Dnc.sourceSection`.
  Its inputs O,s,hs,hc,sq are precisely a neighbourhood supplied by
  `chartCoordinateDifferences_neighbourhood`: hs factors the diagonal, hc
  asserts the difference map is etale, and sq is the Cartesian zero square.
  The map first restricts along O.ι, then inverts restriction from the affine
  standard pair along the coordinate-difference map. The equality sq.w fixes
  the zero section. Both restriction maps use the specified exceptional mate.
- `chartConormalFrame` composes the unique differential frame with the inverse
  unique conormal/differential identification. `chartConormalCoordinateMap`
  sends its ordered basis to degree-one symmetric-algebra generators, using
  the existing vector-bundle structure-algebra counit. Thus it is a real
  homOfVector construction, with no unspecified scheme isomorphism.
  `chartNormalCoordinateMap` composes the inverse canonical conormal model
  with this map. `chartNormalCoordinateMap_spec` states invertibility, the
  projection equation, and the zero-section equation. These yield the actual
  N_h ≅ A^d_U in the specified differential coordinates.
- `chartNormalCoordinateComparison` starts at `Dnc.normalSection`, uses its
  existing ordinary-site comparison, then inverts the normalized restriction
  along `chartNormalCoordinateMap`. The zero-section equation fixes its section.
- `chartDiagonalDelta_coordinate_identity` now has a coordinate map u and its
  factorization w, together with all the centred neighbourhood data above.
  Its conclusion is exactly
  `chartSourceCoordinateComparison.symm ≪≫ chartDiagonalDelta ≪≫
  chartNormalCoordinateComparison = Iso.refl _`.
  This is equality of endomorphisms of the common realized D_d. It no longer
  quantifies over an arbitrary family trivialization or repeats the predicate
  selecting delta. The normalized compact-support presentation N is quantified
  universally; it is not an assumed isomorphism between these objects.
  The natural-number binder d includes 0: all constructions use ULift (Fin d),
  the empty symmetric algebra and the canonical identity/unit constraints.
- `chartGamma` is the existing ordered `affineSpacePurityComparison` at A,
  through `projectionAffineInPresentation` and the canonical tensor-unit
  source constraint. That constraint is the generic K-flat shift cancellation,
  the actual pullback-unit comparison, and the left unitor. Its raw-map HEq
  specifies its entire isomorphism uniquely; no purity arrow chooses it.
  The pullback-unit comparison includes the published exact/left-derived
  inverse-image transport. `chartGamma_eq_inverseOrientation` is model agreement;
  `chartGamma_counit_normalization` identifies its map with the actual ordinary
  ordered affine counit mate. The successor level n+1 ranges over every
  positive level. `chartAffineGamma` is that mate as an isomorphism in the
  ordinary presentation, using its named isomorphy theorem.
- `chartEpsilon` is the normalized exceptional-locality mate in ordinary
  coordinates. `chartEpsilon_standing_composition` explicitly identifies its
  pro-etale realization with `standingExceptionalComposition` at the bounded
  constructible coefficient unit followed by `chartEtaleIdentification`.
  The latter retains the unique normalized counit-preserving etale adjunction
  comparison and the comparison unit. The unit's constructibility is proved
  only as a named postponed theorem; its actual data is A[0].
- `chartOrientation_coordinate_formula` and its forward version express
  theta_h = Lu*(Gamma^-1) epsilon_u, with the canonical Tate restriction
  displayed. The coordinate tower has its existing coordinate-preserving
  isomorphism with Mathlib affine d-space.
- `chartTraceZero` is the recursive zero vector. `chartStandardSection_formula`
  says b_r is precisely its pullback of Gamma^-1, preceded only by the
  coefficient-unit presentation comparison and followed by Tate restriction.
  `chartAffineGamma_zero` and `chartStandardSection_zero` state the identity
  values with the canonical exceptional-identity and unit constraints visible.
- Etale changes of charts are covered by source-etale restriction, the
  coordinate conjugation equation and the universally model-independent
  vector integration equation. All displayed identifications use those fixed
  maps; no orientation or arbitrary isomorphism is an input.

Dependency declarations used (read with signatures and docstrings):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`.
- Mathlib smooth, etale, proper/separated, finite type, affine-space and pullback
  definitions: `SmoothOfRelativeDimension`, `Etale`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `AffineSpace`, `IsPullback`.
- `Sheaf.Paper.PurityDiagonalDualizingObject`: `diagonalDualizing`,
  `diagonalOrdinaryDualizing`, `diagonalDualizingObject`,
  `diagonalDualizingComparison`, `DiagonalOrientationNormalization`,
  `diagonalEtaleLocality`, `diagonalAffineMate`, `diagonalDualizingCongr`.
- `Sheaf.Paper.PurityDiagonalBaseChangeCompared`:
  `comparedDiagonalBaseChange`, `diagonalComparedRestriction`.
- `Sheaf.Paper.PurityDncInvariance` and its public comparisons:
  `Dnc.existsUnique_dncInvariance`, `sourceSection`, `normalSection`,
  `sourceComparison`, `normalComparison`, `pullComparison`, `fibreOne`, `fibreZero`.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`: `sectionInvariantFinite`;
  the published DNC realization supplies its fixed-scalar presentation.
- `Sheaf.Paper.FixedFinitePositiveCoefficientTwist`, through the recorded twist
  dependencies: `diagonalTwistEtale`, `diagonalTwist`, `diagonalExponent`.
- `Sheaf.Paper.PurityNormalProjection`, `PurityNormalCone` and upstream
  deformation-to-normal-cone: actual `normalConeProj`, `normalConeData`,
  `normalConeZeroSection` and the kernel normal cone.
- `Sheaf.AlgebraicGeometry.ConormalGradedAlgebraBasic`:
  `ConormalGradedAlgebra.piece`, `power`, `powerInclusion`, and `representative`
  are the owner declarations used by the coordinate and conormal formulas.
- `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`:
  `ConormalGradedAlgebra.symmetricComparison` is the theorem-constructed canonical
  comparison used through its selected witness; the module is imported directly.
- `Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates`:
  `exists_centred_coordinates` is now an explicit proof dependency (ordinary
  import). The coordinate-difference neighbourhood is its chart specialization.
- `Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence`:
  `Etale.FiniteSmoothPurity.reesConeComparison_exists` and its predicate
  `ReesConeNormalized` from `ReesConeNormalization` fix the actual conormal
  model on homogeneous representatives. Their owning nodes are recorded.
- `Sheaf.SmoothPurity.TensorMateEtalePrecomp` (publicly available through the
  recorded orientation dependency): `Etale.tensorMateEtalePrecompLocalityIso`
  constructs every new section restriction from normalized adjunction data.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: actual symmetric total
  space, projection and augmentation `scheme`, `pi`, `zero`.
- `Sheaf.Paper.VectorBundlePurity` and
  `Sheaf.AlgebraicGeometry.VectorBundleIntegration`: `vectorBundlePurity`,
  `vectorBundleIntegration`, `vectorIntegrationBaseCoefficientPullback`.
- `Sheaf.Paper.AffineSpacePurityComparison`: `affineSpacePurityComparison`;
  `ProjectionPurityAgreement`: `projectionAffineInPresentation`,
  `projection_purity_agreement`; its canonical Tate/tensor coordinate modules
  supply the existing root-power, shift, tensor and identity transports.
- `Sheaf.AlgebraicGeometry.AffineTraceTower`: actual ordered tower, projection,
  coordinate isomorphism and geometric instances.
- `Sheaf.Paper.StandingExceptionalComposition`:
  `ProEtale.standingExceptionalComposition`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials` and its universal derivation.

Edge cases: d=0 uses the empty coordinate sequence and literal identity tower;
no positive-codimension-only regular-immersion predicate is imposed. Empty U,V
and disconnected or nonreduced affine schemes are permitted. All levels n>=1,
including levels not divisible by the ramification index, use ell^n as a valid
annihilator. Global X,Y need not be separated over k. The open square need not
make the chosen affine U all of f^-1(V): source restriction handles the further
open. A coordinate map can have additional zero-fibre components away from the
diagonal, hence the explicit neighbourhood. No finite-Tor assumption is made
on arbitrary coefficients: the only such input is the actual rank-one unit.

Searches for existing statements:

- msearch LeanFinder: “smooth diagonal orientation on etale coordinate charts
  normalized deformation to normal cone and affine space purity”: eight hits
  on standard-smooth/etale presentations and smooth local normal forms; no match.
- msearch Loogle: `AlgebraicGeometry.Smooth, CategoryTheory.Iso`: no hits.
- msearch grep in Mathlib AlgebraicGeometry:
  `diagonal.*orientation|sectionInvariant|dncInvariance`: no hits.
- msearch LeanSearch: “diagonal orientation on smooth etale coordinate charts
  equals affine space integration normalized deformation to the normal cone”:
  eight hits, on diagonals, affine properties and smoothness; no match.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: section invariants, DNC,
  diagonal orientations and chart comparisons locate the dependency APIs above.
  No declaration for this item was found. Searching the exact item ID found no
  upstream implementation. The existing vector-bundle orientation theorem has
  an E=Q_ell hypothesis and cannot replace this arbitrary-E statement.

No statement dispute is proposed; the statement correction is recorded below. No target statement or
shared repository file was edited. Verification uses only the prescribed
scompile.py and deliver2.py wrappers against the live published build.

## Repair of return L

The returned immutable head d9ede3d4c4ff and its saved packet contained the
endpoint-reading equation of `existsUnique_dncInvariance`; the initial retained
packet dry run passed mechanically as d531e6c595c, but the semantic return still
required a repair. That endpoint equation has been removed. The module now
constructs the source and normal coordinate maps described above, and its
coordinate theorem states their conjugation equation with delta. Thus the
coordinate chart, its centred neighbourhood, Cartesian square, conormal model
and ordered differential frame occur in the actual Lean terms.

H3: repaired by `chartSourceCoordinateComparison`, `chartNormalCoordinateMap`,
`chartNormalCoordinateComparison` and the replaced
`chartDiagonalDelta_coordinate_identity`. No unrelated arbitrary frame,
family trivialization, or comparison is an input.

H5: all new definitions have real data. The normal model is constructed from
the existing symmetric comparison and normalized Rees comparison. Its selection
from `chartNormal_model_exists` is fixed by equality to that construction;
selection from the differential/frame theorems is fixed on generators by their
unique predicates. Isomorphy of the coordinate map is postponed only as the
named theorem `chartNormalCoordinateMap_spec`; normalized etale restriction uses
that proof about an already defined map. The explicit `asIso` in the relative-Spec
construction uses `chartDiagonalNormalBundle` for the existing symmetric map. No definition uses a bare Nonempty existence choice.

Advisory: the mathematical node no longer quotes Lean identifiers. It describes
c_src and c_N and cites the owner nodes for conormal and Rees constructions.
`lem-trf-smooth-section-centred-coordinates` is now in the proof and proof_deps
and its module is an ordinary proof import. The accepted assembly, Gamma,
epsilon, b_r, vector integration, restriction and rank-zero clauses are retained.

Repair searches: msearch grep
`sectionInvariant.*(chart|etale)|normalCone.*coordinate` in AlgebraicGeometry
returned 0; LeanFinder “canonical section invariant comparison through etale
coordinates diagonal deformation normal cone identity” returned 8 unrelated
standard-etale algebra hits; Loogle
`AlgebraicGeometry.AffineSpace.homOfVector, CategoryTheory.Iso` returned 0.
Project rg located the existing normalized exceptional restriction and relative
Spec/Rees APIs; the new helper names have no existing source declaration.

## Statement corrected

The original statement asserted the coordinate identity “under these
section-invariant and normal-bundle coordinate comparisons” without defining
the comparisons. Following the current blueprint
`sk-prop-sp-orientation-charts.proof.md`, Steps 1–3, the corrected statement
specifies the centred neighbourhood and Cartesian zero square, c_src as the
open/etale exceptional restriction, the canonical symmetric/Rees conormal
model and ordered differential frame, and c_N as the resulting normal-section
comparison. Its identity is c_N delta c_src^-1 = id on D_d, including d=0.
The statement_change preserves the original text and original dependency/proof
fields and lists exactly the two stmt_deps/proof_deps citers found on the base:

- `lem-pur-etale-orientation-locality`: holds. Its proof uses the dimension-zero
  standard section and bundle unit identities and open restriction, all retained.
- `thm-pur-composition-coherence`: holds. Its proof Steps 4 and 6–8 use the
  assembly, identity in the ordered frames and rank-zero unit law. The repair
  supplies those particular coordinate maps and preserves its formula for b_r.

The additional grep hit `cor-pur-vector-bundle-purity` mentions the item only
inside its proof text, not its stmt_deps or proof_deps; it is not a record in
this required citer list. No citer file is edited.

Self-check after repair: the source and normal coordinate maps have the same target,
the comparison image of the actual section invariant of (A^d_U -> U,0). The new
identity theorem composes only these maps and the existing delta. The old endpoint
predicate is absent from that theorem. Each new theorem has its proof docstring;
every theorem proof remains sorry, every definition has constructed data, and all
54 declarations are recorded. Maximum Lean source line width is 95. The sandbox
and library compiles both passed (29.2 s and 29.1 s) without errors or unexpected
warnings. The dry-run wrapper checks the final file again after import cleanup.

Final repaired-packet dry run: deliver2.py --no-push printed OK at c5031fc37a2;
preflight and both namespace compiles passed. The original statement and changed
original proof/dependency fields were checked verbatim against the read clone;
only the authorized statement-correction fields and lean record differ.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
