## Worker report

The module `Sheaf.Paper.EtaleCartesianTowerTensorComparison` states
`AlgebraicGeometry.ProEtale.EtaleCartesianTower.etale_cartesian_tower_tensor_comparison`.
It has two postponed assertions, the main four-clause theorem and `beta_isIso`.
The latter is the invertibility of the very Cartesian beta whose inverse occurs in
the node, not an assumption or a choice of a comparison. Both have proof docstrings.
All definitions contain explicit data. No node statement is corrected, no dependency
is replaced, and no independent mathematical notion is introduced.

Hypothesis and clause correspondence:

- `P : WeilConjectures.PurityFiniteSetting.{u}` is exactly the fixed finite-field,
  coefficient-prime, finite-extension and positive-level datum. `P.Coefficient` is
  the standard ULift of O_E/(varpi_E^n), not a replacement coefficient ring.
- `EtaleCartesianTower P` packages B,T,A,Q,R,W as `Scheme.{u}`. Its six `Over`
  instances are the structure maps to Spec k, and its six pairs
  `LocallyOfFiniteType`/`QuasiCompact` are their finite-type hypotheses. No
  `IsSeparated` instance is imposed on any structure map to Spec k.
- q,p,G,qQ,J,H have exactly the endpoints in the node. Their `IsOver`,
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` fields express the
  stated common assumptions on all arrows, including the Cartesian projections.
- `dq dp : Nat`, `SmoothOfRelativeDimension dq q`, and
  `SmoothOfRelativeDimension dp p` give smoothness and nonnegative pure
  relative dimensions. The Cartesian square supplies smoothness of qQ;
  permanence supplies the dimensions of all the other smooth composites.
- `Etale G` and `Etale H` are the two given etaleness hypotheses.
  `square : IsPullback J qQ q G` is the actual fibre-product property.
  It allows any chosen representative of Q x_T A; the universal property is
  precisely that of the recorded `Limits.pullback`, including empty schemes.
  `etaleJ` obtains etaleness of J by base-change stability, with a real proof term.
- `a := H ≫ qQ`, `b := G ≫ p`, `F := H ≫ J` are the three composites.
  `outerComm`, `middleComm`, and `totalComm` are explicit equality terms from
  `square.w` and categorical associativity, with no additional assumptions.
- `FiniteEtaleNormalization.omega`, `.pull`, `.comp`, `.rho`, `.sourceEtale`,
  `.beta`, and `.sigma` are reused directly. In particular `.comp` is the
  adjunction conjugate of the fixed compact-support compositor (identical in
  body to `PurityFiniteSetting.finiteExceptionalComposition`), `.sourceEtale`
  is c at the unit followed by rho, and `.beta` is the actual counit mate.
- `FirstEquation` is E_J,q sigma_qQ,G = beta inverse, precomposed with the
  inverse of `targetUnit` to insert eta_G, the canonical pullback-unit map,
  and the right unitor. `congr` identifies qQ G and J q. `betaInv` is
  `CategoryTheory.inv` of the specified beta, justified by `beta_isIso`.
- `SecondEquation` is E_J,pq sigma_qQ,b = J-pullback sigma_q,p after the
  tensor of beta inverse with qQ-pullback E_G,p. `squarePull` compares
  LqQ* LG* and LJ* Lq*. The inverse of `leftDerivedUpperStarTensorIso`
  identifies the tensor of two J-pullbacks with the J-pullback of the tensor.
- `ThirdEquation` is the displayed equation for (a,b,F). `finalFirst` is
  E_H,qQ followed by H-pullback beta inverse; `finalFirstCompared` inserts
  the inverse pullback compositor to identify LH* LJ* with LF*. Its other
  input is a-pullback E_G,p followed by the merely commutative-square
  comparison `outerPull`. The same tensor comparison identifies the target.
- `CompositeEEquation` is E_F,pq = LH* E_J,pq after E_H,pqJ, with the
  exceptional congruence for associativity at the source and the inverse
  pullback compositor at the target. It uses the specified normalized E_F.
- The theorem is the conjunction of those four propositions. There is no
  `IsPullback F a q G` hypothesis anywhere. Neither a cohomological
  shadow nor a noncanonical endpoint isomorphism replaces an equality.

Category presentation: these are canonical ordinary-etale origin coordinates
for the pro-etale bounded constructible finite-Tor categories, exactly the
presentation of the recorded normalization and co-smoothness dependencies.
Those dependencies identify the specified tensor and base-change counit mates
under fully faithful comparison, with the canonical unit/tensor/pullback/support
comparisons. The objects here are the smooth relative dualizing objects and
pullbacks/tensors thereof; there is no quantified arbitrary object whose
constructibility or finite-Tor condition would need an added hypothesis.
`firstEquationModel` and `tensorEquationModel` only assemble formulas before
specializing the coefficient category. Their c, rho, E and input arguments
are all filled with the recorded canonical constructions in `FirstEquation`,
`SecondEquation`, and `ThirdEquation`; they are not assumptions of the theorem.
This follows the explicit abstract-coefficient convention documented by
`Etale.derivedTensor` and the recorded normalization module, avoiding expensive
kernel comparison of two monoidal instance terms at ModuleCat coefficients.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, and its ring instances.
- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`:
  `FiniteEtaleNormalization.compactification`, `.exceptional`, `.pull`,
  `.omega`, `.comp`, `.congr`, `.rho`, `.eta`, `.sourceEtale`, `.beta`,
  `.sigma`, `.targetUnit`, and `finite_etale_dualizing_normalization`.
  Their full signatures and docstrings were read, especially the inverse-free
  smooth-base-change equation and its target-sigma invertibility clause.
- `Sheaf.Paper.PurityFiniteExceptionalComposition`:
  `WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `finiteComparedDualizing`, `finiteComparedTensorClause`,
  `finiteComparedBaseChangeClause`, `IsCohomologicallySmoothFiniteCompared`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale` and
  the reexported native `ProEtale.DerivedCategory.constructibleFiniteTor`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  transported constructible-exceptional coefficient-system interface.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`, with its canonical K-flat
  characterization, rather than an arbitrary comparison.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its canonical tensor comparison is represented here by the published
  `Etale.leftDerivedUpperStarTensorIso` in the origin coordinates.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, its composition and
  base-change instances and dimension-zero characterization;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `.fst`, `.snd`, `.lift`, and the equivalent `IsPullback` universal property.
- Proof dependencies are available through the normalization's public imports
  (including `CanonicalOriginCompactSupportComposition` and its associativity),
  `EtaleSmoothZeroDimensionalFibres`, and `Mathlib.CategoryTheory.Adjunction.Mates`.
  `lem-pur-dualizing-sigma-cocycle-locality` has no recorded Lean module yet;
  its six-step use is retained explicitly in the main theorem's proof docstring.

Edge cases checked against the formulas: G=id (eta and the right unitor are
retained), H=id (the final formula reduces through the canonical identity
compositor), p=id (no Tate identification or orientation is smuggled in),
relative dimensions zero, empty schemes (no nonemptiness or chosen point),
nonseparated finite-type k-schemes (no absolute separatedness), and general
etale H, including a cover for which the outer square is not Cartesian.
The small-site universes stay u+1 for objects and u for morphisms; coefficients
and module values use the published u+1 lift. No extra universe equality.

Searches (msearch logs in the assigned sandbox):

- leanfinder: `Exceptional dualizing tensor compositor through a Cartesian square
  and etale factors`: eight results about tensor-Hom adjunctions, no match.
- loogle: `AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.sigma,
  AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.sourceEtale`: no hits;
  Loogle does not index those project-local identifiers.
- grep: `dualizing.*(etale|pasting)|sourceEtale|cartesianTower`: Mathlib no hits.
- leansearch: `dualizing tensor composition Cartesian square etale tower`:
  eight results (linear-algebra contractions, cartesian monoidal categories,
  etale ring composition, categorical squares), no exceptional comparison.
- rg of live `lean/WeilConjectures` and `lean/Sheaf` with that regexp found the
  normalization's map definitions and DNC-locality statements, none of these
  three tower equations. The exact item id and proposed declaration names
  likewise have no upstream declaration. The existing normalization is reused.

Validation: scompile.py compiled every delivered file (one) in sandbox and
library modes with no errors and no warnings. The successful complete pass was
50.9 seconds in sandbox mode and 20.6 seconds in library mode. Earlier kernel
instance-comparison timeouts were repaired by assembling the equations over an
abstract coefficient category. The limit was never raised; all compilation
used the prescribed wrapper, with no global build or edits to the read clone.

## Second reading by NF

A separate pass through the node and final source checked all six objects, all
six arrows' field-base/finite-type/separatedness assumptions, both relative
dimensions, both etale hypotheses, and the sole Cartesian square. It checked
composition direction: Lean composes left to right, so E_H comes before
LH* beta inverse, and tensor comparisons are used in their inverse direction.
It also checked that FirstEquation inserts eta_G rather than forgetting the
coefficient-unit comparison, and that CompositeEEquation uses the normalized
E_F itself. No discrepancy of the mathematical statement was found. The
redundant specialized sigma wrapper was removed for kernel performance, and
two generic formula assemblers now specialize only to the canonical data.
This is a second pass by the dispatched worker, not a claim of an independent
agent review; the brief forbids starting other agents and assigns independent
review to the maintainer. No new nodes or dependency repairs are delivered.
