## Worker report

The module Sheaf.Paper.PodMixedSupportCupProduct defines the right-support cup at all four
coefficient stages and packages it together with the existing four left-support maps on the
fixed Poincare geometry. It introduces no theorem and no sorry. The main declaration is
WeilConjectures.SixFunctorDatum.poincareMixedSupportCupProducts.

Hypothesis and clause correspondence:

- The fixed primes p,l, exponent a>=1, q=p^a, finite field k_0 and its fixed algebraic closure
  k are FiniteFieldDatum D. The distinct coefficient prime and the fixed algebraic closure
  of Q_l are D.CoefficientDatum C. E is explicitly a field and a finite-dimensional Padic
  C.l algebra. The recorded coefficient constructions fix its integers and uniformizer.
  Positive finite exponents are m+1; this includes every n>=1 and excludes the zero quotient.
- The geometric assumptions, including d>=0, smoothness of pure dimension d, separatedness,
  finite type and geometric connectedness, are exactly PoincareDualitySetting D.k₀ d.
  pairingGeometricSpace D d G is its geometric fibre; sixFunctorStructure is the structure
  map to Spec D.k. The type of c is Compactification (G.structureMorphism D.k).
  This is a construction parameter supplied by Nagata, not a properness hypothesis on X.
- S : SixFunctorDatum supplies the specified operations, coefficient normalizations,
  projection transformations and ordinary pull/direct adjunctions. It is the operations
  already used by sk-def-pairing-data. No SfOrientationDatum, ambient exceptional-adjoint
  datum, or IsProper hypothesis occurs in this definition.
- At finite coefficients the K,L arguments of finiteRightSupportCup and finitePairingCup
  belong to finiteTorConstructibleCategory. Integral inputs belong to the full subcategory
  of finiteTorConstructibleIntegral. Rational and common inputs are the recorded bounded
  constructible categories, which are the finite-Tor categories at field coefficients.
- The first four entries of poincareMixedSupportCupProducts are precisely finitePairingCup,
  integralPairingCup, rationalPairingCup, commonPairingCup, from the recorded dependency
  sk-def-pairing-data. They already have coefficient-complex endpoints: canonical
  tensorIso.inv, then the actual point functor applied to projection at (K, Ra_* L), then
  support of 1_K tensor the pull/direct counit. The finite implementation includes its
  canonical realization/tensor-coordinate comparison, not a second tensor definition.
- The finite support/direct objects used by these maps carry the finite-Tor membership
  from S.finiteCoherence. Their integral counterparts use S.integralCoherence. Thus the
  preservation assertions mentioned in the node are used through the existing operation
  interface; no preservation property is added as an unrelated extra hypothesis.
- Integral operations are the recorded completed operations of S.higher.integral,
  rational operations are S.higher.rational, and common-stage ones are S.closure.commonStage.
  These are exactly the operations already used by the four existing pairing cups.
- In each right-support definition the first arrow is the canonical coefficient-complex
  Koszul braiding, in the direction ordinary cohomology tensor compact cohomology ->
  compact cohomology tensor ordinary cohomology. It is followed by the left-support cup,
  then point-fibre of support applied to the canonical signed symmetry on X. The finite
  normalization equalities identify S.finiteTensorDomainStage with finiteIntrinsicDerivedTensor;
  the higher normalizations identify the supplied stage tensors with the recorded tensor
  bifunctors. The final targets therefore have L tensor K. No identification of ordinary
  and compact support is made.
- Associativity/unit laws and coefficient-change compatibility are forward property
  references in the accepted node, not statements to be reproved or assumptions to the
  construction. The right-support convention is explicitly constructed here.

Dependency declarations read and used:

- WeilConjectures.AlgebraicGeometry.PoincareDualitySetting:
  AlgebraicGeometry.PoincareDualitySetting and structureMorphism (sk-def-set).
- Sheaf.Paper.PairingData (sk-def-pairing-data): pairingGeometricSpace,
  pairingPointIdentifications, pairingStageCup; SixFunctorDatum.pairingFiniteInput,
  pairingIntegralInput, pairingFiniteSupport, pairingFiniteDirect, pairingIntegralSupport,
  pairingIntegralDirect, pairingFiniteCounit, pairingFiniteSiteCup,
  pairingFiniteTargetCoordinates, finitePairingCup, integralPairingCup,
  rationalPairingCup and commonPairingCup. The earlier upstream etale cup is only the
  site-valued finite presentation, so it cannot alone attach this coefficient-valued node.
- Sheaf.Paper.FiniteTorAmplitudeSites and its public FiniteTorAmplitude dependency:
  finiteTorConstructibleCategory and finiteTorConstructibleIntegral.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
- Sheaf.Paper.DerivedPullbackTensorHom: finiteIntrinsicDerivedTensor,
  finiteIntrinsicClosed, finiteIntrinsicTensorModels, constructibleIntegralTensor,
  rationalDerivedTensor, commonStageDerivedTensor.
- Sheaf.Paper.PointFibreDerivedTensor: pointFibreDerivedTensor, tensorIso, and the canonical
  pointModuleDerivedBraiding (the last two are public dependencies of that module).
- Sheaf.Paper.FiniteCoefficientPoint: pointFiniteSections, pointFibreIntegralAmbient,
  pointRationalFibre, pointQbarFibre and the existing coefficient-category realizations.
- The ordinary adjunction counits of fix-prop-adjunctions are used through S.finite and
  S.higher/S.closure; the construction uses the same chosen operations, not a second
  small-etale counit. The upstream recorded Adjunctions module and its bounded
  constructible pull/direct restrictions were read. No dependency record needs repair:
  the needed pro-etale maps are already provided by PairingData and its operation datum.
- Sheaf.AlgebraicGeometry.SfEtaleExchanges reexports SfExchanges, including
  sfFiniteProjectionAmbient. The actual datum-coordinate projection is already supplied
  by ConstructibleProjectionMates and used by pairingFiniteSiteCup / pairingStageCup.
- Sheaf.Paper.FiniteTorStability: finiteTor_stability, finiteTor_stability_integral_images,
  finiteTor_stability_rational and finiteTor_stability_algebraicClosure explain the
  preservation memberships carried by the existing operations. Integral output
  constructibility is recorded by sfIntegralDirectImage_constructible and
  sfIntegralCompactSupport_constructible in the two corresponding dependency modules.
- Sheaf.Paper.DerivedPullbackTensorIso: pullbackTensorIntegralBraiding,
  pullbackTensorRationalBraiding and pullbackTensorCommonBraiding; and its public
  FinitePullbackTensorComparison dependency: pullbackTensorBraiding. The finite owner
  def-pur-finite-pullback-tensor-comparison is retained. The integral swap is owned by
  def-pod-integral-tensor-constraints. The new definition owner
  def-sf-rational-common-tensor-symmetries records the rational/common swaps and their
  pinning theorems. The item cites these definitions, not derivedPullbackTensorIso.

Edge cases checked before construction: m=0 is the residue coefficient stage n=1;
all d>=0, including the point in dimension zero, are admitted; zero K or L uses exactly
the same composite; negative cohomological degrees retain the signed braiding. No empty
scheme or tensor index is artificially excluded by the auxiliary maps (the main fixed
geometric connectedness convention is exactly the existing setting). In the nonproper
case, such as A^1, ordinary and compact-support cohomology are kept in different source
positions. Rationalization may annihilate torsion and still defines the same maps.
The common-stage swap is the existing representative-independent class, not a newly
chosen finite-stage representative. Site object and morphism universes are unchanged.

Searches (2026-10-24):

- msearch.py leansearch: "mixed support cup product compact cohomology projection formula
  counit"; eight generic coalgebra and locally constant counit hits, no such construction.
- msearch.py leanfinder: "Mixed support cup product of compact support cohomology and
  ordinary cohomology via projection formula and adjunction counit"; eight group cohomology
  hits, none the geometric mixed-support product.
- msearch.py loogle: "CategoryTheory.Adjunction.counit, CategoryTheory.MonoidalCategory";
  twelve generic monoidal-adjunction hits, no geometric compact-support cup.
- msearch.py grep: "mixedSupportCupProduct|mixed.support|cupProductOfProjection" under
  Mathlib CategoryTheory; zero hits.
- rg in WeilConjectures and Sheaf for mixedSupportCupProduct, mixedSupport, mixed.support,
  cupProduct; found the upstream small-etale mixedSupportCupProduct and the existing
  PairingData coefficient-valued maps. Reused the latter instead of duplicating them.
- rg for def-pod-mixed-support-cup-product in WeilConjectures found the upstream
  PoincarePairing docstring, whose declaration is only the small-etale site-valued version.
- rg for rightSupport and signed-symmetry declarations found no right-support cup;
  found and reused the recorded finite/integral/rational/common signed swaps.

No statement correction or dependency-interface repair is needed. The definition-owner
node added for the returned H2 point is described below.

## Second reading by Q58

The dispatcher requires this worker to work alone and assigns the maintainer's independent
reading after delivery. This section records a second self-reading, not a claim of a second
agent review. With the node and file reopened, the checks were: all four coefficient
categories occur; finite/integral K,L carry exactly finite Tor; the geometric bundle uses
G, not an arbitrary smooth space; the canonical inverse tensor comparison is already in
each reused left-support cup; the projection's second input is direct(L); the target swap
is under the actual support functor; both swaps have the intended direction. No orientation
or properness assumption enters. The repaired definition dependencies name the existing signed
braidings and introduce no forward property dependency or cycle. In particular the
unused theorem lem-pur-derived-pullback-tensor-iso is no longer in stmt_deps. The public declaration
signatures are recorded verbatim and the module has no theorem or sorry.

Validation: scompile.py passed both the sandbox module and the final library module
Sheaf.Paper.PodMixedSupportCupProduct with no errors or warnings. The definition has
real data throughout. The first two compile attempts exposed parsing, explicit endpoint,
and derived-category-instance elaboration issues; these were repaired without changing
the node statement or any existing declaration.

## New nodes

`def-sf-rational-common-tensor-symmetries` owns the existing rational and common-stage
Koszul symmetries in `Sheaf.Paper.DerivedPullbackTensorIso`, together with their
`_existsUnique` pinning theorems. The coefficient prime is `l` with `Fact l.Prime`,
`E` has the explicit field, Padic-algebra and finite-dimensional instances, and `Ω`
has the field, Padic-algebra and algebraic-closure instances. `W : Scheme.{u}` and
`hW : ∀ w : W, Invertible (l : W.residueField w)` render exactly the geometric
hypothesis; the closure universe is independent of the scheme universe. The rational
objects are `M N : sfRationalConstructibleCategory l E W`; the rational pinning theorem
identifies `e.hom` with the localization of the integral hom, using `HEq` for the
prescribed tensor-object identifications. The common objects are
`M N : generalAlgebraicallyClosedConstructibleCategory l Ω W`; the common pinning
theorem quantifies over every `L` and both tensor-stage inequalities `hS,hT` and pins
the hom to `ofHom` of source comparison, rational symmetry, target comparison inverse.
The definitions take `.exists.choose` from uniqueness, so the data are determined
by these maps and are not arbitrary existence choices. Source: the current blueprint's
graded-commutative and coefficient-change clauses and the existing module's Stacks
06YS, 07A4, 0941 construction. LeanSearch, LeanFinder, Mathlib grep, project grep,
DAG ownership search and blueprint reference search are recorded in the new JSON.
They found these exact published declarations but no rational/common definition owner;
therefore this is an `existing: true` attachment with no new Lean file. The integral
symmetry and its reduction pinning are reused through the already reviewed definition
node `def-pod-integral-tensor-constraints`, not duplicated here.

## Returned H2 repaired

Compared with immutable head 15c090393ed6 and the current main node, the only faulty
edge was our added theorem dependency: the cup definitions do not invoke
`derivedPullbackTensorIso`. Removed that edge, retained
`def-pur-finite-pullback-tensor-comparison`, cited the existing integral definition
owner, and added the rational/common definition owner above. All three stages still
use exactly the maps independently checked by the maintainer. No mathematical
statement or cup composite changed. The second self-reading also checked the new
node against the full signatures and docstrings: localization pins the actual
rational hom; every larger field pins the common-stage representative; the
coherent-reduction condition pins the reused integral hom. Zero objects, torsion
killed by localization, equal input stages, arbitrary larger fields, and independent
scheme/closure universes remain admitted. No downstream theorem is a prerequisite.

Repair validation (2026-10-24 UTC): scompile.py compiled the sandbox and final
`Sheaf.Paper.PodMixedSupportCupProduct` paths cleanly. Comparing the repaired item
to current main shows only `lean` and the three added definition dependencies differ;
no base edge was removed. Traversing both statement and proof edges from each added
definition dependency finds no path back to the item.
