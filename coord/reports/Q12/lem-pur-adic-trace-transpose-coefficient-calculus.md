## Worker report

Q12 states lem-pur-adic-trace-transpose-coefficient-calculus. The construction module
is Sheaf.Paper.AdicTraceTransposeData and the statement module is
Sheaf.Paper.AdicTraceTransposeCoefficientCalculus. Every postponed theorem has a
proof docstring and `sorry`; definitions contain actual data. No statement correction
is made. The module uses canonical tensor coordinates for H; source_presentation
also states its identification with the recorded completed pullback and Tate twist.

Hypothesis and clause correspondence (names below are in WeilConjectures.AdicTraceTranspose):

- Finite field, characteristic and distinct coefficient prime: D : FiniteFieldDatum
  and C : D.CoefficientDatum, including C.different and the prime instance. E,F,L are
  Padic.FiniteCoefficientFields C.l C.Qbar; h,k are inclusions. `field` only packages
  this existing field for the existing operation interface.
- Finite-type schemes over k and a k-morphism: SixFunctorSpace and its over-category
  morphism f. The main theorems additionally bind IsSeparated X.obj.hom and
  IsSeparated Y.obj.hom, and SmoothOfRelativeDimension d f.hom.left. Separatedness,
  finite type and quasi-compactness of f are explicit; d : ℕ includes zero.
- Completed coefficients and actual finite-Tor domain: `Cat` abbreviates the integral
  branch of ConstructibleExceptionalCoefficients.C, literally the full category of
  finiteTorConstructibleIntegral. `unit` is integralConstantCoefficientObject, not
  an unspecified monoidal unit. `line` is sfOrientationIntegralComplex in degree
  -2d. `source` is the full-subcategory lift of the published ordinary tensor and
  inverse image, in canonical j coordinates. source_mem and source_presentation
  relate these to completed pullback/tensor and Lf*(-)(d)[2d]. sourceComplex and
  sourceRepresentative keep the signed total formula on all flat representatives.
- P,G,adjunction,epsilon: `operation` is R.operation at the integral field stage and
  fixed compactification c. R is a published RingSystem, so these are its specified
  operations and counit. `integrated` transports along R.left, takes inverse PF,
  tensors the given trace with the identity and cancels the coefficient unit.
  `gamma` calls the published adicTranspose on ordinaryTrace and lifts its ambient
  arrow through the full subcategory; adicTranspose is exactly that adjunction.homEquiv transpose. Thus it is tilde-u and gamma after j,
  rather than a differently normalized trace. The natural transformation
  gammaTransformation has components exactly gamma; gamma_natural gives naturality.
- Ordinary scalar C and strict-tower chi: `scalar` is R.scalar for completedChange
  induced by the actual coefficientInclusion. Its realization is ordinary derived
  tensor; R.integralScalar_eq and integralScalar_normalized retain the strict-tower
  realization and chi, as specified in the dependency. Nothing tests equality of
  maps only after finite reduction.
- a,q,c: supportIso is exactly the q field (called c in this node) of R.comparison;
  it retains QNormalized in the dependency. lineComparison is uniquely the
  underlying sfOrientationIntegralScalarAmbient, including roots and its completion
  unit; unitComparison is uniquely constantCoefficientIntegralScalarIso.
  sourceComparisonArrow composes scalar realization, scalarTensor, scalarPull and
  lineComparison. sourceComparison_existsUnique specifies all components of a.
  SourceTensorCoherent and SourceShiftCoherent render its stipulated ordinary
  tensor unit, associator and shift normalization as explicit hypotheses. They are
  definitions of propositions, with no postponed proofs. coefficient_calculus,
  coefficient_natural, invertible_exact and shift_calculus each bind both premises.
- Arbitrary traces: Traces is the dependent family P_E(T_E) → 1_E. TraceCompatible
  is precisely c_T ≫ P_F(q) ≫ t_F = C_Y(t_E) ≫ unitComparison. The latter factor
  restores the tensor-unit identification suppressed in the node. There is no
  finite-level normalization or trace invertibility hypothesis.
- b definition and naturality: exceptionalComparison uses Mathlib mateEquiv of
  supportIso.inv, hence is a natural transformation by construction. exceptional_counit
  states its component formula as adj_F(c_G inverse ≫ C_Y(epsilon_E)).
- Two displayed coefficient equations: coefficient_calculus has exactly these two
  conjuncts with Lean composition left-to-right: c_H ≫ P_F(a) ≫ integrated_F =
  C_Y(integrated_E), and C_X(gamma_E) ≫ b = a ≫ gamma_F. coefficient_natural gives
  the same second equation as equality of natural transformations.
- Tower and identity: scalarComposition is R.scalarComposition.iso with actual
  completed coefficient-map composition; scalarIdentity is R.scalarIdentity.iso.
  exceptional_tower_identity states alpha_X ≫ b_direct = C_X(b) ≫ b ≫ G(alpha_Y),
  and b_self ≫ G(unit_Y) = unit_X. It needs no trace hypothesis.
- Shifts and sign: SourceShiftNormalized fixes each source shift on sourceComplex,
  using every flat K-flat representative and the ambient inclusion shifts.
  sourceShift_existsUnique and sourceShift supply the canonical comparison, not a
  free shift choice. Its proof records the tensor sign (-1)^(2dn)=1. The explicit
  TraceShiftCompatible hypotheses are exactly the integrated u and adj(u) shift
  squares after j. shift_calculus concludes the gamma and b degree-one squares,
  with both endpoint comparisons expanded. operationRightShift is the published
  counit-compatible shift; Operation.counitShift and unitShift retain that condition.
- Final conditional: invertible_exact assumes IsIso of every gamma component and
  concludes IsIso of every b component and G.IsTriangulated. coefficient_natural,
  exceptional_tower_identity, the SourceTensorCoherent and SourceShiftCoherent
  hypotheses, and shift_calculus give the claimed natural-transformation unit/composition/shift
  compatibility. Exactness is already part of the specified operation interface,
  consistently with the node's proof observation that it needs no invertible trace.

Dependency declarations actually used: ConstructibleExceptionalAdjunctionCoefficients
(System/RingSystem, Operation, Scalar, Comparison and their realization, shift and
normalization fields); FiniteTorAmplitudeSites (finiteTorConstructibleIntegral);
IntegralCompactSupportCoefficientComparison (PurCompactSupport.completed,
completedChange, pull, image, scalarTensor, scalarPull, projectionMap and its recorded
comparison); PuritySourceTransports (RationalSmoothPurityCanonical.ordinaryModel,
ordinaryModel_existsUnique and completed-to-ordinary tensor normalization);
OrientationCoefficientTwists (sfOrientationIntegralComplex_mem,
sfOrientationIntegralScalarAmbient); ConstantCoefficientScalarNormalization
(constantCoefficientIntegralScalarIso); IntegralDerivedOperations (integralDerivedPullback);
IntrinsicCoefficientTwistsUnrestricted (sfIntegralTwistingFunctor);
Mathlib.CategoryTheory.Adjunction.Mates (mateEquiv); proof imports are
PastedMatesCounitNormalization, Shift.Adjunction and Triangulated.Adjunction.
The dependency nodes with records are reused, not copied or weakened.

Edge cases checked: d=0 makes the Tate line unshifted and the Koszul sign one;
E=F uses multiplication unit constraints rather than an ill-typed literal identity;
E⊆F⊆L keeps the tensor associators at both sites. K=0 and zero traces are admitted;
no invertibility conclusion is made without hgamma. The empty scheme is admitted:
no nonemptiness or connectedness is assumed. Uniform Tor bounds and all positive
reduction exponents come from the published full category, not fresh object premises.
All variables and the universe are explicit, with autoImplicit disabled.

Searches: msearch leanfinder "Scalar compatible trace under projection formula gives
coefficient comparison of adjoint transposes commuting with shift and extension
towers" returned eight unrelated linear trace lemmas; loogle
"CategoryTheory.Adjunction, CategoryTheory.NatTrans" returned none; grep
"mate.*pasting|conjugate.*comp|homEquiv.*naturality" found generic adjunction calculus.
Additional recorded leansearch "Integral projection trace adjoint transpose canonical
coefficient and source functor" found eight linear algebra adjoint/trace results;
leanfinder "Canonical integral Tate shifted pullback tensor scalar comparison" found
scheme tensor-pullback and module pullback results; grep
"traceTranspose|Tate.*scalar|sourceComparison" in Mathlib/CategoryTheory found none.
Project rg in WeilConjectures and Sheaf found finite TensorTraceTranspose and
TraceTransposeBaseChange but no integral geometric theorem with these clauses.
DAG search found this item and its citers, no definition of the assembled data;
blueprint_refs ancestor gives thm-pur-rational-and-qbar-purity and search
"projection trace" found no competing unit. The constituent notions are all reused.

Validation: prescribed scompile.py compiles each supplied module against the live
published build. No global build, direct git mutation or shared-source edit was run.

## New nodes

`def-pur-adic-trace-source-coordinates` owns Sheaf.Paper.AdicTraceTransposeData. It names
only the assembled canonical constructions needed to state this item: coefficient
unit, shifted Tate line, lifted tensor source, signed representative comparison,
projection-trace composite, its transpose, and the actual coefficient mate. It adds
no compatibility conclusion of the parent theorem. Each constituent is an existing
operation; all choices are either explicit formulas or uniquely normalized witnesses.
The item cites this node. Searches and their raw wrapper digests are in its record.

## Dependency modules

None. The published dependency interfaces suffice; explicit scalar and operation
shift projections are exposed by small instance adapters in the construction module.

## Second reading by Q12

This is the worker's own final rereading, not an independent-agent review; the
brief assigns independent review to the maintainer. I reread the item and both
modules and checked every hypothesis and equation against the mapping above.
The final rereading restored both scheme separatedness premises explicitly,
expanded the tensor-unit constraint in the trace square, stated the counit formula
for b, and replaced a free source shift parameter with its unique signed-total
normalization. Composition directions agree after reversing the node's written
right-to-left composition convention. No disputed statement was found.

The first dry run exposed a concurrent landing of the name def-pur-adic-projection-trace-data by Q21. That existing node is preserved and cited. The fresh node is def-pur-adic-trace-source-coordinates; it owns the concrete source/full-subcategory adapters and signed representative comparison, while ordinaryTrace/integrated use ordinary tensor coordinates and gamma now directly calls the recorded adicTranspose. No existing node record is overwritten.


## Repair of dc037092d04e

H2: removed lem-sf-constructible-exceptional-adjunction-coefficients,
lem-weil-constant-coefficient-objects-constructible and lem-coef-integral-residue-tor
from BOTH dependency lists. RingSystem, C and Allowed are owned by the already cited
def-weil-exceptional-inverse-image; exists_system is unused. The constant scalar-unit
map is now cited through def-sf-normalized-constant-coefficient-scalar-unit, and
integralConstantCoefficientObject through def-weil-constant-coefficient-objects.
The unused IntegralResidueTor import was removed; unit_mem remains the named local
property with its matching new-node statement and complete proof docstring.

H3/H6: removed the two sorried declarations source_tower_identity and
source_coefficient_shift. Their formulas are now the data-free proposition
definitions SourceTensorCoherent and SourceShiftCoherent. The main coefficient
statement and its natural-transformation, invertibility/exactness and shift clauses
all explicitly assume haTensor and haShift. Thus the tensor associator/unit and
shift equations for a are premises exactly as in the unchanged item statement;
this delivery does not assert or prove them.

Advisories: gamma now uses the existing adicTranspose, through ObjectProperty.homMk.
ordinaryTrace extracts the ambient ordinary-coordinate trace arrow, and integrated
only applies the specified left realization. adicTraceMap has completed tensor
endpoints and takes RingedModels/RingedOpenComparisons; these are different from
this node's ordinary tensor endpoints. No second completed projection or completed
trace map is introduced. The existing projectionMap, ordinary tensor model and
coefficient-unit comparison are retained literally.

The existence-only source_presentation is not used by any definition or theorem
in the delivery to choose a reassociation. sourceAmbient is a concrete functor,
source is its literal full-subcategory lift, and sourceRepresentative is uniquely
fixed by ordinaryModel.representative, the exact pullback factorization, and e.
SourceShiftNormalized fixes the signed source shifts using precisely those
representatives. This records the limit of the presentation assertion rather than
claiming that a choice from Nonempty supplies canonical j.

The newly cited owners also cover the advisory about hidden definition dependencies:
def-sp-open-coefficient-adjunction-data owns PurCompactSupport.pull;
def-pur-integral-compact-support-coefficient-data owns completed, completedChange,
projectionMap and completedPull_comp; def-sfb-proetale-tensor-model owns
ProEtaleTensorModel, proEtaleFlatRepresentatives and proEtaleOrdinaryTensor;
def-sf-orientation-integral-line-comparisons owns sfOrientationIntegralComplex;
def-dl-a1-locally-constructible-adic-heart owns dlAdicGeometricResidueInvertible;
def-weil-pbc-proetale-operations owns proEtaleRingModulePullback; and
def-pur-integral-derived-operations owns IntegralOnSlice.duality and its underlying
site/sheafification data. These records and their source signatures were read in
the current shared clone. Both node lists contain these definition owners.

Comparison with current main: the live item's lean is null; this repair changes
only its lean and stmt_deps. The new source-coordinate node is absent on current
main. The current normalized-unit and constant-object ownership records are reused.
Compared with the returned interface, the two unrecorded coherence theorems have
been removed and replaced by explicit premises, and the three challenged theorem
edges are absent. No natural-language item statement or proof was changed.

Validation: both modules compile cleanly using the prescribed server scompile.py
on the repaired sources. A first run timed out while recompiling the construction
module; the subsequent runs completed without errors or additional warnings.
The coefficient module completes in approximately 14 seconds. The main module
continues to bind all universes and variables explicitly with autoImplicit disabled.

The repaired delivery passed deliver2.py --no-push preflight and the per-file server
compiles. The first preflight found three stale bracket citations in the new node
statement after their dependency edges were removed; those citations were removed
and every new definition owner is cited individually.
