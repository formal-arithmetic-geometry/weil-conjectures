## Worker report

The module Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation states
AlgebraicGeometry.Etale.AffineIntegrationCoefficient.equation, with proof `sorry`.
The statement is unchanged. Every definition has actual data and every postponed
proof is the theorem belonging to its recorded DAG node.

Hypothesis and conclusion correspondence:

* `ell p`, `Fact ell.Prime`, `_hp`, `_hEll`, `k`, `Field k`, and `CharP k p`
  are precisely the positive characteristic and distinct coefficient prime.
* `E F`, their field/algebra/finite-dimensional instances, give the two finite
  extensions of Padic ell. The existing chosen uniformizers are those in
  Padic.coefficientExtensionRing. `m n : ℕ` index the positive exponents m+1,n+1;
  Scheme.finiteTateCoefficient is exactly the existing ULift of those quotients.
  Thus no positive level is omitted. `φ` is any unital ring homomorphism between
  the two lifted rings, equivalently any homomorphism of the original rings.
* `S.Over`, the locally-finite-type, quasi-compact and separated instances on the
  structure morphism render separated finite type over k. `d : ℕ` includes zero.
  `affineTraceTower S d` and `affineTraceProjection S d` are the already published
  ordered affine model, canonically standard affine space by affineTraceAffineSpaceIso.
* `compactification` explicitly iterates the standard projective-line chart,
  using Compactification.comp, precomp and the canonical AffineSpace.map. It is
  not an arbitrary chosen compactification. All F occurrences are the published
  rightDerivedLowerShriekOfCompactification for that exact compactification.
* `coefficient` is the existing ordered right functor at ordinaryFiniteUnit,
  the canonical ordered model of W_R = R_X(d)[2d]. `trace` is its actual counit,
  transported by reductionEtaleAffineLeftIso and the coefficient unit comparison.
  This is precisely vectorBundleIntegration in its global standard frame, by
  the existing standard-frame normalization, without a new orientation choice.
* `hA hB` assert annihilation by N = ell ^ max (m+1) (n+1); `hS` asserts its
  invertibility. Finiteness of both lifted coefficient rings is explicit in the
  conclusion and supplied globally by vectorBundlePurityFiniteCoefficient.
  `hNoeth`, and the two IsNoetherian conjuncts, give the base, affine total scheme
  and specified compactification's middle scheme.
* `Domain` uses the recorded AdjunctionTransfer.etaleProperty, exactly bounded
  constructible intersected with finite Tor amplitude. Its first clause is F_R
  preservation. Its second is H_R preservation, in the canonical tensor model
  IntegrationScalar.object of the ordered W_R. Its third is preservation by the
  ambient right adjoint of exactly this F_R. `ambient` constructs that adjoint
  using isLeftAdjoint_rightDerivedLowerShriekOfCompactification, not a hypothesis.
  The fourth clause is the equivalence on the two corresponding site subcategories
  induced by the actual comparison inverse image. The functors already carry their
  canonical chartOperationComparison (inverse image/Tate/shift and tensor) and
  chartScalarComparison (scalar extension); these imported explicit natural
  isomorphisms give the stated intertwinings without an arbitrary comparison.
* The following quantified clause is T_Z preservation, on both Z=X and Z=V.
* `Equations` supplies invertibility of the actual projections P at W_R, as
  required to define the displayed z. It uses compactScalarProjection, not a
  replacement projection map. Its first equality is q_W followed by F_B(w)
  followed by t_B = T(t_A) followed by the normalized multiplication unitor.
  `coefficientIso` is reductionEtaleAffineScalarIso at the unit followed by the
  right functor applied to the ordinary scalar-unit multiplication. This is w.
* The second equality ranges over every K satisfying the exact ctf predicate.
  IntegrationScalar.integration is P inverse, then tensor of t, then the right
  unitor, exactly z. IntegrationScalar.comparison is compactScalarProjectionTarget
  followed by tensor of w, exactly the canonical a in these tensor coordinates.
  Its left side is q_H followed by F_B(a) followed by z_B; its right side is T(z_A).
  All maps are derived. There is no flatness, projective dimension, or extra
  boundedness hypothesis on φ or B over A.

Dependency declarations used (read in their source, including signature/docstring):

* Mathlib.AlgebraicGeometry.AffineSpace: AlgebraicGeometry.AffineSpace and its
  over projection; the ordered model uses affineTraceAffineSpaceIso.
* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing and the imported coefficientExtensionRing,
  coefficientExtensionIdeal, coefficientExtensionUniformizer constructions.
* WeilConjectures.AlgebraicGeometry.DerivedCategories: DerivedCategoryModule and
  DerivedCategory.torsionCohomology; the actual category is the ordinary small-etale
  ModuleCat-valued derived category, with coefficient universe u+1.
* WeilConjectures.SixFunctors.Etale.Derived.Tensor: derivedTensor.
* WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes:
  DerivedCategory.isBoundedConstructible.
* Sheaf.AlgebraicGeometry.EtaleTorAmplitude: DerivedCategory.hasTorAmplitudeGE;
  the bounded finite-Tor predicate used here is the already recorded etaleProperty.
* WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  rightDerivedLowerShriekOfCompactification.
* Sheaf.Targets.VectorBundlePurity: vectorBundlePurity,
  vectorBundlePurityFiniteCoefficient, vectorBundlePurityProjectionMap,
  VectorBundlePurityAtModulus (actual inverse projection and integration transpose).
* Sheaf.AlgebraicGeometry.VectorBundleIntegration: vectorBundleIntegration and
  VectorIntegrationNormalization, whose global standard frame is used here.
* Sheaf.Paper.EtaleCompactScalarCoherence: compactScalarMap,
  compactScalarProjection, compactScalarProjectionTarget, etaleCompactScalarCoherence.
* Sheaf.Paper.AffineCounitScalar: affineScalarCompactificationCounit and
  affine_counit_scalar, repaired in this delivery as described below.
* Sheaf.Paper.EtaleCtfChartDomain: etaleCtfChartDomain,
  etaleCtfChartScalarDomain, chartOperationComparison and chartScalarComparison.
* Sheaf.Paper.IntegrationTransposeScalarMate: IntegrationScalar.object,
  integration and comparison. The new definition node def-pur-integration-scalar-objects records
  these existing exact constructions. The theorem node is absent from stmt_deps;
  neither its conclusion nor a choice from it is used.
* Proof imports: Sheaf.Paper.SfBcAdicRingDomain (sf_bc_adic_ring_domain),
  Sheaf.AlgebraicGeometry.AffineSpaceTopTrace (exists_affineSpaceTopTrace), and
  the coefficient-compatibility module imported by the repaired counit dependency.
  The finite-type-over-Noetherian leaf uses Mathlib's isNoetherian_of_locallyOfFiniteType.

Edge cases read before writing: d=0 has identity affine tower and adjunction;
empty base requires no points/nonemptiness; K=0 is included by the universal
quantifier; m=n=0 are the positive first quotient levels; identity coefficient
maps, ramified extensions, and nonflat Z/ell^2 -> Z/ell are all included. No
hypothesis that the ring homomorphism arises from a field embedding is imposed.
No mathematical statement dispute or source correction is needed.

Searches: the saved searches.jsonl records msearch.py calls. LeanFinder query
"Affine etale integration commutes with arbitrary derived extension of finite
coefficients" returned eight etale-algebra hits, no integration theorem.
LeanSearch with the same query returned etale ring-map/base-change results,
not the requested derived morphism equations. Loogle query
"CategoryTheory.Adjunction, CategoryTheory.MonoidalCategory" returned twelve
monoidal-adjunction results, no geometric coefficient equation. msearch grep
"integration.*(scalar|coefficient)|coefficient.*integration" in CategoryTheory
returned zero hits. rg of lean/WeilConjectures for the item ID returned none;
rg of both project roots for affine integration, coefficient and trace scalar
terms found the generic IntegrationScalar helpers and the downstream projection
mate, but no existing declaration of this item. The existing vector trace scalar
node overlaps the first equality only and has no Lean record; it does not state
the tensor equation or the finite-stage domain conclusions.

Compilation: every delivered file was checked separately through scompile.py.
The final two-file compile returned exit 0 with no errors and no warnings.
Irreducible helper definitions and explicit unfolding at their construction sites
avoid expensive repeated elaboration; the mathematical interfaces are unchanged.

## Dependency modules

lem-sp-affine-counit-scalar: its recorded Sheaf.Paper.AffineCounitScalar file is
absent in the read clone, and scompile.py --source Sheaf.Paper.AffineCounitScalar
reported "Module source unavailable". The authorized §1(B) repair supplies the
module, restores exactly its recorded theorem signature, and defines its
canonical counit using the existing reductionEtaleAffineLeftIso followed by the
published affineTraceAdjunction counit. The selected normalized projective-line
datum has its counit and orientation fixed by its existing characterization.
Only this dependency's lean record is changed; its statement and split stay intact.

## Second reading by Q103

I reread the node, dependency signature and both modules after compilation. The
positive-level predecessor convention covers all m,n>=1; the coefficient lift is
only a universe encoding. The specified standard compactification is constructed,
not assumed. Both equations use the actual compactScalarMap. The target coefficient
unitor is displayed explicitly, and the source a is the exact tensor/pullback/w
composite. Checked each Domain conjunct against the corresponding preservation
and site-equivalence clause. Removed no mathematical hypothesis or clause and
added no flatness assumption. The dependency repair keeps its signature verbatim.
This is a separate self-check; no independent agent was started, as instructed by
the dispatcher. The maintainer's independent review remains the external reading.

## New nodes

def-pur-integration-scalar-objects records exactly the existing plain definitions
IntegrationScalar.object, integration and comparison in
Sheaf.Paper.IntegrationTransposeScalarMate, with existing: true and no file.
The first is derived pullback tensored with W; the second is inverse projection,
tensor of the trace, then the right unitor; the third is scalar tensor/pullback
comparison followed by tensor of the orientation isomorphism. The source is
main-20261015 cor-pur-vector-bundle-purity.proof.md paragraph 2, also used in
the reduction-exceptional Charts paragraph. LeanSearch returned eight unrelated
pullback/manifold hits; Loogle returned twelve general monoidal-adjunction hits;
Mathlib CategoryTheory grep returned zero hits. DAG grep found only the theorem
node's auxiliary declaration record; project grep found these exact definitions
and no upstream IntegrationScalar duplicate. blueprint_refs search integration
returned 33 blueprint nodes, no definition node for this package. No declarations
are moved, copied or introduced, and the theorem conclusion is not a premise.

## Returned-delivery repair

L at immutable head b7f3d9aedc42 requested definition-only ownership in place of
the added theorem statement dependency. The item's stmt_deps now extends the
current base by def-pur-integration-scalar-objects alone;
lem-pur-integration-transpose-scalar-mate is absent. The new node lists the three
existing definitions, not gamma, mate, or integrationTransposeScalarMate.
Their bodies are actual composites and do not invoke that theorem.

The requested N6 availability recheck on 2026-10-23 used
scompile.py --source Sheaf.Paper.AffineCounitScalar, which still returned
"Module source unavailable". The shared read clone also has no source file.
The accepted lean-only dependency repair is therefore retained. Current base
metadata for both existing nodes is preserved, apart from authorized fields.

Second reading of the repair: opened the existing definitions and compared each
with the new node. The implicit coefficient and scheme universes are the existing
u+1 and u. All rings are commutative, f and W and K are arbitrary, c is specified,
and integration requires precisely invertibility of its canonical projection at
every K. The comparison uses the existing tensor/pullback map then tensor of l.
No finite, Noetherian, flatness or trace-compatibility hypothesis is imposed on
these definitions. The item uses only object/integration/comparison. Its two
equations, Domain and coefficient hypotheses are unchanged from the reviewed
packet. The advisory about site intertwinings is accounted for by the imported
canonical chartOperationComparison and chartScalarComparison constructions;
this repair does not add an existential choice or a tautological isomorphism
conjunct. The original correspondence and edge-case review above still apply.
