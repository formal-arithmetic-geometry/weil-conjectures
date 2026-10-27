## Worker report

The module Sheaf.SixFunctors.TensorAdjunctionReductionSquares states
WeilConjectures.GeneratorReduction.tensorAdjunctionReductionSquares, with one
postponed theorem proof. It uses the published GeneratorReduction word syntax,
operation models, evaluations, recursive r, primitive transpose predicates and
canonical independently constructed structural maps. It does not invoke the
larger generatorReductionCoherence theorem. Two transparent predicates select
the exact structural subfamily and its invertible members. Two recursive action
helpers express the node's naturality clause on arbitrary input morphisms;
they use precisely the functors already used by the object evaluations.
All definitions have real data. Only the final theorem uses sorry.

Hypotheses and clauses, compared with the node:

- The global field is the fixed algebraic closure D.k in FiniteFieldDatum D.
  coeff : D.CoefficientDatum retains the prime coeff.l, primality, and inequality
  with D.p. E, Field E, Algebra (Padic coeff.l) E and FiniteDimensional give the
  stated finite coefficient extension. Its valuation ring, chosen uniformizer,
  positive quotients and completed coefficient sheaves are those used by the
  published scalarReductionSource and coefficientSequenceDerived categories.
  System index n means positive exponent n+1; exponent zero is never substituted.
- W : S → Scheme.{u} and hW : FiniteTypeFamily W D.k retain the finite-type
  structure maps. The independent index universes s and i remain arbitrary.
  The pro-etale categories are the actual small Scheme.ProEt sites, of object
  universe u+1 and morphism universe u, with module universe u+1. No equality
  of site object and morphism universes is imposed.
- o : GeneratorReduction.Operations fixes the actual strict system operations,
  section-normalized composition, geometric/open adjunctions, ringed tensor
  models, and representative-normalized realization model. Its fields are
  independently normalized presentations, not free structural arrows or a
  hypothesis asserting the desired square.
- Word has input, scalar unit, binary tensor, pull, proper push and quasi-compact
  open constructors. Pull stores separatedness, locally finite type and
  quasi-compactness; push also stores properness; open stores the open immersion
  and quasi-compactness. There is no compact-support constructor.
- B.length ≤ 3 and C.length ≤ 3 count tensor as one binary operation vertex.
  The words are finite inductive trees. The input index type need not itself
  be finite; this permits irrelevant inputs and every finite typed word.
- IsTensorAdjunction selects exactly tensorAssociator, tensorLeftUnit,
  tensorRightUnit, pullComposition, pushComposition, pullPushUnit,
  pullPushCounit, openUnit and openCounit. It excludes the four other published
  generator families. No arbitrary arrow or arbitrary whiskering is quantified.
- K k has the integral completed-ring derived-category type. hAdm uses the
  published Admissible, containing finiteTorConstructibleIntegral (in turn
  sfIntegralConstructible and its derived completeness) and SystemAdmissible
  for the actual reduction of each input. The four integers lo, hi, torLo,
  torHi are shared by every input and every word vertex.
- hIntermediate is the pair of recursively defined Word.admissible predicates.
  Each system vertex is normalized, has compatible retained Origins using
  FixedEtaleOriginWitness, constructible cohomology and cohomological/Tor support
  in those same finite intervals. This is a restriction only on systems that
  actually occur in B or C, not on all objects preserved by direct image.
- hPrimitiveB and hPrimitiveC are exactly Word.primitiveFormulas at every
  basic operation on every integral child value. Tensor uses tensorD inverse,
  pull uses pullD inverse, proper image its defining strict-tower identity,
  and open uses openDInv, including the inverse laws for the specified d_j.
  Each equation reads R(d inverse) followed by the actual counit. Input and
  scalar-unit cases impose no extra primitive equation.
- Assertion unfolds to B.r followed by g.systemMap on the reduced inputs
  equal to R(g.integralMap) followed by C.r. Thus it is exactly the displayed
  square with Lean's left-to-right composition convention. Word.r is identity
  at an input, the fixed scalar-unit comparison at a unit, r_A followed by
  A(r_child) at unary vertices, and r_tensor followed by tensor(r_left,r_right)
  at binary vertices.
- The integralMap is the separately defined ringedMap transported by the
  independently defined recursive completionMap. It is not defined from r or
  the desired square. The direct-image compositor is ringedPushComp, the actual
  adjoint conjugate of ringedPullComp, and the system side uses the same mate
  convention through Compositors.pushComp.
- IsTensorCompositionIso selects the five invertible constraints. The second
  conjunct states the square for their inverse arrows. inverseOrZero is the
  existing globally defined inverse construction; on this complete admissible
  domain completion transports and these constraints are invertible, so these
  are exactly their canonical inverses, with no extra IsIso assumption.
- The last conjunct explicitly states naturality of the common arrow from
  R(B_int K) to C(R K): for any input morphisms f : K → L within the same
  admissible bounded domain, reduction of B_int(f), then the square at L,
  equals the square at K then C(R(f)). The actual word morphism actions are
  recursive functor maps, using both tensor slots. Domains with different
  finite bounds fit in a common enlarged interval. Thus naturality is not
  replaced by per-degree isomorphisms or by an assertion only about objects.
- All equalities have morphism types in coefficientSequenceDerived, the
  ordinary derived category of whole strict semilinear systems. All quotient
  transitions are retained, and no evaluation faithfulness is assumed.

Dependency declarations read and used:

- Sheaf.Paper.FiniteFieldFiber: FiniteFieldDatum, FiniteFieldDatum.CoefficientDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing;
  the underlying coefficientExtensionRing/Uniformizer/Integers constructions
  are retained through the recorded dependency imports.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
- Sheaf.Paper.CoefDerivedSystemEvaluationCalculus: CoefficientDerivedSystemCalculus,
  reduction, adjunction, reductionTensor, systemClosed and coefficientSequenceLimit.
- Sheaf.Paper.SemilinearDerivedSections: SemilinearDerivedSectionsData,
  semilinearDerivedSections, evaluation_mate (proof support).
- def-weil-scheme-morphism-properties is the convention record; its component
  properties use Mathlib IsSeparated, LocallyOfFiniteType, QuasiCompact,
  IsProper and IsOpenImmersion.
- Sheaf.Paper.IntegralDerivedOperationsOnSlices: IntegralOnSlice.completedTensor;
  the global integralCompletedTensor and integralDerivedPullback used by Word
  are the retained published global specialization, not a second tensor notion.
- Sheaf.Paper.SfDerivedDirectImage: SfIntegralDirectImage and
  sfDirectImageReductionComparison. The existing integralSystemDerivedDirectImage
  in GeneratorReductionStatement is its strict-system limit specialization.
- Sheaf.SixFunctors.IntegralOpenReductionComparison:
  IntegralOpenReduction.integralOpenReductionComparison and its Comparison interface.
- Sheaf.Paper.SfIntegralConstructible: sfIntegralConstructible, through
  finiteTorConstructibleIntegral and Admissible.
- Sheaf.Paper.NormalizedDVRTower and the coefficient calculus:
  NormalizedDVRTower, IsNormalizedCoefficientSequence and actual quotient transitions.
- Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness: Scheme.FixedEtaleOriginWitness,
  through IntegralSystemRealization.Origins.
- Sheaf.Paper.FiniteTorAmplitudeSites publicly reexports FiniteTorAmplitude:
  finiteTorConstructibleIntegral and the finite-level Tor definitions.
- Sheaf.Paper.BasicOperationsCoefficientReduction: basicOperationsCoefficientReduction
  and its specified coefficient comparisons (proof support).
- Sheaf.SixFunctors.IntegralSystemOperations: Operations, calculus, pull,
  Operations.push, Operations.shriek, Compositors and Compositors.pushComp.
- Sheaf.SixFunctors.IntegralSystemCanonicalBridge: RingedModels,
  RealizationModel, ringedAdj, ringedOpenAdj, ringedPullComp, ringedPushComp,
  ringedAssociator and the canonical realization comparisons.
- Sheaf.SixFunctors.IntegralSystemExpressionDomain: Origins, Good,
  Expression.domain and the typed geometric/domain conventions.
- Sheaf.Paper.RingedExchangeTensorCoherence:
  SheafOfModules.ringedExchangeTensorCoherence (canonical ringed tensor coherence).
- Mathlib.CategoryTheory.Adjunction.Mates: mateEquiv, mateEquiv_hcomp,
  mateEquiv_vcomp (proof support).
- Sheaf.Paper.CompletedOperationTowerSubstitution:
  CompletedOperations.completedOperationTowerSubstitution and its structural laws.
- Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus:
  purNormalizedReconstructionAdjunctionCalculus and the actual-unit/counit
  reconstruction equivalence (proof support).

One-definition and import ownership note: the parent node
lem-sf-generator-reduction-coherence already owns the published Word, Operations,
canonical arrows and predicates in GeneratorReductionStatement. They are reused
rather than copied, and no parent theorem is used. The parent is itself a
proof-dependent citer of this item. Consequently the maintainer must omit the
parent's automatic proof import of this new module under stages/2-statements.md
§3(7)'s import-cycle exception: adding that import would close a source-module
cycle. No DAG edge to the parent theorem is added. This delivery uses only its
pre-existing data constructions. A future module ownership extraction can make
both proofs import those constructions without changing any notion.

Edge cases checked before writing: the empty scheme, empty and identity opens,
identity proper/pullback maps, zero input complexes, a scalar-only input with an
empty variable index, and either orientation of each invertible tensor/composition
identification. None is excluded by the predicates or indices. No nonempty input
hypothesis, strictly positive amplitude, nonzero coefficient-object assumption,
faithfulness of evaluated derived maps, or normalization of unrelated systems is
introduced. Adjunction units/counits are included as arrows without assuming
that they are invertible. Normalization and support restrictions occur only on
the finite word vertices and every input, exactly as in the statement.

Searches actually run:

- msearch.py leanfinder: "Reduction coefficient comparison commutes with tensor
  associators unitors adjunction unit counit and pullback direct image compositors".
  Eight hits, including CategoryTheory.Adjunction.map_μ_comp_counit_app_tensor_assoc,
  unit_app_tensor_comp_map_δ and PresheafOfModules.pullbackComp. These are generic
  monoidal/adjunction facts, not this coefficient-system square.
- msearch.py loogle: "CategoryTheory.Adjunction, CategoryTheory.mateEquiv".
  Twelve hits, including mateEquiv, mateEquiv_counit, mateEquiv_hcomp and
  mateEquiv_vcomp. These provide mate calculus, not the requested theorem.
- msearch.py grep in Mathlib/CategoryTheory:
  "(reduction|coefficient).*(associator|compositor|adjunction)|semilinear.*coheren".
  Zero hits.
- rg of project Sheaf/SixFunctors and WeilConjectures for primitiveTranspose,
  PrimitiveTranspose, reductionComparison, shortWord, ShortWord,
  tensorAdjunctionReduction and structuralGenerator: no hits. Follow-up rg for
  primitive, transpose and realization found GeneratorReductionStatement, whose
  full definitions were read and reused. Its broader theorem does not have the
  same hypotheses or subfamily/inverse conclusion as this item.
- rg and grep for the exact item id in WeilConjectures: no hits. rg of the
  proposed theorem and selector names in both library roots and upstream-name
  records: no hits. Searches for Word.systemAction/integralAction: no hits.

The source is the local current main-20261015 maps-used paragraph named by the
node; all nine expanded DAG proof steps are included in the theorem docstring.
No statement correction, new independent definition node, dependency reattachment
or STATEMENT-DISPUTED finding is needed. The four helper definitions are the
selected-generator/naturality interface of this statement, recorded together
with the theorem in lean.declarations.

Validation: scompile.py first compiled both sandbox and library forms cleanly
(7.4s and 19.5s). The explicit naturality helpers and clause were then added and
the final module is compiled again before the delivery dry run. Compilation,
preflight and delivery use only the prescribed launcher wrappers.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
