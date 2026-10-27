## Worker report

The delivery states lem-sf-projection-weil-tensor-domain-bridge in
`Sheaf.Paper.ProjectionWeilTensorDomainBridge`, namespace `WeilConjectures`.
The node's mathematical statement, accepted proof and dependency lists are unchanged.
The theorem statements are split into the node's clauses in one owning module; every
new theorem has `sorry` as its entire proof. No projection transformation is assumed
invertible. The declaration list includes the two concrete bundling definitions and
the geometric-base-change property instances.

Source read: the current main-20261015
`sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md`, especially
its Weil-equivariance sentence, together with all five accepted proof steps of the
assigned node. Those steps supply the more detailed coefficient and domain bridge.
Read the whole stage-2 brief, stage document, worker role, setup/goal/state, delivery
errors H, and the CompactObject example (now withdrawn and attached to the upstream
CategoryTheory.IsCompactObject definition).

Hypotheses and clauses, matched explicitly:

- The global finite-field datum is `D : FiniteFieldDatum.{u}`; it contains the prime p,
  positive exponent a, q=p^a, the finite field k₀ and its fixed algebraic closure k.
  `c : D.CoefficientDatum` supplies the prime ell, ell≠p and the chosen Qbar.
  `E : Type u`, `Field E`, `Algebra (Padic c.l) E` and `FiniteDimensional ... E`
  give the finite coefficient extension. Its ring, uniformizer and all quotients
  are the dependency's existing Padic coefficientExtension constructions, without
  a second coefficient definition. Positive n is `n : ℕ`, `hn : 1 ≤ n` for S.
  Quotient towers elsewhere use n+1, hence include exponent one and no exponent zero.
- The operation hypothesis is `S : SixFunctorOperationDatum D c E n hn`, precisely
  the recorded operation datum rather than SixFunctorDatum or a projection-isomorphism
  datum. The ambient operation's spaces are SixFunctorSpace, which imposes locally
  finite type and quasi-compactness on the structure morphism and no separation.
- X₀ and Y₀ are `Over (Spec (.of D.k₀))` with `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact` on their structure maps. f₀ is their Over morphism with the
  same three morphism properties. `sfProjectionWeilSpace` bundles exactly
  `D.geometricFiber`; `sfProjectionWeilMap` is exactly `Over.pullback.map f₀`.
  The three instance theorems assert the base-change properties already in this
  hypothesis sentence. They supply no new geometric hypothesis.
- The assertion for each W=X,Y is the arbitrary W₀ statement
  `sfProjectionWeilCoefficientBridge`. Its first conjunct identifies the completed
  ring comparison by every finite quotient projection. The ring on the Weil side
  is `pbcAdicCompletion ... (pbcIntegralDatum c.l E)`, the actual limit of the finite
  coefficient sheaves. The comparison is not an unspecified ring isomorphism.
  The second conjunct is `sfIntegralConstructible ... K ↔
  PbcIsBoundedConstructibleComplete ... (integralDetailedTransport ...).obj K`.
  These are full subcategory predicates under the canonical completed-coefficient
  transport, with the actual compatible etale-origin conditions inside the latter.
- For all integral bounded constructible M,N, `sfProjectionWeilIntegralTensorDomains`
  states membership of both `ordinaryAmbient` and `completedAmbient` in the existing
  integral category and invertibility of the specified `chi.app (M,N)`.
  It requires no Weil maps. This is the comparison unit from WfTensorCompletion,
  not an arbitrary chosen isomorphism of the two derived objects.
- With integral Weil isomorphisms phi and psi,
  `sfProjectionWeilIntegralTensorBridge` states IsIso chi and exactly the equation
  `ordinaryMu.hom ≫ ordinary.map (phi,psi) ≫ chi = pullback.map chi ≫
  completedMu.hom ≫ completed.map (phi,psi)`. Lean composes left to right, so this
  is the displayed chi*phi_ord = phi_comp*Phi^*(chi) in the node.
- `sfProjectionWeilRationalTensorBridge` supplies a normalized RationalComparison,
  an isomorphism of actual WeilD pairs with underlying arrow equal to chi, and HEq
  of its faithfully included completed Frobenius with `wfTensorFrobenius`.
  HEq retains the specified object models rather than adding object equalities as
  assumptions. WeilD inputs K,L have arbitrary rational structure isomorphisms;
  there are no integral structure-map binders or lattice-isomorphism hypotheses.
- `sfProjectionWeilCommonTensorBridge` quantifies E,F,G with E≤G,F≤G, transports
  the given WeilD inputs by the existing Weil scalar extensions, fixes the
  underlying arrow to the same normalized chi at G, and specifies its actual
  common-stage image by `ebar = ((weilScalarSystem ...).ι G).mapIso e`.
- `sfProjectionWeilScalarDomainBridge` handles an arbitrary algebra embedding
  `i : E →ₐ[Padic c.l] F`. It states both intrinsic integral constructibility of
  the completed scalar extension and its membership in the identified Weil
  integral category. This supplies the common-stage underlying-input domain.
- In `sfProjectionWeilTensorDomainBridge`, K and L are objects of the intrinsic
  integral constructible categories and `_hL` is precisely the recorded
  `finiteTorConstructibleIntegral ... L.obj`. The existential P,H,U,V,B are
  objects of the appropriate full constructible subcategories. The first five
  clauses specify their ambient derived objects as P=Lf*L, H=K completed-tensor P,
  U≅the completed proper/open image of K, V≅that image of H, and B=U completed-tensor L.
  These are derived-object identifications, not cohomology-only statements.
  The compactification b is arbitrary; it parametrizes the existing construction
  and is not a compactifiability hypothesis on a new class of morphisms.
- The next five equalities identify P,H,U,V,B with the corresponding integral
  operation outputs of S. The final five equalities identify their raw
  rationalizations with the rational pullback, source tensor, two compact-support
  outputs, and target tensor of S. Thus all five actual outputs have the precise
  underlying constructible models, with morphism domains inherited from the full
  subcategories. The completed proper/open image is the existing realization of
  the strict finite-reduction-limit construction, as recorded by
  sfQcqsCompactSupportRealization and S.higher.supportConstruction.
- `sfProjectionWeilCommonDomainBridge` repeats those five integral models at every
  common finite field G in S.closure.coefficientStages, and gives derived isomorphisms
  of their inclusions with all five common-stage operation outputs of S.closure.
  Combining it with the scalar-domain theorem treats inputs originating at
  different finite fields, and combining it with the common tensor theorem retains
  the specified tensor Weil map. These are exactly the bounded-constructible
  domain conditions used in the assigned node's application of lem-fix-weil-operations.

Dependency declarations read and used:

- Sheaf.Paper.FiniteFieldFiber: FiniteFieldDatum, CoefficientDatum, geometricFiber.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: finite_coefficientExtensionRing;
  its public imports give the ring, uniformizer and quotient constructions.
- Sheaf.Paper.SixFunctorOperationDatum: SixFunctorOperationDatum, with the full
  signatures of SixFunctorHigherOperations and SixFunctorCommonStages in its
  public dependency SixFunctorOperationDatumStages. The fields used are integral,
  rational, integralTensor, rationalTensor, closure, coefficientStages,
  commonStage and commonStageTensor, with their existing construction normalizations.
- Sheaf.Paper.PbcWeilCategory: WeilD, weilFrobeniusPullback,
  weilScalarExtension and weilScalarSystem; WeilDQbar is their common-stage category.
- Sheaf.Paper.WeilTensorProduct: wfOrdinaryDerivedTensor, wfCompletion,
  wfCompletionUnit, wfConstructibleInclusion, wfWeilStructure and wfTensorFrobenius.
- Sheaf.Paper.SfIntegralConstructible: sfIntegralConstructible and its full category.
- Sheaf.SixFunctors.ConstructibleTensorCompletion: constructibleTensorCompletion,
  the actual quotient-map comparison normalized on total K-flat tensor sections.
- Sheaf.Paper.IntrinsicCompletionCompleted: IsCompletedIntrinsicallyDerivedComplete
  and the actual completed Koszul unit, reexported through the tensor dependencies.
- Sheaf.Paper.WfTensorCompletionFrobenius: Integral, ordinaryAmbient,
  completedAmbient, ordinary, completed, chi, ordinaryMu, completedMu, pullback,
  RationalComparison, Normalized, ordinaryPair, completedPair,
  wfTensorCompletionFrobenius and wfTensorCompletionCommonField.
- Sheaf.Paper.IntegralStratifiedPerfectCharacterization (publicly exposed because
  its canonical transport occurs in the signatures): integralDetailedLevelComparison,
  integralDetailedCoefficientComparison and integralDetailedTransport.
- Proof imports: RationalLatticeAdicDomain.rational_lattice_integral_comparison;
  IntegralOperationsPreserveConstructible.integralOperations_preserve_constructible;
  SfIntegralCompactSupportConstructible.sfIntegralCompactSupport_constructible;
  DerivedPullbackTensorHom.constructibleIntegralPullback/constructibleIntegralTensor;
  SfRationalizationKaroubi.sfRationalConstructibleLocalization;
  IntegralScalarExtensionConstructibleIntrinsic.sfIntegralScalarExtension_constructible.
- Sheaf.Paper.QcqsCompactSupportRealization: sfQcqsCompactSupportRealization and its
  existing PurCompactSupport completed proper/open realization.
- The recorded lem-fix-weil-operations module
  WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius is imported as a proof
  dependency. Its attached declaration isWeilPairing_mixedSupportCupProduct states
  the cup-product part on the etale module category; this delivery supplies the
  coefficient-domain bridge and tensor-map identification, not a second definition
  of all Weil operations or a proof of that entire downstream operations assertion.
- The proof-only node lem-wf-constructible-tensor-koszul-unit has no Lean record in
  the read snapshot. No nonexistent module is imported and no replacement theorem
  for that other node is invented; its role is included in the full proof docstrings,
  and the already recorded WfTensorCompletion interface supplies the needed types.

Searches actually run (no exact duplicate statement or definition found):

- msearch.py leanfinder: "Constructible completed coefficient categories ordinary
  completed tensor Frobenius Weil projection formula domain bridge". Eight hits:
  BDeRhamPlus, BDeRham, FontaineTheta and ordinary AdicCompletion tensor results.
  None states the project-specific domain bridge.
- msearch.py loogle: "IsIso, Functor". Service returned zero hits and the diagnostic
  "loogle: unknown identifier 'IsIso'"; this query is inconclusive, not a proof of
  absence. LeanFinder and direct source searches supply the useful search evidence.
- msearch.py leansearch: "Weil complexes completed tensor constructible projection
  formula". Eight hits, ordinary HomologicalComplex tensor and homology maps plus
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian, no exact match.
- msearch.py grep: "Weil.*[Cc]omplet|[Cc]omplet.*Weil", CategoryTheory: zero hits.
- Direct rg over Mathlib/CategoryTheory for that same expression: no hits.
- Direct rg over lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for the item id, projectionWeilTensorDomain and Weil/domain patterns: no bridge
  declaration. The broad domain pattern also returned unrelated integral-domain
  algebra nodes; these are not matches. Narrow source/name checks returned none.
- Source searches located WfTensorCompletionFrobenius, IntegralStratifiedPerfect-
  Characterization and the operation-normalization interfaces, all reused above.
  No new independent definition node is needed.

Edge cases read against the signatures: empty geometric scheme (no points required),
zero objects and zero tensors, f₀=id, exponent one (tower index zero), torsion integral
representatives, E=F=G and identity coefficient embeddings, arbitrarily larger common
finite field, arbitrary characteristic p and distinct ell, and rational Frobenius
multiplication by a negative uniformizer power. The rational/common tensor clauses
never demand an integral Frobenius isomorphism. Scheme and small-site universes stay
those of the recorded interfaces; the site object and morphism universes are not
identified by a new hypothesis. No statement dispute or source correction is needed.

Compilation: every delivered file is checked only with the prescribed scompile.py.
The final library and sandbox passes are both clean under the fixed 60-second limit;
all theorem proofs remain sorry. Initial elaboration failures were repaired by
unfolding the explicit geometric-fibre projection for its structure properties,
spelling CommRingCat.ofHom fully, and publicly importing the module whose canonical
transport appears in the public signatures.

## Second reading by Q01

A separate pass reopened the item and reread the complete final Lean file against
its statement. This is the author's second pass, not an independent-agent review;
the dispatcher prohibits starting another agent, and the maintainer supplies the
independent delivery review.

The pass checked D/c and arbitrary E against the coefficient hypotheses, separation
on X₀,Y₀ and f₀ against precisely the node's separation assumptions, and the explicit
Over.pullback map against geometric base change. It checked the quotient projection
equations and predicate equivalence rather than merely an equivalence of abstract
categories. It found that the first draft's equivariance theorem alone did not
state constructibility and comparison invertibility for integral pairs without Weil
maps: added sfProjectionWeilIntegralTensorDomains. It also found that a bare common-
stage Nonempty isomorphism lost the specified image arrow: replaced that clause by
an existential ebar with ebar exactly mapIso e. Finally it checked the main theorem's
five P,H,U,V,B clauses, their five datum equalities and five rational equalities,
then the scalar-domain and common-stage analogues. The ordinary/completed rational
map comparison is tied explicitly to wfTensorFrobenius by HEq, while the Weil
isomorphism's underlying arrow is literally normalized chi. All introduced theorem
proofs are exactly sorry, all definitions have actual data, and every declaration
has its source and owning-node proof docstring. No node correction, new node or
dependency record repair was made.
