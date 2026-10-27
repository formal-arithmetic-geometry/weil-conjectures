## Worker report

Repair of independent return e6758ebc294d, H3 and H4. The item now states
`WeilConjectures.HomChain.pairing_naturality` on the recorded
`PodCoefficientStage.domain S s` FullSubcategories and a given
`PodCtfAdjunctionData R`. The previous coefficient/Ctf/Bounded/inclusion/push,
tensorModel/internalHom/projectionModel, RestrictedPairing and Presentation
interfaces are gone. The theorem has exactly the same six identities. The item
has no statement correction. Its seven original stmt_deps are retained and
its stmt_deps gains only the new helper definition node def-pod-ctf-pairing-maps.

Hypothesis-by-hypothesis correspondence:

- `D : FiniteFieldDatum`, `C : D.CoefficientDatum`, the field E finite-dimensional
  over `Padic C.l`, and n with `hn : 1 ≤ n` supply precisely the finite-field and
  coefficient conventions of def-fix-six-functor-datum. S is the recorded
  `SixFunctorOperationDatum`.
- `s : PodCoefficientStage` selects finite, integral, rational or common
  coefficients using its existing domain, operations, tensor and internalHom.
  Integral operations are the completed operations of S.higher.integral;
  rational and common-stage operations are S.higher.rational and S.closure.commonStage.
- X and Y are `SixFunctorSpace D`, so are finite-type k-schemes. Their arrow
  `f : X ⟶ Y` is over k. `IsSeparated f.hom.left`, `LocallyOfFiniteType f.hom.left`
  and `QuasiCompact f.hom.left` express separated finite type. There is no
  extra separatedness assumption on the structure morphisms of X or Y.
- c is a compactification of f, as used by the operation datum. It is arbitrary.
  R is the supplied restricted-adjunction data on the existing four-stage
  categories; it is not chosen from the existence theorem.
- M is in `(PodCoefficientStage.domain S s X).FullSubcategory`, N and N' in
  the corresponding category on Y; r is any arrow N to N'. No alternative
  constructible category or free tensor-Hom adjunction is introduced.

Objects and maps:

- C is `R.support.obj M`; L_N is `inner S s f c R M N`, obtained by
  `PodCtfPairing.homX` from `sixFunctorDomainHom` applied to `R.exceptional.obj N`.
- A_N is `outer`, namely `R.direct.obj L_N`. B_N is `target`, using the same
  restricted Hom on Y with left input C. The definitions at N' are identical.
- h is `innerMap`, the Hom functor's image of `R.exceptional.map r`; a is
  `outerMap`, namely `R.direct.map h`.
- Evaluation is literally `(R.tensorAdjunctionX M).counit.app V`. The left tensor
  throughout is `@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M`,
  with the corresponding closedY tensor for C on Y.
- q applies that tensor functor to `R.ordinaryAdjunction.counit.app L_N` and
  then evaluates at `R.exceptional.obj N`.
- P_T is `PodCtfPairing.projection S s f c R M T`, the canonical forward
  projection, transported through R.tensorY, R.tensorX and the full inclusion.
  It is constructed from the published projection component, not an arbitrary map.
- p is P at A_N, followed by `R.support.map q`, followed by
  `R.exceptionalAdjunction.counit.app N`.

Clause-by-clause correspondence with `Naturality` (Lean's `≫` means first the
left arrow, then the right arrow):

1. `R.pull.map a ≫ ε(L_N') = ε(L_N) ≫ h` is the ordinary counit square.
2. `R.support.map (R.exceptional.map r) ≫ μ(N') = μ(N) ≫ r` is the exceptional
   counit square.
3. `tensorLeft M |>.map h`, followed by evaluation at f!N', equals evaluation
   at f!N followed by `R.exceptional.map r`.
4. `tensorLeft M |>.map (R.pull.map a) ≫ q_N' = q_N ≫ R.exceptional.map r`.
5. `P_A_N ≫ R.support.map (tensorLeft M |>.map (R.pull.map a))` equals
   `tensorLeft C |>.map a ≫ P_A_N'`.
6. `tensorLeft C |>.map a ≫ p_N' = p_N ≫ r`.

Dependencies read and used:

- def-fix-six-functor-datum: `Sheaf.Paper.SixFunctorOperationDatum`,
  `WeilConjectures.SixFunctorOperationDatum`, through the PodCtfAdjunctions import.
- fix-prop-adjunctions: `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`,
  its ordinary/exceptional and composition conventions; the stage functors and
  adjunctions themselves come from `SixFunctorPushStage` and R's constructed
  fully faithful restrictions.
- def-weil-derived-pullback-tensor-hom: `Sheaf.Paper.DerivedPullbackTensorHom`,
  sixFunctorFiniteHom, constructibleIntegralHom, rationalDerivedInternalHom and
  commonStageDerivedInternalHom, as selected by PodCoefficientStage.internalHom.
- det-thm-sf-ctf-stability-adjunctions: `Sheaf.Paper.PodCtfAdjunctions`;
  PodCoefficientStage.domain/operations/tensor/homPairs/internalHom and
  PodCtfAdjunctionData.pull/direct/support/exceptional, ordinaryAdjunction,
  exceptionalAdjunction, tensorAdjunctionX and closedX/closedY are now used
  directly. In particular the evaluation uses the recorded restricted adjunction,
  and the categories are its domain FullSubcategories. The shared Hom functor is
  `sixFunctorDomainHom` from `Sheaf.Paper.SixFunctorDatum`; no copy is made.
- fix-prop-projection-formula: `Sheaf.Paper.CompactSupportProjectionFormula`,
  compactSupportProjectionFormula and the canonical
  CompactSupportFiniteProjection.component / compactSupportProjectionComponent
  from `Sheaf.Paper.ConstructibleProjectionMates`. Only the forward component
  is needed by the six identities.
- def-exchange-projection: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage, through
  SixFunctorExchangeData. The existing HEq pins to the stage operations,
  adjunctions and tensors are used without any dependency-module changes.
- lem-pod-closed-uncurry-laws is a Mathlib leaf: MonoidalClosed.uncurry_curry,
  uncurry_natural_left and uncurry_eq in
  Mathlib.CategoryTheory.Monoidal.Closed.Basic, with ihom.ev its counit.
- Proof-only lem-weil-pbc-adjunction-of-natural-bijection is Mathlib
  Adjunction.mkOfHomEquiv. lem-pod-hom-chain-ctf-domains has no module to import.
  The postponed proof docstring records every proof step and its dependency.

Edge cases: r = identity gives identity images and the six identity squares.
Zero objects M, N or N' remain in the actual domains. Empty schemes are allowed;
f = identity is not excluded. n = 1 is allowed and n = 0 is correctly excluded.
No site universe equality, finite-reduction faithfulness or rational-to-finite
reduction is imposed. All four stages retain the recorded domains, tensor
comparisons and evaluation. The left-factor convention introduces no further
symmetry or sign.

Searches retained from the saved investigation (actual queries are in searches.jsonl):

- msearch.py leanfinder, "Naturality of projection formula pairing ordinary
  counit evaluation exceptional counit in target object": eight hits, including
  ihom.coev_naturality and ExactPairing.coevaluation_evaluation; no combined law.
- msearch.py loogle, "CategoryTheory.Adjunction.counit_naturality": three hits,
  including counit_naturality; only individual squares.
- msearch.py grep, "counit_naturality|uncurry_natural_right", in
  CategoryTheory/Monoidal/Closed: five hits; individual closed-category laws.
- msearch.py leansearch, "Naturality of the projection formula ordinary counit
  evaluation exceptional counit pairing in the target object": eight hits,
  including Adjunction.counit_naturality and ExponentiableMorphism.ev_naturality;
  no theorem with all six specified maps.
- rg of lean/WeilConjectures and lean/Sheaf for the item id, homChain,
  hom_chain, pairing_naturality and pairingNaturality found abstract chain and
  external evaluation results, not this combined statement. For this repair,
  read the live PodCtfAdjunctions source (also confirmed with scompile --source),
  SixFunctorDatum.sixFunctorDomainHom/SixFunctorClosedDomain, and the landed
  PodHomChainCounitFormula helpers. These are the canonical constructions reused.

## New nodes

`def-pod-ctf-pairing-maps` is the shared definition owner permitted by the
return. Its module `Sheaf.Paper.PodCtfPairingMaps` imports the landed
PodCtfAdjunctions and supplies the canonical constructions under
WeilConjectures.PodCtfPairing: rawProjection selects the published component at
each stage; rawProjectionIso uses the inverse uniquely determined by the recorded
projection theorem; projectionIso transports it through R.tensorY, the support
image of R.tensorX inverse and the full inclusion; projection is its forward
map; homX and homY fix the first input of
sixFunctorDomainHom. No definition has postponed data or introduces an independent
operation. No dependency node or module is changed. This is the definition-node
alternative explicitly requested by the return, owning the canonical constructions
without importing the downstream counit-formula theorem.

Its source is fix-lem-tensor-adjunction.proof.md Step 1 and the third paragraph
of thm-pod-identification-of-the-comparison. Blueprint ancestor search returns
that latter node; the new node records the path through this item. Searched
blueprint_refs for projection and restricted pairing and searched DAG nodes for
PodCtfPairing and the new id: no definition node owns this interface. The related
existing def-pod-derived-poincare-pairing is the global Poincare pairing and
def-sf-etale-chart-hom-chain is an etale chart Hom chain, not these operations.
The sibling PodHomChainCounitFormula exposes equivalent helper constructions
inside a theorem module whose proof cites this item; importing it would close
the cycle. The shared helper owner and the direct consumer probe avoid that cycle.

Fresh msearch queries for this definition node:

- LeanSearch: "Transport a projection formula morphism through full subcategory
  inclusions and tensor comparison isomorphisms", eight hits including
  ObjectProperty.liftCompιIso and cartesian projection comparisons; no combined
  four-stage restricted projection/Hom interface.
- LeanFinder: "Canonical forward compact support projection transported to
  finite Tor full subcategories and fixed left internal Hom functors", eight
  hits about LightCondensed internal Hom and condensed monoidal structures.
- Loogle: "CategoryTheory.Functor.preimage, CategoryTheory.Prod.sectR", zero hits.
- Mathlib grep: "preimageIso|def preimage" in CategoryTheory/Functor, nine hits
  including Functor.preimage and preimageIso; these constructions are reused.
- Source/project rg for rawProjection and PodCtfPairing found only the downstream
  sibling's helper constructions, plus unrelated ambient projection maps.

## Returned-delivery repair

- H4: removes the independent Presentation and RestrictedPairing machinery and
  uses R's recorded operations, restricted adjunctions, actual tensorLeft and
  evaluation. The canonical shared helpers now have the new definition node as owner.
- H3: uses exactly the PodCoefficientStage.domain FullSubcategories of the landed
  sibling. The forward projection is the same canonical map transported by
  R.tensorY and R.tensorX. A scratch consumer imports both theorem modules and
  checks equality with the sibling's homX/projection and applies conjunct six
  directly to its pairing; no new equivalence bridge is assumed.
- The saved packet's first required dry run failed with a 60-second dependency
  timeout locally and on the server. A direct forward-map trial compiled, but
  did not pass the definitional consumer equality check. The final shared owner
  retains the sibling's exact rawProjectionIso and
  projectionIso construction so that the canonical forward map agrees
  definitionally with the consumer; neither inverse is chosen arbitrarily.
  Profiling located the remaining timeout in the inherited general restricted
  theorem, which takes roughly 30 seconds in checking and again in linting.
  The final packet uses the return's permitted definition-node alternative and
  imports the already landed dependency, preserving it unchanged. The slow
  dependency is not split, edited or recompiled as part of this delivery.
- Earlier H2/H9/H13 repairs remain: the seven original stmt_deps are retained;
  no retired ConstructibleFiniteTorAdjunctions is imported or restored. Only the
  permitted shared definition owner is included as a new node/module.

## Second reading by Q11

Self-check under the explicit instruction not to start other agents. Read the
node and both modules against the maintainer's return. M/N/N' use R's categories;
L, A, B, h, a, evaluation, q and p use its actual functors and counits. Checked
all six compositions in order, especially the forward direction of projection
in clauses five and six. The new projection is the hom of the sibling's
transported isomorphism with exactly the same construction; the scratch consumer
checks this and direct use of the last conjunct. No independent tensor-Hom
adjunction, arbitrary projection, new hypothesis or changed node statement is
present. Existing dependency declarations and HEq normalizations are preserved by importing
the landed module. The new node states the shared projection/Hom constructions, with the projection
isomorphism obtained from the already recorded projection theorem. Only the item theorem is newly
postponed. All signatures disable automatic implicit variables.

Validation: scompile.py compiled each final module separately and then the
module-mode scratch ConsumerCheck. PodCtfPairingMaps passed in sandbox (44.9 s)
and library (31.4 s); HomChainPairingNaturality passed in sandbox (33.8 s) and
library (21.2 s). ConsumerCheck passed in sandbox (16.4 s) and library (15.6 s),
including rfl equalities for the sibling's homX and forward projection and
application of the sixth conjunct directly to its pairing. No compiler messages
were emitted. Checked both verbatim signatures, explicit variables and universes,
100-character Lean line limits, zero sorry in the helper module and one named
sorry theorem in the item. The packet has two modules, the item node, the new
definition node and this report; the scratch consumer is not delivered.
