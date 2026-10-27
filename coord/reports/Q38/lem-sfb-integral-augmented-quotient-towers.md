## Worker report

Item: lem-sfb-integral-augmented-quotient-towers, Q38, 2026-10-22.
Module: Sheaf.Paper.IntegralAugmentedQuotientTowers.
Main declaration: WeilConjectures.IntegralAugmentedQuotient.augmentedQuotientTowers.
The only postponed theorem is this declaration. All helper definitions contain real data;
all other helpers are abbreviations of published constructions. The natural-language
statement, proof, and proof dependencies are unchanged.

The previous run's unchanged-node rejection is addressed by supplying the missing Lean
record and module. The live node's reviewed field certifies its stage-1 split, while its
Lean record was null. No reviewed statement is re-recorded or replaced.

The statement uses natural isomorphisms of ordinary module functors into STRICT diagram
categories. This is an equivalent encoding of the asserted natural chain isomorphisms:
NatIso.mapHomologicalComplex applies them in every degree of every cochain complex,
and naturality for the differentials is exactly the chain condition. Evaluating the
strict diagram at op n then gives the node's beta, lambda, theta at exponent n+1.
No localization to a homotopy or derived category is used in this statement. No claim
is restricted to K-flat or bounded representatives. In particular this encoding does
not replace a strict chain isomorphism by per-degree cohomology isomorphisms.

Hypotheses, objects, and clauses:

- Prime ell: the explicitly bound l : Nat with [Fact l.Prime]. Finite E/Q_l:
  E : Type u, [Field E], [Algebra Q_[l] E], [FiniteDimensional Q_[l] E]. The
  published Padic.coefficientExtensionIntegers and its chosen uniformizer are used
  through pbcIntegralDatum, PbcIntegralRing and pbcUniformizer. The ULift only places
  coefficients in the value universe of the original small pro-etale site.
- Positive characteristic different from ell: k : Type u, [Field k],
  [Fact (ringChar k).Prime], [Fact (ringChar k != l)]. In a field these say precisely
  that the positive characteristic p is prime and differs from ell.
- Separated finite-type k-schemes and a k-morphism: X.Over, Y.Over, g.IsOver,
  IsSeparated for both structure maps, and LocallyOfFiniteType plus QuasiCompact
  for both. There is no condition on g beyond being over k.
- Sites and coefficients: modules W is reductionModules W ((datum l E).completedRing W)
  on ProEt.topology W, with object universe u+1 and morphism universe u. Its constant
  partner is exchangeConstantRing W (PbcIntegralRing l E). Positive n in the node is
  n+1 here, with n : Nat. redR and redC are the already constructed ordinary tensor
  quotient functors, not derived reductions. Their maps are the already specified
  residue transitions. res is the actual constant-function restriction.
- beta: beta W is OrderedExchange.ordinaryRho (datum l E) W, in the direction
  res H tensor_C S to res(H tensor_R S). Its defining ordinaryRho_existsUnique fixes
  s tensor x to s tensor x on EVERY local pure tensor, and includes naturality in
  modules and all quotient transitions. With a degree-zero quotient, the ordinary
  total tensor has just H^j tensor S in degree j and differential d_H tensor 1;
  applying this natural isomorphism termwise is exactly beta_{W,n,H}.
- The common quotient and its inverse: CommonQuotient explicitly requires an
  endomorphism mu of res M, acting on every local section by the constant section
  pi^(n+1), together with TWO isomorphisms from the SAME sheaf cokernel of mu.
  cokernel.pi mu followed by either isomorphism equals the appropriate actual
  quotient augmentation. The equation c.hom >> beta.hom = r.hom identifies beta
  with those two quotient identifications. Thus h tensor 1 goes to [h] on both
  sides. This also specifies the inverse on sections with nonconstant completed
  scalars; it never substitutes a quotient of sections for the sheaf cokernel.
  The theorem requires this for W=X,Y and for every term of EVERY unbounded H.
  Cokernels of complexes are degreewise; their quotient maps are chain maps.
  The augmentation equalities uniquely determine c and r (cokernel.pi is epi),
  hence force their compatibility with module maps and all differentials. Thus
  these are the asserted quotient-COMPLEX identifications, not unrelated
  per-degree isomorphisms lacking coherent maps.
- d_H: d is a natural isomorphism pullR >> res_X to res_Y >> pullC.
  PulledReduction.IsOrdinaryNormalized applied to d.inv fixes its scalar-insertion
  formula. On underlying inverse-image generators both sides insert the same
  section, so d is precisely the identity after the specified identifications.
  The normalization determines its inverse as well; d is not an arbitrary iso.
- T,U,V are exactly redR_Y >> towerPullR, pullR >> redR_X, and
  res_Y >> redC_Y >> towerPullC. Applying these functors degreewise gives the
  node's three ordinary tensor complexes at every level.
- lambda is the existential natural strict-tower iso a : T ~= U. Its full displayed
  generator equation sends insertion of s tensor x to the transported finite
  scalar tensor insertion of x, using the canonical finiteRingIso and
  proEtaleRingDirectImageMap. This fixes the comparison on all sheaf tensors.
- theta is DEFINED, not existentially unconstrained: whisker d across redR_Y,
  then whisker beta_Y.symm across towerPullC. The canonical composition comparison
  for whiskering inserts exactly the necessary rebracketing. Consequently its
  component is g_C^*(beta^-1) after d_{P tensor S}, in the node's direction.
- The constant balancing is c : V ~= (res_Y >> pullC) >> redC_X. Its final displayed
  augmentation equation identifies the pulled quotient unit with the quotient
  unit of g_C^*Q. Both are epimorphic sheaf cokernel maps; this condition specifies
  the canonical quotient comparison and therefore its formula on arbitrary
  pulled tensors. It is asserted only on Q=res P, exactly as in this node.
- Strict transitions: a, d, beta, theta, c are natural transformations/isomorphisms
  in actual module/diagram categories. Each component of a, beta, theta and c is
  a morphism of N^op diagrams, so it commutes with every residue transition,
  including identities and arbitrary composites. Existing redR and redC maps
  send s tensor x to reduced(s) tensor x. Naturality gives the differential
  compatibility without an additional flatness or boundedness assumption.
- lambda b_T=b_U is the first displayed forall M n equation: pullR of the
  completedReductionModuleUnit followed by a equals the completed unit on pullR M.
- theta res b_T=b_V d_P is the next equation: res_X of pullR of the completed
  quotient unit followed by the explicitly defined theta equals d followed by
  pullC of OrderedExchange.ordinaryAugmentation on res_Y M. These are actual
  module-map equalities, hence actual chain-map equalities in every cochain degree.
- Arbitrary complexes/non-K-flat tensors: H is any CochainComplex, j is any integer,
  and the comparison natural isomorphisms and augmentation equations quantify
  over all ordinary modules. There are no K-flat, flat, constructible, complete,
  or bounded hypotheses. Finite tensor complexes with nonflat terms are included.

Dependency declarations and modules read and used:

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing; imports the actual coefficientExtensionIntegers,
  coefficientExtensionUniformizer, coefficientExtensionRing constructions.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf;
  constant-section maps use the canonical toSheafify unit.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  AlgebraicGeometry.ProEtale.coefficientRing, condensedRingObj,
  condensedPullbackHom, coefficientPullbackIso, condensedPushforwardHom.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs:
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar and lowerStar, formed by the
  specified algebraic inverse image and scalar extension/restriction.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  compactificationOverField. Its separated finite-type over-field setting is
  rendered by the explicit scheme binders; no compactification hypothesis is added.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  SheafOfModules.restrictScalars; PulledReduction.res uses that actual restriction.
- Mathlib.Algebra.Homology.HomologicalComplex: CochainComplex.
  Mathlib.Algebra.Homology.BifunctorShift: CochainComplex.mapBifunctor.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  SheafOfModules.cochainModulesMonoidal, the existing sheaf tensor at independent
  site sizes. Imported as a proof dependency, without a duplicate tensor.
- Sheaf.CategoryTheory.FiniteTypeConstantExact:
  SheafOfModules.strictPerfectConstantSheaf_exact; imported for the recorded proof.
- Sheaf.Paper.PulledReductionComparisonData:
  PulledReduction.res, pull, insertion, IsOrdinaryNormalized, tres.
- Sheaf.Paper.AdicCoefficientDatum: reductionModules, reductionTensorSection,
  completedReductionModuleTowerFunctor, completedReductionLevel, and datum finite
  rings/projections. Sheaf.Paper.CompletedTowerPullback supplies completedModulePullback
  and completedReductionModuleUnit with its x maps to 1 tensor x normalization.
- Sheaf.Paper.ProEtaleConstantReductionModels: OrderedExchange.reductionModule,
  quotient, ordinaryAugmentation; all maps carry their prescribed residue formulas.
- Sheaf.Paper.OrderedExchangeCoefficientComparison:
  OrderedExchange.ordinaryRho and ordinaryRho_existsUnique, the existing beta.
- Sheaf.Paper.BoundedConstructibleComplete: PbcIntegralRing, pbcUniformizer,
  pbcIntegralDatum. Only these unconditional coefficient constructions are used;
  no noetherian/dimensional/bounded-constructible condition is imported as a hypothesis.

The six added stmt_deps are already landed interfaces which own these constructions:
def-weil-pbc-pulled-reduction-comparison-data, def-weil-pbc-adic-coefficient-datum,
def-weil-pbc-bounded-constructible-complete, def-sp-constant-reduction-models,
lem-weil-pbc-ordered-exchange-coefficient-comparison and def-weil-pbc-completed-pullback.
A targeted dependency-path audit found no path from any of them back to this item.
No dependency module or new node is introduced. The existing downstream
IntegralPullbackStrictRoosNormalization module is NOT imported: some of its aliases
have the same mathematical source notation, but the present aliases refer directly
to the underlying published constructions, avoiding a downstream dependency cycle.

Proof imports: the already-stated constant-exactness and tensor dependencies are
imported. lem-sfb-integral-coefficient-square-normalization currently has no Lean
record or module, so there is no module for that proof dependency to import. It is
not used as a hidden hypothesis or as a source of unspecified data: d is asserted
with its normalization in the present theorem itself, and all constructions already
have real published definitions. The DAG proof dependency is retained unchanged.

Edge cases checked before writing: zero complexes, empty schemes (possibly zero
coefficient sheaves), first positive level n=0 meaning exponent 1, arbitrary degrees
and unbounded complexes, torsion/nonflat terms such as S_m, and identity morphisms.
Cokernels and strict naturality work in all these cases. The finite quotient is
ordinary (S_m tensor S_n has the common min(m,n) quotient), not a derived tensor.
No characteristic-zero case or exponent-zero quotient is silently introduced.

Searches actually made:

1. msearch.py leanfinder, query: "A strict augmented tower of ordinary tensor quotients
   of module sheaf cochain complexes commutes with pullback and restriction of scalars
   preserving the tensor generator and quotient augmentation". Eight hits, including
   SheafOfModules.pullbackObjFreeIso and its normalization lemmas,
   PresheafOfModules.Monoidal.tensorObj/map, and rTensor.inverse_apply. No exact match.
2. msearch.py loogle, query: '"SheafOfModules", "pullback"'. Twelve hits, mainly
   PresheafOfModules.pullback, pullbackId, pullbackComp and adjunctions. No exact match.
3. msearch.py grep, query:
   '(pullback|restrictScalars).*(quotient|[Tt]ower)|(quotient|[Tt]ower).*(pullback|restrictScalars)'.
   Twenty-five hits in ordinary algebra, presheaf/constant sheaf and unrelated modules;
   no strict augmented sheaf-complex statement. A second grep for scalar/multiplication
   constructors in Algebra/Category/ModuleCat/Sheaf returned zero hits.
4. rg in lean/WeilConjectures and lean/Sheaf for augmentedQuotient, quotientTowers,
   quotient_towers, this blueprint id, and combinations of integral/coefficient/tower.
   No exact item statement. The broader search found existing strict scalar balancing,
   quotient construction, pulled reduction and downstream Roos normalization modules.
   Their full relevant declarations were read and reused where appropriate. The
   downstream theorem asserts additional Roos/derived-limit assertions and is not an
   exact existing match for this ordinary strict-tower node. The generic common-quotient
   presentation modules take additional ringed presentation data, and are not this
   specialized normalized result with no added hypotheses. No second construction
   of those data was introduced.

Source checks: read the current blueprint proof named by the node, and Stacks
sites-modules.tex lemmas constant-exact (093J) and completion-flat (093M), and
sites-cohomology.tex pullback-tensor-product (07A4). The source uses canonical
coefficient transport and quotient maps; no correction of this node is needed.
No STATEMENT-DISPUTED finding.

Validation: scompile.py compiled the module separately in sandbox and library module
contexts, with no errors or non-sorry warnings. The latest clean pass took 9.9 and
12.8 seconds respectively. The initial elaboration repair made the scalar action on
res M explicit, so the constant-ring action cannot accidentally be read as the
completed-ring action on M.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
