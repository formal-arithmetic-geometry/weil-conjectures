## Worker report

The delivery states `WeilConjectures.pointSectionsScalarExtension` in
`Sheaf.Paper.PointSectionsScalarExtension`. It supplies canonical constructions
needed to type the full assertion, including its integral and rational tower
coherence. Every theorem has a `sorry` proof. Definitions have actual data:
evaluation, scalar restriction, termwise tensor and exact-functor localization;
choices are made only from uniquely characterized maps or normalized universal
properties. All helpers are listed in their owning node's `lean.declarations`.

Source read: the server copy of
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-admissible/def-weil-finite-coefficient-point.md`,
including the last sentence about the stagewise functor and finite-stage colimit.
The local shared checkout does not contain this literature path. Its final
paragraph fixes the same global finite-field datum, algebraic closure of Q_l,
finite coefficient extensions, and geometric-point fibre functor as the node.
The node's six explicit proof steps specify the integral comparison, its strict
completion normalization, unit, associator and rationalization used here.

Hypothesis and conclusion correspondence:

- The global datum is `D : FiniteFieldDatum.{u}`; its fields provide p, a, q,
  k_0, k and the algebraic-closure instance. The geometric point is literally
  `Spec (.of D.k)`, with its small `Scheme.ProEt` site. The prime is `l : ℕ`
  with `[Fact l.Prime]`, and `hl : l ≠ D.p` retains the characteristic exclusion.
- `Q : Type u`, `[Field Q]`, `[Algebra ℚ_[l] Q]` and
  `[IsAlgClosure ℚ_[l] Q]` fix the specified algebraic closure. The final
  theorem uses `F G H : Padic.FiniteCoefficientFields l Q` and `hFG : F ≤ G`,
  `hGH : G ≤ H`. Their recorded finite-dimensional instances give precisely
  finite extensions in that closure. The field inclusions are exactly
  `IntermediateField.inclusion hFG` and `IntermediateField.inclusion hGH`.
  Generic auxiliary constructions accept arbitrary embeddings, allowing their
  identity specializations without a separate coefficient category.
- O_E and its quotients are the recorded `Padic.coefficientExtensionIntegers`
  and `coefficientExtensionRing`. `completedIntegralCoefficientSheafUnrestricted`
  is the same inverse limit as the recorded completion, with its auxiliary D and
  hl omitted only from its interface. `integralTowerModules` is modules over
  that completed sheaf, not the discrete constant sheaf. Every complex is
  unbounded in the ambient derived category.
- `K : completedIntegralDerivedCategory ...` and
  `hK : boundedConstructibleDerivedCompleteIntegral ... K` state exactly
  membership in D^b_c(s,O_E): completeness, all positive reductions constructible,
  and their single uniform cohomological interval. No separate boundedness,
  projectivity, torsion-freeness or finite-generation hypothesis is added.
- `integralScalarExtension` is the recorded strict Cone(1-s)[-1] descent with
  its `integralScalarExtensionOnGoodIso` on K-flat flat-term representatives.
  `integralScalarExtension_constructible` supplies
  membership of T_{L/E}K in the target constructible category wherever the
  second scalar extension or completion comparison needs it.
- `pointCompletedSections` evaluates at
  `op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))` and restricts coefficients by
  `pointCompletedConstant`. That ring homomorphism is uniquely fixed to the
  recorded constant section `integralScalarConstant` for every coefficient.
  `pointCompletedDerivedSections` is its exact termwise localization.
- `pointIntegralModuleTensor` is Mathlib `ModuleCat.extendScalars` along the
  recorded integer-ring inclusion. `pointIntegralModuleDerivedTensor` applies
  this ordinary tensor degreewise and localizes. It is not an independently
  chosen left-derived functor.
- `pointSectionsTensor_existsUnique` fixes the sheaf-level sections-tensor
  isomorphism by `a tensor n ↦ completedScalarTensorSection ... (constant a) n`.
  The tensor convention puts the coefficient on the left, canonically the same
  ordinary tensor as the node's right-coefficient notation. The representative
  equation in `pointOrdinaryDerivedComparison_existsUnique` identifies ordinary
  derived tensor with exact termwise tensor by its actual universal counit.
  `pointDerivedSectionsTensor` uses those exact-functor localization comparisons;
  it is precisely theta, natural on every derived morphism.
- `pointConstructibleCompletionIso` has hom exactly the canonical
  `completedScalarComparison` chi. `pointSectionsScalarExtensionIso` is, by
  definition, the inverse of theta followed by sections of that chi. Thus the
  requested isomorphism exists with the specified normalization, rather than
  merely an arbitrary isomorphism of its source and target.
- The final theorem's first conjunct is the naturality square for every
  morphism `f : K ⟶ J` of the full constructible category.
- Its second conjunct identifies phi for the identity inclusion with the
  identity after `pointIntegralModuleDerivedUnit` on sections and
  `pointIntegralScalarUnit` on the integral sheaf complex. The former is
  multiplication on ordinary tensors; the latter is chi inverse followed by
  ordinary derived multiplication. Both multiplications are uniquely fixed on
  pure tensors.
- Its third conjunct is exactly the node's integral tower equation in Lean's
  left-to-right composition order. `pointIntegralScalarAssoc` is chi for the
  second extension inverted, ordinary derived extension of the first chi
  inverted, the ordinary derived tensor associator, and the direct chi.
  `pointIntegralModuleDerivedAssoc` is the ordinary balanced coefficient-product
  associator. The ordinary sheaf associator, its module version and both units
  are uniquely specified on pure tensors before passing to derived categories.
- `pointModuleDerivedRationalization` tensors termwise with the fraction field.
  `pointDerivedTensorRationalization` is fixed by the balanced map
  `b tensor (a tensor n) ↦ ba tensor (1 tensor n)`, including its localization
  denominators. `pointRationalSectionsScalarExtensionIso` tensors integral phi
  with L and follows this canonical map, giving the stated isomorphism in D(L).
- The fourth conjunct gives its naturality. The fifth and sixth give the same
  identity and composition equations over the fields, using the ordinary
  `ModuleCat.extendScalarsId` and `extendScalarsComp` associators descended to
  derived categories. Thus neither rational coherence clause is omitted.

Dependency interfaces read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  closure field instances.
- `Sheaf.Paper.CompletedIntegralCoefficients`:
  `completedIntegralCoefficientSheafUnrestricted`, the finite coefficient system
  and projections, `completedIntegralDerivedCategory` and its commutative enhancement.
- `Sheaf.Paper.DerivedCompleteIntegralDetailed`:
  `boundedConstructibleDerivedCompleteIntegral` and its full subcategory.
  The currently recorded `Sheaf.Paper.SfIntegralConstructible.sfIntegralConstructible`
  (declaration namespace `WeilConjectures`) is imported and matched explicitly
  by `pointIntegralConstructible_iff` on this same completed coefficient category.
- `Sheaf.Paper.IntegralScalarExtension`: `integralScalarExtension` and
  `integralScalarExtensionOnGoodIso`, selected from normalized unique descent in
  `IntegralScalarExtensionWellDefined`; its integer inclusion and constant sections
  also supply the coefficient actions here.
- `Sheaf.Paper.IntegralScalarExtensionConstructible`:
  `integralScalarExtension_constructible`, the actual full-subcategory
  `constructibleIntegralScalarExtension`, and its canonical action-linearity theorem.
- `Sheaf.Paper.PointProEtaleSectionsExact`:
  `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact` and the actual
  `pointModuleSections` evaluation. Its clauses state abelian surjectivity, exact
  module evaluation, quasi-isomorphism preservation, derived factorization, shift
  and triangle compatibility, and natural cohomology comparison.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedOrdinaryScalarExtension`, `completedDerivedScalarExtension`, its universal counit,
  `completedScalarComparison` with both strict cone-coordinate formulas,
  `finiteFreeCompletedScalarComparison` and its identity normalization.
- `Sheaf.Paper.DerivedCompleteUnrestricted`: the same augmented Roos-completeness
  condition at the interface used by the finite-free comparison. The old
  finite-field-indexed completeness predicate remains in its owning module.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`:
  `Padic.FiniteCoefficientFields` and its finite-dimensional instance. This
  already recorded dependency is added to the item's statement dependencies
  solely to express the fixed-closure convention without duplicating its notion.
- Mathlib `SheafOfModules.evaluation`, `ModuleCat.restrictScalars`,
  `ModuleCat.extendScalars`, `extendScalarsId`, `extendScalarsComp`,
  `Functor.mapDerivedCategory`; upstream exact-functor composition, natural
  isomorphism, and identity comparisons transport the actual termwise maps.
  The continuous-coefficient, tensor, K-flat-resolution, change-of-rings and
  DVR proof modules are imported for the six-step proof plan.

Edge cases checked: zero K; the first quotient n=0 meaning positive exponent
one; complexes extending in both directions before the constructibility predicate;
identity field inclusions; fully ramified extensions with different uniformizers;
ell=2; arbitrary characteristic p with only ell≠p; arbitrary finite towers in the
fixed closure; integral torsion objects and denominators after rationalization.
No basis is added as a hypothesis. The schemes and coefficient fields fit one
common arbitrary universe u; the small site still has object universe u+1 and
morphism universe u, and section modules live in u+1. Neither site universe is
collapsed to the other. D's fields and each finite subfield of Q are in that
common universe; this places no finite-type or geometric restriction on the datum.

Searches actually run:

- msearch LeanFinder: “Global sections on an algebraically closed point commute
  with finite scalar extension of complete integral l-adic coefficients”. Eight
  hits concerned adic-completion algebra maps and scheme residue-field evaluation;
  none states the completed pro-etale comparison or its coherence.
- msearch Loogle: `SheafOfModules.evaluation, ModuleCat.extendScalars`. No hits.
- A second exact-name Loogle query `ModuleCat.extendScalars` returned twelve
  hits, including the functor, its adjunction, and its identity/composition
  isomorphisms. These exact ordinary module constructions are reused above;
  they do not state the completed pro-etale sections comparison.
- msearch grep: `globalSections.*[Tt]ensor|[Tt]ensor.*globalSections|SheafOfModules.*evaluation`.
  Two hits identify sheaf-module evaluation and its limit implementation; neither
  states scalar-extension compatibility.
- msearch LeanSearch: “Global sections of proetale sheaves at an algebraically
  closed field commute with finite free coefficient extension”. Service unavailable
  with Internal Server Error; no claim of a negative mathematical result is made.
- rg of upstream WeilConjectures for the item id, `pointSectionsScalarExtension`,
  `pointSectionsTensor`, and `pointCompletedSections`: no matching declaration.
  A broader pro-etale/global-sections tensor search returned adjacent six-functor
  material, not this completed integral sections comparison. The same name/concept
  search in `lean/Sheaf` found no complete statement.
- `scompile.py --source` confirmed the initially unrecorded scalar, finite-free,
  and point-section modules unavailable under the first guessed names. Read-only
  server delivery-branch inspection found Q04/Q08/NB interfaces. Their signatures
  and full docstrings were read before reuse, replacing the older Q10/NN drafts.
  The current Q42 finite-free module supplies the canonical comparison. No second definition of a published notion is introduced.

No statement correction or mathematical dispute is needed.

## Published dependencies refreshed

A fresh server source query found that Q42's finite-free comparison and Q04's
independent-universe scalar extension landed while this worker packet was checked.
The shared checkout's node records lagged behind those published sources. I read
both current modules and the current derived-completeness module in full. Their
canonical maps retain the quotient and zero shifted-product normalization, actual
ordinary and derived tensor functors, universal counit, and identity comparison.
The scalar extension also retains the published `integralScalarExtensionOnGoodIso`
name as an alias of `integralScalarExtensionComparison`.

This packet now delivers only the main module and item node. The four inherited
dependency copies and node edits were removed. It imports the current published
`completedOrdinaryScalarExtension`, `completedDerivedScalarExtension`,
`completedCoefficientMap`, `completedScalarCounit` and `completedScalarComparison`.
The counit is the published morphism on a cochain representative. The sections
comparison is normalized by that exact counit; no replacement is chosen.
The published unrestricted completeness predicate uses an auxiliary small
finite-field datum existentially; this changes no completeness condition because
the actual rings, reductions, and their canonical augmentations ignore that datum.
The main helper applies the finite-free comparison to the equivalent condition.

Published `Sheaf.Paper.PointProEtaleSectionsExact` and its recorded declaration
`AlgebraicGeometry.ProEtale.point_proEtale_sections_exact` are reused directly.
The current constructibility interface is `Sheaf.Paper.SfIntegralConstructible` /
`WeilConjectures.sfIntegralConstructible`; it is publicly imported and compared
with the equivalent finite-field interface by `pointIntegralConstructible_iff`.
The latter is required by the published preservation theorem. No predicate is
redefined and no mathematical node statement is changed. There are no new nodes.

## Validation

All modules are compiled individually through the prescribed `scompile.py` wrapper.
The earlier errors were the missing algebraically closed instance for D.k; this
is supplied directly by `IsAlgClosure.isAlgClosed D.k₀`, with no extra hypothesis.
All theorem proofs remain `sorry`, and node signatures and declaration inventories
are extracted from the final files. The worker runs `deliver2.py --no-push`; the
independent second reader supplies its own reading and performs delivery.

## Resumed worker checks

The inherited second-reading text has been removed from this worker packet so
that the next independent reader can write the reading of this final version.
The source blueprint was opened again on the server, including its final
stagewise-colimit paragraph. Searches were rerun with msearch LeanFinder
("Global sections at an algebraically closed point commute with finite free
extension of completed integral coefficients"), Loogle (`ModuleCat.extendScalars`),
and grep (`sections.*scalar|scalar.*sections|globalSections.*tensor`). They return
residue-field evaluation/adic completion, the ordinary reused scalar functors,
and unrelated manifold sections respectively, with no exact statement. Direct rg
of upstream and the shared Sheaf library found no main declaration match.

## Second reading by N0

I independently read the item statement, its six proof steps, all eight statement
interfaces, and the full delivered module. I read the actual source blueprint
`def-weil-finite-coefficient-point.md` on the server: its opening fixes the finite-field
and coefficient datum, and its last paragraph requires the same evaluation functor
stagewise before the finite-stage colimit. This item makes the needed scalar coherence
explicit. I also read Stacks `proetale.tex`, the equivalence in
`lemma-w-local-strictly-henselian-extremally-disconnected` (0982) and the statement and
proof of `lemma-w-contractible-is-weakly-contractible` (098H). The latter is a big-site
statement; the delivered point-exactness dependency explicitly supplies the small-site
result rather than silently restricting arbitrary big-site sheaves.

My object, hypothesis and conclusion checklist, in node order:

1. Global datum p,a,q,k_0,k: `D : FiniteFieldDatum.{u}`. I opened its structure;
   primality, positive exponent, cardinality, fields, inclusion and algebraic closure
   are its fields. `pointDatumIsAlgClosed` derives the needed closure instance from
   `IsAlgClosure.isAlgClosed D.k₀`; it adds no hypothesis. Verdict: exact.
2. Prime ell different from p: `(l : ℕ) [Fact l.Prime]` and `(hl : l ≠ D.p)`.
   These section variables are bound and used by the final theorem. Verdict: exact.
3. Fixed algebraic closure of Q_l: `(Q : Type u) [Field Q] [Algebra ℚ_[l] Q]
   [IsAlgClosure ℚ_[l] Q]`. Finite subextensions and the tower are `F G H :
   Padic.FiniteCoefficientFields l Q`, `hFG : F ≤ G`, `hGH : G ≤ H`. I read the
   subtype definition and its finite-dimensional instance. The maps are literally
   `IntermediateField.inclusion`, with composite for F to H. Verdict: exact;
   the extra tower field imposes no restriction on a pair (take H = G).
4. s = Spec k and its small pro-etale site: every occurrence is `Spec (.of D.k)`;
   sections evaluate at `op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))`.
   Verdict: exact, with the actual terminal object.
5. Completed coefficient rings R_F: `integralTowerModules` uses
   `completedIntegralCoefficientSheafUnrestricted`, the inverse limit of constant
   positive quotient sheaves. I read `CompletedIntegralCoefficients` and the currently
   recorded `CompletedIntegralCoefficientGerm`, including `integralConstantToCompletion`.
   Verdict: exact completion, with no discrete-constant replacement.
6. K in D^b_c(s,O_E): `K : completedIntegralDerivedCategory ...` and
   `hK : boundedConstructibleDerivedCompleteIntegral ... K`. I read that predicate:
   derived completeness, constructibility of every n+1 reduction, and one common
   integer interval, without a termwise boundedness condition. The recorded
   `sfIntegralConstructible` is also publicly imported; `pointIntegralConstructible_iff`
   states the bridge between the two recorded canonical reduction interfaces.
   Verdict: same full subcategory; no flatness, torsion-freeness or extra finiteness.
7. T_{L/E} and its preserved constructibility: the module uses the published
   `integralScalarExtension` and `integralScalarExtension_constructible` directly.
   I read the normalized-descent definition and retained good-complex comparison.
   The latter preservation theorem provides hK for the second extension in the tower.
   Verdict: the specified strict Roos tower, not an arbitrary derived-limit object.
8. Termwise derived sections: `pointCompletedSections` is Mathlib evaluation followed
   by restriction along the canonical integral scalar map; `pointCompletedDerivedSections`
   is its `mapDerivedCategory`. Exactness is supplied as a named theorem using
   `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact`. Verdict: exact termwise
   descent on unbounded ambient complexes.
9. Module tensor is ordinary termwise tensor: `pointIntegralModuleTensor` is
   `ModuleCat.extendScalars` along `integralScalarIntegerInclusion`, and
   `pointIntegralModuleDerivedTensor` is its exact-functor localization. The coefficient
   is written on the left by Mathlib's convention. Verdict: the same balanced tensor.
10. Existence and normalization of phi: `pointSectionsTensor_existsUnique` fixes theta
    on every pure tensor by `completedScalarTensorSection` with constant coefficient.
    `pointOrdinaryDerivedComparison_existsUnique` fixes the derived identification by
    the published `completedScalarCounit` on every representative. The definition
    `pointDerivedSectionsTensor` composes these actual localization comparisons.
    `pointConstructibleCompletionIso` has hom exactly `completedScalarComparison`;
    `pointSectionsScalarExtensionIso` is exactly the inverse of theta followed by
    sections of this chi. Verdict: the required actual isomorphism, not mere Nonempty.
11. Naturality in every constructible derived morphism: conjunct 1 of
    `pointSectionsScalarExtension` quantifies J, its constructibility proof and every
    `f : K ⟶ J` and gives the naturality square. Verdict: exact full-subcategory
    naturality, including arbitrary roofs rather than just chain maps.
12. Identity: conjunct 2 compares phi to `pointIntegralScalarUnit` after
    `pointIntegralModuleDerivedUnit`. The former is chi inverse followed by derived
    multiplication; both ordinary multiplications are fixed on pure tensors.
    The dependency's identity normalization identifies chi with completeness.
    Verdict: precisely the stated multiplication/completeness identification.
13. Integral tower: `pointIntegralScalarAssoc` is, in order, chi for L to M inverted,
    derived extension of chi for E to L inverted, the balanced ordinary associator,
    and chi for E to M. Conjunct 3 reads Gamma(a_int) then phi_{M/E} on the left;
    on the right it reads phi_{M/L}, tensor of phi_{L/E}, and a_mod. Verdict: exactly
    the displayed node equation in Lean's left-to-right composition convention.
14. Rational comparison: `pointModuleDerivedRationalization` tensors termwise with
    the fraction field. `pointTensorRationalization_existsUnique` fixes the map by
    b tensor (a tensor n) to ba tensor (1 tensor n), and its docstring checks
    denominators and inverse maps. `pointRationalSectionsScalarExtensionIso` is
    integral phi tensored with L followed by that map. Verdict: the stated D(L)
    source and target, with no torsion-freeness assumption.
15. Rational naturality, identity and composition: conjuncts 4, 5 and 6 respectively.
    They use the same integral unit/associator on the source and the descended
    Mathlib `extendScalarsId` and `extendScalarsComp` on the field-module side.
    I opened these Mathlib declarations and the upstream exact-localization
    `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, `mapDerivedCategoryIdIso`.
    Verdict: all clauses present with the correct directions and canonical maps.

Edge cases: zero complexes are allowed (the zero support fits any common interval);
no representative is assumed bounded or K-flat as a hypothesis. The n=0 tower index
means exponent one, as the dependency definition specifies. There is no arbitrary
index set in this item, and the base is a spectrum of a field, so empty schemes are
outside its hypotheses. Identity inclusions and repeated fields in towers are
included, as are ell=2, every p different from ell, ramified towers and torsion
modules. Rationalization correctly kills torsion without first excluding it. The
common universe u is arbitrary and matches the finite-field/coefficient convention;
the actual small site retains object universe u+1, morphisms u, coefficients/modules
in u+1, and the standard unbounded derived localization. No equality of site object
and morphism universes is imposed. Every universe and binder is explicit or bound by
a section variable with `autoImplicit false`.

Independent duplicate searches used different wording from the worker:

- msearch LeanFinder: “Evaluation at the terminal object commutes with finite free
  change of complete l-adic coefficient rings on the pro-etale site of an algebraically
  closed point”. Eight hits were adic-completion evaluation/factor maps and BDeRhamPlus;
  none is the sheaf comparison or its coherence.
- msearch Loogle: `ModuleCat.extendScalars, "comp"`. Eight hits include the reused
  ordinary `extendScalarsComp`, its unit laws and pseudofunctor; no completed sections
  comparison. Their actual source signatures were opened.
- msearch grep: `(evaluation|sections).*(extendScalars|[Tt]ensor)|extendScalars.*(evaluation|sections)`.
  Eleven hits concerned manifold tensoriality, coevaluation and monoidal evaluation,
  without the completed integral comparison.
- msearch LeanSearch: “Global sections of complete integral proetale modules commute
  with finite free scalar extension and composition of coefficient inclusions”. This
  time the service worked: eight hits concern generating sections, free module sheaves,
  pullback of free summands, polynomial laws, and scalar descent, with no exact match.
- Direct rg by names and by sections/scalar/tensor concepts in Mathlib, upstream
  WeilConjectures and lean/Sheaf found no existing main theorem. I opened adjacent
  `PointSectionsFiniteness`: its integral section functor lands over `ULift O_E` and
  its theorem asserts cohomological finiteness, not scalar comparison or coherence.
  The present unlifted coefficient functor and ordinary module tensors are the explicit
  size transport needed by this node, not a replacement coefficient sheaf. The ringed
  topological-point tensor material is also on a different site.

Mismatch found and repaired: the current completed-coefficients dependency record
points to `CompletedIntegralCoefficientGerm.integralConstantToCompletion`, while the
packet imported the older owning module and separately bundled the sectionwise
`integralScalarConstant` using a new unique-existence theorem. I changed the public
import to the recorded germ module, and made `pointCompletedConstant` the direct
composite of its `integralConstantToCompletion`, the actual constant-sheaf unit,
and the inverse ULift ring equivalence. Their finite quotient projections are the
same constant residues, so this changes no scalar action or theorem meaning. The
now unnecessary `pointCompletedConstant_existsUnique` theorem was removed and the
node's declaration inventory refreshed. The main theorem signature is unchanged
and remains verbatim equal to `lean.statement`.

All other reviewed constructions were retained. No new node, dependency module,
statement correction or citer audit is needed. Definitions contain real data;
remaining choices of maps/isomorphisms have explicit unique normalization, and each
remaining postponed theorem is owned by this node, has a source/blueprint docstring
and a proof plan. Every theorem proof is `sorry`. The main docstring follows all six
DAG proof steps, including the integral associator and the rational denominators.

Validation of the repaired version: the prescribed `scompile.py N0
lem-weil-point-sections-scalar-extension` invocation compiled the single delivered
module in both sandbox and library positions with exit 0, no errors and no warnings.
The signature and 58-declaration inventory were checked with the project's declaration
reader; `lean.statement` is verbatim equal, every line is at most 100 characters,
and the fourteen theorem bodies are exactly `by sorry`.
