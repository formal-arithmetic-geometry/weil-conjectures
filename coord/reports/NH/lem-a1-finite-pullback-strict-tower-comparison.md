## Worker report

The delivery states `WeilConjectures.FinitePullbackStrictTower.finite_pullback_strict_tower_comparison`
in `Sheaf.Paper.FinitePullbackStrictTowerComparison`. Its conclusion is a `Comparison`,
which retains the actual strict diagrams and their transition maps, the natural
isomorphism on the entire unbounded derived category, and the normalized representative
zigzag. This is statement work: the comparison theorem and its helper existence
and compatibility theorems have `sorry` proofs with source/proof docstrings. Constructions
use actual limit cones, the canonical adjunction, existing tensor complexes and existing
finite inverse images.

Hypotheses and clauses, read against the JSON statement:

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite E/Qell: `(E : Type u) [Field E] [Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]`. The coefficient integers, uniformizer and
  finite quotients are the recorded Padic constructions, never additional input data.
* Arbitrary schemes and morphism: `{X Y : Scheme.{t}} (g : X ⟶ Y)`.
  Invertibility on both schemes is exactly `hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`
  and the corresponding `hY`.
* Small pro-etale sites and completed coefficients: `Modules l E W` is `SheafOfModules` on the actual
  `completedIntegralCoefficientSheafUnrestricted`. This is definitionally the same
  category as `integralTowerModules`, with the original completed commutative ring.
  Its coefficient size is `max u (t+1)`; site objects remain size t+1 and arrows size t.
  No relation between u and t is imposed.
* The constant positive quotients are `integralCoefficientSheaf l E W n`, where n
  denotes exponent n+1. `PrincipalKoszulStrictReplacement.residue` restricts the
  quotient unit module along the specified `limit.π`, rather than along another map.
* The structural map is `CompletedTowerIndependent.directRingMap`, the adjoint of
  c_g: its nth component is the source limit projection followed by the canonical
  coefficient direct-image map. Compatibility gives the actual map to the target
  limit. `pull` is the left adjoint to pushforward through that map. Thus `G` is
  ordinary ringed-topos pullback, with its unit fixing its tensor generators.
* `integralOperationsGoodComplex` means independent-coefficient K-flatness AND
  flatness of every term. There is no boundedness condition.
* `finiteComplex` is the published `integralOperationsPullbackTowerFunctor` followed
  by the existing transposition; hence its levels are exactly Res_n g_n^*(P_n)
  with the published quotient transitions. No freely chosen diagram maps occur.
* `Comparison.B : DerivedPair ... finiteComplex` gives the derived functor, its
  universal counit and its invertible computation map on every good P.
  `Comparison.b : pulledReduction ... ≅ B.functor` is a natural isomorphism of
  functors on the WHOLE derived category. Thus naturality includes arbitrary
  derived morphisms and independence of representative, not just chain maps.
* `H` and `augmentation` alias the recorded principal Koszul strict replacement.
  It has degrees -1,0, exponent n+1, transition (t,1), and the quotient augmentation.
  `diagramPull` applies the SAME ordinary G at all levels and arrows.
* `koszulIso`, `balancedIso`, and `middle_quasiIso` give exactly the three arrows
  of the specified zigzag. `pull_good` and `koszul_pull_good` assert flat-term
  K-flatness of GP and all G(P tensor Q_n). The middle arrow is the actual
  augmentation applied to GP, and is a levelwise quasi-isomorphism.
* `reductionIso` identifies the published scalar-extension reduction with P tensor
  S, and `ReductionNormalization` fixes this identification on arbitrary tensor
  sections. `reductionH_normalization` fixes the map from derived reduction to
  H(P) by its composition with the actual augmentation and the universal counit.
  `zigzag` equates b, using those computation maps, to the displayed strict zigzag.
* `KoszulNormalization` fixes both Koszul summands on pullback tensor generators,
  with the scalar in the first variable. `BalancedNormalization` fixes the last
  isomorphism by ((x tensor b) tensor 1) ↦ x tensor pi_n(b). Linearity and local
  surjectivity of pi_n give ((x tensor b) tensor a) ↦ x tensor pi_n(b)*a for every
  local a. Balancing gives the inverse inserting 1. These are the finite evaluation
  comparisons of the imported interfaces, characterized by their section formulas;
  this does not introduce an arbitrary evaluation automorphism.
* The shift fields fix the chain shifts at each level by
  `mapCochainComplexShiftIso`, descend them through the universal counits, and
  assert the displayed equality of morphisms for every K and every integer r.
  The order is Lean's `b(K[r]) ≫ sB = sV ≫ b(K)[r]`.
* There is no assumption that c_g is invertible and no exactness assumption on G.
  All extra fields of Comparison are conclusions, not premises.

Dependency declarations used (module — declaration):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` —
  `Padic.finite_coefficientExtensionRing` and the imported coefficient-extension
  integer, uniformizer and quotient definitions.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` —
  `integralConstantToCompletionOfUniverses`; the imported
  `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`, `integralCoefficientSheafSystem`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic` — `DerivedCategory`, `DerivedCategory.Q`,
  `HasDerivedCategory.standard`.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` —
  `CochainComplex.IsKFlatIndependentCoefficients`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` — `SheafOfModules.IsFlatOnSite`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
  `Mathlib.Algebra.Homology.BifunctorShift` — the existing total tensor and shifts.
* `Sheaf.Paper.AdicCoefficientDatum` — the published adic datum and strict reduction
  interfaces; its live node record is restored byte-identically.
* `Sheaf.Paper.IntegralCompletedTowerPullbackUniverses` — `Modules`, `Towers`, `transpose`,
  `DerivedPair`, `reductionComplex`, `reductionPair` in
  `WeilConjectures.CompletedTowerIndependent`.
* `Sheaf.Paper.PbcQbarCompletedPullback` — original completed-pullback interface,
  retained by public import with its live node record byte-identical. The new
  specialized definition module gives
  the same ordinary/strict-derived construction at independent coefficient size:
  `directRingMap`, `pull`, `adjunction`, `towerPull`, `derivedPull`, `derivedCounit`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantExact` —
  `Scheme.coefficientProEtaleConstantModuleInverseImage`.
* `Sheaf.Paper.SfImmersionCompletedPullbackComparison` and
  `Sheaf.Paper.CompletedPullbackReduction` — recorded finite evaluation and
  completed pullback comparisons; their normalization is the balanced formula.
* `Sheaf.Paper.IntegralOperationsWellDefined` — `integralOperationsGoodComplex`,
  `integralOperationsPullbackTowerFunctor`, `integralOperationsLevelPullback`,
  `integralOperationsPullbackGenerator`, and its additive instance theorem.
* `Sheaf.Paper.IntegralReductionTowerUnrestricted` — `integralTowerModules`,
  `unrestrictedIntegralReductionFunctor`, `unrestrictedIntegralComplexFunctor`,
  `unrestrictedIntegralTransition`, `unrestrictedIntegralTensorSection`.
* `Sheaf.Paper.PrincipalKoszulStrictReplacement` — `koszul`, `multiplication`,
  `sourceTower`, `targetTower`, `comparison`, `residue`.
* `Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel` —
  `PrincipalQuotientCompletion.transpose`.
* `Sheaf.Paper.CoefficientRingedTensorHomModel` — `coefficientTensorGenerator`.

The proof-only imports follow every recorded proof dependency, including
K-flat resolution, change of rings, diagram K-flat replacements, canonical
ringed tensor pullback, cochain tensor coherence, constant ring maps,
independent-coefficient tensor descent and the resolving-class theorem. The
main docstring gives the node's nine proof steps, including normalization and
localization of shift identities. No proof dependency is replaced by a hypothesis.

Edge cases checked: empty source or target schemes (the stalk hypotheses are
vacuous where appropriate); identity morphisms; zero complexes; unbounded complexes;
first quotient n=0 meaning positive exponent 1; r=0, positive and negative shifts;
site/field universes unrelated; no assumption that inverse image preserves the
infinite limit; arbitrary coefficient action, rather than replacing c_g by an iso.
The two cone basis maps use the actual mapping-cone inclusions, so the degree -1
summand and its shifted signs are retained.

Searches performed before introducing interfaces:

* msearch.py leanfinder: "Derived pullback of strict completed reduction towers
  agrees naturally with exact finite coefficient pullback and shifts" — eight
  general shift/pullback results, none the strict-tower normalized comparison.
* msearch.py loogle: "SheafOfModules.pullback" — twelve ordinary module pullback
  declarations, no completed strict tower comparison.
* msearch.py grep: "strict.*tower.*pullback|StrictTower.*Pullback", CategoryTheory —
  no match.
* rg in Mathlib, WeilConjectures and Sheaf for the item ID and finite/strict/tower
  comparison names — no duplicate theorem. Read the related published
  CompletedTowerPullback, CompletedPullbackReduction, IntegralOperationsWellDefined,
  PrincipalKoszulStrictReplacement and the integral interfaces before reusing them.
* Existing DAG nodes and their recorded signatures show that strict reduction and
  tower pullback are existing notions. The specialized independent-size helpers
  now belong to the new specialized definition node, as permitted by the latest return;
  neither general dependency node is rebound to an O_E special case.

The definition owners `def-a1-flat-term-kflat-complex`,
`def-pur-integral-finite-pullback`, `def-a1-principal-completed-koszul-towers`,
`def-pur-principal-quotient-completion-model`, `def-coef-ringed-tensor-hom-model`
and `def-weil-integral-reduction-tower`, together with the new existing-definition
owner `def-a1-integral-finite-pullback-tower`, are in stmt_deps. The theorem
`lem-pur-integral-operations-well-defined` is not a statement dependency.
No statement correction or disputed mathematical statement is asserted.

## Returned delivery repair (da39d42ea06e)

Both dependency copies, `def-weil-pbc-adic-coefficient-datum` and
`def-weil-pbc-completed-pullback`, are byte-identical to the current live files.
Their declaration bindings, original notes, and all supporting metadata are retained.
They introduce no dependency-record delta in this delivery. In particular, the
Noetherian A/I^n datum is not rebound to O_E, and the Rlim completed-pullback
interface is not rebound to its strict-tower part. The obsolete §1(B) helper modules
are removed from the packet.

As the return explicitly permits, the `CompletedTowerIndependent` helpers now
belong to the new node `def-a1-integral-completed-tower-pullback-universes`, in
`Sheaf.Paper.IntegralCompletedTowerPullbackUniverses`. Each is listed in that
node's `lean.declarations` with its source and owning blueprint docstring. The
item cites this node and imports its module.
They provide exactly the specialized construction the comparison uses, without
claiming to replace either general dependency. `reductionPair` and `derivedPull`
have explicit result types, as does `derivedCounit`. Their choice is through a
universal left-derived counit, determining the object up to the canonical
counit-compatible isomorphism. The finite structural map remains constructed by
the actual limit cone, never selected as an unconstrained map.

The new existing-definition owner now also lists
`WeilConjectures.integralOperationsPullbackTransition_existsUnique` in
`lean.declarations`. It continues to use the published canonically characterized
transition; no new transition or extra hypothesis is introduced.

The item retains the reviewed comparison signature and every `Comparison` field.
The prior repair remains: `lem-pur-integral-operations-well-defined` is absent from
stmt_deps, and the flat-term K-flat, finite pullback, principal Koszul and new
strict finite-pullback tower definition owners are cited. There is no statement
correction and no disputed statement.

## Second reading by NH

This is a second pass by the same worker. The dispatcher prohibits starting other
agents, so no independent-worker review is claimed; the maintainer independently
reviews the delivered head.

Read the item statement, its complete `Comparison` record and theorem, all moved
helpers, and the existing-definition owner against the published transition
characterization. The item theorem and the comparison record retain the previously
reviewed binders, full derived naturality, normalized three-arrow zigzag, both
flat-term K-flat assertions, and all counit-normalized integer-shift equations.
Only helper placement, import ownership, explicit helper result types, and
metadata change. Empty schemes, zero/unbounded complexes, n=0 (exponent 1),
identity maps, noninvertible c_g, unrelated site/coefficient universes, and r=0,±1
remain admitted. The first and last zigzag arrows retain their tensor-generator
normalizations, and the middle arrow remains the actual quotient augmentation.

The defect found is the H13 rebinding of two general dependency records to
specialized helpers. Both full records are now restored, and the helpers are
owned by the new specialized definition node instead. No declaration in either
reviewed general module is edited. The finite tower owner now includes its named unique-transition
theorem, and the derived helper signatures explicitly state their result types.

## New nodes


`def-a1-integral-finite-pullback-tower` owns the existing plain definitions
`WeilConjectures.integralOperationsPullbackTowerFunctor`,
`integralOperationsPullbackLevel`, `integralOperationsPullbackTransition`,
`integralOperationsRestrict`, and the named characterization theorem
`integralOperationsPullbackTransition_existsUnique`, all in
`Sheaf.Paper.IntegralOperationsWellDefined`.
It has existing:true and delivers no Lean module. It specifies the actual levels,
restriction along the limit projections, quotient transitions, and chain-map action.
Read lines 148-152, 183-188, 213-232 and 451-454 and their docstrings: the transition
is selected from an existence-and-uniqueness characterization on the adjunction
unit generators, so this records a canonical construction. The definition does
not invoke the module's well-definedness/descent theorem. Its sources are the
local Stacks pullback/adjunction lemmas 03D2/03D3 and coefficient reduction 06YT.

New searches run during repair: msearch.py leansearch and leanfinder with
"strict inverse tower of finite coefficient module pullback complexes with quotient
transitions" each returned eight general results, none the construction.
msearch.py grep with
`integralOperationsPullbackTowerFunctor|integralOperationsPullbackTransition|integralOperationsPullbackLevel|integralOperationsRestrict`
returned zero Mathlib hits. rg of the project and upstream trees found these
published definitions and their consumers. A complete DAG lean.declaration /
lean.declarations scan found them listed only under the well-definedness theorem,
with no definition owner. blueprint_refs.py searches for
`integralOperationsPullbackTowerFunctor` and `finite pullback tower` returned zero
blueprint matches. Hence an existing:true owner is needed, with no duplicate code.


`def-a1-integral-completed-tower-pullback-universes` owns the specialized O_E
strict derived reduction and strict derived tower pullback with independent scheme
and coefficient universes. It covers the same helpers already used in the reviewed
comparison, without rebinding the general Noetherian adic datum or the Rlim
completed-pullback node. The source is Stacks 099N(5), prior to Rlim, with ordinary
ringed pullback from 03D2/03D3 and universal resolving-class functors from
06YS/06YY/06XN. The item imports it as a definition dependency. The main declaration
is `CompletedTowerIndependent.derivedPull` and all 22 helpers are listed.

Clause correspondence for this definition node:

* The prime, finite field extension and independent site/field universe binders
  are `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]`
  `[FiniteDimensional (Padic l) E]`, with `X Y : Scheme.{t}`.
* `Modules`, `Towers`, `towerDerived` and `transpose` reuse the completed module
  category, functor category, standard localization and existing transposition.
  `reductionComplex` uses the existing quotient functors and transitions.
* `DerivedPair` retains a functor, universal localization counit, and computation
  isomorphisms for every `integralOperationsGoodComplex`. `reduction_exists`
  states the existence required to define the counit-characterized `reductionPair`.
* `ringPush` is the actual direct image on the original small sites. `component`
  is the limit projection followed by the finite coefficient map, and
  `component_naturality` asserts all transition equalities. `directRingMap` is
  the lift of that cone through the preserved limit; it is not arbitrary data.
* `push` is module direct image with this action. `push_isRightAdjoint`, `pull`
  and `adjunction` supply the ordinary canonical ringed pullback and unit.
  `pull_additive`, `towerPull` and `towerPull_additive` give the additive
  object-and-arrow functor on strict towers, without asserting exactness.
* `towerPull_exists` specifies the universal left-derived functor and counit,
  a triangulated integer-shift structure, and invertible computation on every
  tower complex with K-flat evaluations. The explicitly typed `derivedPull`
  and `derivedCounit` select these universally characterized data.
* No helper assumes scheme-level invertibility of ell or invertibility of c_g,
  and no helper takes boundedness, constructibility, or an equality of universes.
  There is no Rlim in the specialized node's construction.

Searches for this node: msearch.py leansearch and leanfinder each returned eight
general pullback/completion hits, no strict derived tower at independent coefficient
size. The exact hit names and queries are recorded in its mathlib_searches.
msearch.py grep and rg of both project source trees returned no declarations of
`CompletedTowerIndependent`, `reductionPair` or `towerPull_exists`; a DAG-name grep
also returned no specialized owner. blueprint_refs.py returned zero matches for
`strict tower pullback`. The broad general nodes remain cited and unchanged.

Self-check of the new definition node: opened its statement and helper signatures
and matched the clauses above, including the universal counits and the actual
projection-induced structural map. The chosen data are determined up to exactly
the counit-compatible isomorphisms used downstream. Source and coefficient sizes
are independent, small-site arrows stay in t, and the positive exponent is n+1.
This is a specialization owner authorized by the return, not a replacement of the
reviewed general definitions. The new node has the required empty proof fields,
three search kinds, source, ancestor/via, and its own module.

The helper module's `Modules` alias uses the same explicit completed RingCat sheaf
presentation as the published `PrincipalKoszulStrictReplacement.Modules`, with
coefficient size max u (t+1). This is definitionally equal to `integralTowerModules`.
The profiler showed repeated unfolding of limits when reconciling those two
presentations in normalization types; the aligned alias avoids that repeated work.
No category equivalence, additional hypothesis or changed mathematical object is
introduced. Temporary profiler directives are removed from the final source.

The reduction cochain functor now has its explicit source and target categories;
the reduction shift-descent field also spells out those same category parameters.
This directs instance synthesis to the existing standard tower localization after
the definitionally equal module-presentation alignment. It adds no typeclass
hypothesis and does not alter the normalization or descent equality.


The existing tensor-generator, tensor-reduction, G, pulled-reduction, H,
augmentation and diagram-pull wrappers, together with the helper transposition,
now have explicit result types and use `def` rather than eagerly reducing
abbreviations. Their right-hand sides remain the same published constructions;
the tensor-generator body applies the same published generator to its explicit
arguments. These annotations avoid repeated expansion of the limit/tensor
implementations while checking the large dependent Comparison record. All
comparison fields and normalization equations are retained.

## Validation

Final scompile.py run compiled both delivered files separately, in dependency
order, under sandbox and library module names. Exit code 0, with no errors or
warnings. The helper library module took 7.3 seconds and the comparison library
module 39.2 seconds. All invocations retained nice 19, two threads and the standard
60-second limit. No profiler settings remain. The tensor-generator signature
explicitly supplies the independent universes u, t+1 and t, rather than imposing
an equality between them.

The general dependency copies were compared byte-for-byte with live again and
are unchanged, including their original notes and supporting metadata. All Lean
lines are at most 100 characters; JSON uses indent 1, Unicode and a final newline.
The existing tower owner's declaration list includes its unique-transition theorem.
No live source, launcher script or validation tool was edited, no direct Git
command was run, and no global build was run.
