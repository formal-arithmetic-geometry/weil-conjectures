## Worker report

Item: `lem-trf-point-system-insertion-composition`, Q22, stage 2.
Module: `Sheaf.Paper.PointSystemInsertionComposition`.
Main declaration: `WeilConjectures.PointSystemInsertion.pointSystemInsertionComposition`.

The delivery states the simultaneous coefficient, module, strict-system, tower,
complex and ordinary-derived composition assertion. Every theorem has proof `sorry`;
every definition has actual data. The natural transformations in `Maps` are witnesses
of the main theorem, each fixed by its sectionwise or localization normalization.
They are not unnormalized comparison hypotheses. The several `*Laws` predicates
merely package the clauses of this one statement.

The node's natural-language statement, proof and proof dependencies are unchanged.
Its statement dependencies gain five already-landed owning nodes:
`def-coef-ringed-sequence-site`, `def-trf-point-restriction-coordinates`,
`lem-pur-proetale-module-pullback-composition`, `def-pur-integral-finite-pullback`,
and `def-sf-scalar-reduction-categories-restriction`. Their recorded declarations
supply the existing system category, coefficient/section operations,
independent-universe ordinary compositor, finite pullback/unit generator,
and completed scalar-reduction module category used here. No new notion node or dependency
replacement is needed. The general positive-power system action is a helper of the
item: it reindexes this existing sequence site and uses the uniquely prescribed
inverse coefficient maps, rather than introducing a second system category.

Hypotheses and notation, one by one:

| Node | Lean rendering |
| --- | --- |
| Algebraically closed field k | `k : Type t`, `[Field k]`, `[IsAlgClosed k]` |
| Arbitrary automorphism of s=Spec k | `h : Aut (Spec (.of k))`; no finite-field or Frobenius hypothesis |
| Prime l invertible in k | `l : ℕ`, `[Fact l.Prime]`, `_hl : IsUnit (l : k)` |
| Finite extension E/Q_l | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| R and chosen uniformizer | Dependency constructions `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer` |
| A_n, n>=1 | `Padic.coefficientExtensionRing l E (n + 1)`; every positive exponent occurs |
| Small pro-etale site | Recorded `Scheme.ProEt` and `ProEt.topology`; object universe t+1 and morphism universe t are retained |
| B_n and completed Rhat | `pointRestrictionRing ... (some n)` and `pointRestrictionRing ... none`, respectively the recorded `integralCoefficientSheaf` and `completedIntegralCoefficientSheafUnrestricted` |
| Actual completion projections | `limit.π (integralCoefficientSheafSystem ...) (op n)` |
| All strict quotient-linear systems | Existing `coefficientSequenceModules l E (Spec (.of k))` on the ringed sequence site; horizontal restrictions are the original semilinear transitions |
| U | Existing `coefficientSequenceRestriction`, with all original maps |
| F_r | `F ... r a`, an alias of recorded `pointRestrictionInverseImage` along `(h ^ (r + 1)).hom`; `a=none` is completed coefficients |
| Canonical coefficient maps | `c ... r a`, directly the recorded `pointRestrictionCoefficientMap`; no arbitrary ring map parameter |
| G_r | `G ... r`, continuous pushforward along `reindex ... r` with inverse finite coefficient comparisons at every (n,U) |
| F_r on towers | `FTow ... r`, actual `Functor.whiskeringRight` |
| Complex and derived actions | `mapHomologicalComplex (.up ℤ)` and `mapDerivedCategory`; `G_exact` and `sections_exact` supply exactness of the actual composite functors |
| Ordinary unbounded derived categories | Recorded `coefficientSequenceDerived`, and the standard localization of `ℕᵒᵖ ⥤ ModuleCat ... R` supplied by `towerDerived` |
| Gamma retaining transitions | `sections`, exactly `coefficientSequenceRestriction` followed by levelwise final-object `pointRestrictionSections` and its recorded constant R-scalar action |

Here a Lean power index r denotes the paper's r+1, and m denotes m+1. Thus
`r=0`, `m=0` are the required first-power cases, not zeroth powers.
The common-universe lift `pointRestrictionScalars.{t,u} ... none` is the recorded
presentation of R-modules. There is no equality imposed between t and u.

Conclusions, clause by clause:

1. `Maps.d` contains natural linear module isomorphisms at every finite coefficient
   and at the completion; `Maps.t` contains natural isomorphisms of entire strict
   systems. `SectionLaws` conjuncts 1 and 2 require identity on every section in
   site-reindexing coordinates, not merely existence of some compositors. The
   heterogeneous equalities transport only between equal direct and successively
   reindexed section carriers. This is the normalized canonical site compositor.
2. `ringCompositor` is the actual sheaf pushforward compositor induced by the
   dependency's `pointSheafReindexCompositor`. `CoefficientLaws` conjunct 1 is
   `d_D ≫ c_(m+1,D) = F_1(c_m,D) ≫ c_1,D` for `some n` and `none`.
   Conjunct 2 is the displayed completed projection/coefficient equation for every
   power and every quotient. These use the actual limit and its actual projections.
3. `Maps.b` is a natural isomorphism of whole completed-module towers, so its
   components commute with all original transitions. `SectionLaws` conjunct 3
   prescribes identity on every section. `RestrictionCompositionLaws` is the
   displayed b/d/t equation, in Lean's left-to-right composition order.
   `towerCompositor` applies d levelwise, with the actual functor associator.
4. `Maps.j` is an invertible finite comparison. `TensorLaws` conjunct 1 prescribes
   precisely the recorded adjunction generator followed by restriction along the
   canonical comma arrow: the sheafified x tensor 1 map of comparison part (a).
   Conjunct 2 conjugates d through these j maps to `tensorCompositor`. That definition
   is exactly the inverse of `coefficientModulePullbackComposition`, followed only
   by the actual equality of powers. The latter is the existing specified adjunction
   compositor, whose exact localization is the module-composition comparison of
   the recorded derived theorem. In particular the two successive unit insertions
   are sent to the direct unit insertion, with d acting as identity in coordinates.
5. `Maps.u` is a natural transformation with values in the category of whole
   R-module towers: its maps are R-linear and preserve every original transition.
   `StrictInsertionLaws` conjunct 1 specifies restriction along h^(r+1), using the
   underlying abelian presheaf restriction on the actual ringed sequence site.
   In the normalized inverse-image coordinates the graph coprojection and its
   sheafification are the identity, as in the recorded inverse-image dependency.
   The finite presentation then applies the j fixed in clause 4; no unrelated
   finite insertion is selected.
6. `complexInsertion` is termwise `NatTrans.mapHomologicalComplex` of u, with the
   canonical target factorization. Thus it is a natural R-linear chain map of
   entire towers. `StrictInsertionLaws` conjuncts 2 and 3 give the displayed
   successive/direct insertion equations on modules and on all unbounded complexes.
   Being a complex morphism asserts compatibility with every differential.
7. `finiteUnit` uses j with the canonical section-group equality from
   `inverseImageEvaluationSection_eq`. `tensorTransition` is the concrete conjugate
   of the ORIGINAL underlying horizontal restriction by these unit isomorphisms.
   No assumption that v_n is B_n-linear is introduced. `TransitionLaws` conjunct 1
   gives the balanced rule reducing a through the actual `integralCoefficientSheafTransition`;
   its a=1 case is v_n(x) tensor rho_n(1). Conjunct 2 explicitly says both paths
   equal `finiteUnit ... (v_n(x))`, i.e. v_n(x) tensor 1.
8. `Maps.I` is a natural transformation on the ENTIRE ordinary derived system
   category with target D(Tow(Mod R)). `DerivedInsertionLaws` conjunct 1 fixes its
   localization on every representative via the exact functor factorization
   isomorphisms and the actual whole-tower chain map. Conjunct 2 gives the required
   derived composition equation using `mapDerivedCategoryCompNatIso` of t.
   Naturality for every derived morphism is part of the type of I; it does not rely
   on derived evaluations being faithful.
9. No cartesianness, normalization, boundedness, constructibility or Tor-amplitude
   condition appears on the system modules, complexes, or derived objects anywhere.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the reexported actual coefficient ring,
  integer-ring, ideal and uniformizer constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, the completed coefficient sheaf,
  `integralCoefficientSheafSystem`, and its projections.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearSections.semilinearDerivedSections` and its componentwise system calculus.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus` and its reexport of the actual
  ringed sequence system model; no private replacement of its U is made.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`, reexporting the specified general
  K-flat-normalized derived pullback comparison.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseInverseImage_equivalence`,
  `isoSectionwiseConstantMap`, `isoSectionwiseModuleInverseImage` and its exactness.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its publicly imported
  `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageFiniteCoefficientMap`, `inverseImageCompletedCoefficientMap`,
  `inverseImageFiniteModules`, `inverseImageIntegralModules`,
  `inverseImageFiniteComparisonComplex`, `inverseImagePullbackComparisonDerived`.
- `Sheaf.Paper.CoefTowerCoaugmentation`: `CoefTower.adjunction` and the ordinary
  whole-tower coefficient convention. The assertion here never takes a limit of
  its section tower or replaces its target by a tower of derived categories.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `point_proEtale_sections_exact`.
  Our `sections_exact` states exactness of the actual composite whole-system
  section functor, including independent coefficient size, not a new section functor.
- `Sheaf.SixFunctors.FrobeniusPointTransport`:
  `frobeniusPointTransportQbar` and, for this item, the finite restriction/unit recipe
  it reexports. The finite-field specialization is not used to restrict k or h.
- `Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus`:
  `pointSheafInsertionCalculus` and `pointSheafReindexCompositor`.
- The first three added landed dependencies provide
  `coefficientSequenceModules`, `coefficientSequenceEvaluation`,
  `coefficientSequenceRestriction`, `coefficientSequenceEvaluationAb_eq`,
  `pointRestrictionRing`, `pointRestrictionScalars`, `pointRestrictionCoefficientMap`,
  `pointRestrictionSections`, `pointRestrictionArrow`,
  `coefficientModulePullbackComposition_existsUnique`,
  and `coefficientModulePullbackComposition` in their recorded modules.
- Proof-only imports are precisely the recorded object-restriction, site-generator,
  constant-coefficient-composition, scalar-extension-isomorphism, tensor-composition,
  inverse-limit, scalar-restriction, cochain-tensor and localization modules.
  Their generic proof tools are retained although stage 2 postpones the proof.

Sources opened: local Stacks `sites.tex`, lemma-composition-morphisms-sites (03CB),
its explanation by uniqueness of left adjoints, and the recorded constant-sheaf
normalizations in the dependency source; blueprint main-20261015,
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`,
Global powers. The declaration docstring contains all seven node proof steps,
including the coefficient limit projection argument, the original semilinear
transition calculation and localization of a whole-system equality.

Edge cases checked before finalizing: h=id; a nontrivial arbitrary automorphism;
first power and first quotient (Lean indices 0); zero modules and zero complexes;
zero or noncartesian original transitions; complexes unbounded in both directions;
all characteristics in which l is invertible; independent field and coefficient
universes. No nonempty/faithful/flat/bounded input condition was inserted.

Searches before writing (all use the prescribed wrapper or read-only source search):

- `msearch.py ... leanfinder`, query “Composition of point insertion along powers of
  a scheme automorphism on strict coefficient module systems”: eight results,
  including affine-space reindexing and adic-completion factor-power identities;
  none state this simultaneous strict-system coefficient/insertion composition.
- `msearch.py ... loogle`, query `SheafOfModules.pullbackComp`: five hits, ordinary
  module pullback composition/identity/associativity and conjugation identities;
  these are generic ingredients, not the point/system/localization assertion.
- `msearch.py ... grep`, regex `point.*insertion|insertion.*compos` in CategoryTheory:
  zero Mathlib hits.
- `rg` in project `lean/WeilConjectures` and `lean/Sheaf`, and `grep -rn` for this
  item's exact id in `lean/WeilConjectures`: no existing exact declaration.
  Related finite `PointSheafInsertionCalculus`, Frobenius-only
  `PointSystemTransportDescent`, and its power/Roos theorem do not state this
  arbitrary-field, arbitrary-automorphism coefficient/system assertion. Their
  underlying recorded constructions were read and reused where applicable.
- The independent-universe ordinary compositor was found in
  `ProEtaleCoefficientModulePullbackComposition`, read in full with its node, and
  used directly instead of introducing a new module-pullback compositor.

No statement correction, no disputed statement, and no dependency node repair.
All compilation uses `scompile.py`; the server's 60-second limit is unchanged.

## Second reading by Q22

This is a second in-session pass; the dispatcher explicitly prohibits starting
another agent. The delivery receives its independent mathematical review from
the maintainer. I reopened the node and module and checked every row and numbered
clause above against the final declaration and its predicates.

The initial presentation made Lean unfold scalar-restricted MODULE maps when
checking original semilinear transitions. I changed these occurrences to the
underlying abelian presheaf maps, and made the canonical equalities of evaluated
section groups explicit. This preserves the original transition without treating
it as a map over a wrong finite coefficient ring. The tower compositor now includes
the actual associator. The simultaneous laws were separated into named Prop
predicates to avoid generating large structure eliminators. These are presentation
changes only; the node statement was not changed.

I checked the directions of all compositors: d and t go successive to direct;
tensorCompositor is the inverse of the dependency's direct-to-successive map;
the b square starts with U then the two completed inverse images; I lands in the
ordinary derived category of WHOLE module towers. The strict and derived formulas
use the very same t, and the localization equation fixes I on every representative.

Validation: prescribed server `scompile.py` passed both its sandbox and final-module
compiles, respectively 9.0 and 10.0 seconds, with no error or non-sorry warning.

## Returned delivery repair

Return: L, immutable head `ec031c41b70a`, H2. The saved packet first passed the
prescribed `deliver2.py --no-push` check (commit `05162773a57`), including compilation.
I retained the reviewed Lean file and repaired the node ownership record.

1. Replaced `lem-weil-point-automorphism-restriction-natural` in `stmt_deps` with
   the existing definition owner `def-trf-point-restriction-coordinates`.
   Its `existing: true` record owns the actual `pointRestrictionRing`,
   `pointRestrictionScalars`, `pointRestrictionCoefficientMap`,
   `pointRestrictionInverseImage`, `pointRestrictionSections`, and
   `pointRestrictionArrow` definitions in
   `Sheaf.Paper.PointAutomorphismRestrictionNatural`. I reopened their complete
   signatures and docstrings and checked their uses in `F`, `FTow`, `c`,
   `sections`, `SectionLaws`, and `StrictInsertionLaws`. No use of the theorem
   `point_automorphism_restriction_natural` occurs. The import stays the same
   because the definition owner records that very module.
2. Addressed the advisory citations too: added
   `def-pur-integral-finite-pullback`, whose recorded
   `WeilConjectures.integralOperationsLevelPullback` and
   `WeilConjectures.integralOperationsPullbackGenerator` in
   `Sheaf.Paper.IntegralOperationsWellDefined` are used in `tensorPull` and
   `TensorLaws`; added `def-sf-scalar-reduction-categories-restriction`, whose
   recorded `WeilConjectures.scalarReductionSource` in
   `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` supplies the
   completed-module tower category. I read both ownership records and the
   definitions and docstrings at their recorded source locations.
3. Retained `lem-pur-proetale-module-pullback-composition`, accepted in the return:
   the chosen compositor is pinned by its own existence-and-uniqueness theorem.
   Retained the accepted `def-coef-ringed-sequence-site` citation.

The item differs from current main only in `lean` and `stmt_deps`; the repair
changes only `stmt_deps` and this report relative to the saved returned packet.
There is no statement, proof, proof-dependency, signature, universe, or Lean-source
change. The original clause-by-clause and edge-case reading above remains valid.
No new node or dependency module was introduced.
