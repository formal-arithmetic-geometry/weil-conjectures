## Worker report

The module `Sheaf.Paper.CompletedCoefficientPullbackLinearity` states all clauses of
`lem-sf-completed-coefficient-pullback-linearity`. It introduces no definition, no
alternative coefficient map, and no additional premise. The eight declarations are
constituent statements of this one node, each with `sorry` and its source and proof
plan in its docstring. The main declaration records module and derived linearity;
the scalar-square, exactness, preservation and restriction clauses are listed in
`lean.declarations`.

Hypotheses and objects, clause by clause:

- Scheme X is `(X : Scheme.{u})`. Its actual small pro-etale site is `X.ProEt`,
  with objects in universe u+1 and morphisms in universe u; these remain distinct.
- The commutative Noetherian adic datum is `{A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)`. The inherited fields are `ideal`, `noetherian`,
  `finitelyGenerated`, `quotientTorsion` and `quotientPerfect`; `quotientFinite`
  gives finiteness of every positive quotient. No completeness of the original A
  is assumed, and A is not identified with its completion.
- `pbcAdicCompletion X d` is definitionally `AdicCoefficients.completedRing`,
  the actual limit of the sheafified continuous-function quotient rings from
  `def-weil-pbc-adic-coefficient-datum`; `pbcAdicProjection` is its limit projection.
  Natural index n denotes exponent n+1, so every positive power is included.
- `(e : Aut X)` is the scheme automorphism, with the original canonical inverse
  image `proEtaleSheafInverseImage e.hom CommRingCat` and base change
  `proEtaleBaseChange e.hom`.
- The map s_X is `pbcCompletedScalar X d`, the recorded `adicDatumScalar` followed
  by its normalized completed-ring comparison. Its finite projections are the
  quotient A -> A/I^(n+1) followed by the fixed constant/function comparison.
- The maps rho_A and c_A are respectively `proEtaleConstantDirectImageMap` and
  `proEtaleConstantInverseImageMap`, with coefficient `CommRingCat.of A`. Their
  definitions use the constant-section sheafification map and its adjoint.
- The map c_e is `completedCoefficientMap e.hom d`: `limit.lift` with components
  inverse image of the actual projection followed by `completedFiniteCoefficientMap`.
  The latter is the canonical constant comparison conjugated by the published
  constant/function coefficient isomorphisms, exactly the profinite-coefficient
  comparison under those identifications. No arbitrary ring map is quantified.
- The adjunct c_e^# is `completedCoefficientDirectImageMap e.hom d`, defined as
  the inverse-image adjunction unit followed by direct image of c_e.
- `sfCompletedCoefficientScalarSquares` states `c_A ≫ s_X = e⁻¹(s_X) ≫ c_e`,
  `s_X ≫ c_e^# = rho_A ≫ e_*(s_X)`, and, for every `U : X.ProEtᵒᵖ` and `b : A`,
  `(c_e^#).hom.app U (pbcCompletedSection X d U b) =
  pbcCompletedSection X d ((proEtaleBaseChange e.hom).op.obj U) b`.
- Module Hom A-actions are the existing `pbcCompletedModulesLinear`, through
  `pbcCompletedScalarSections` and `pbcCompletedSection`; derived and full-subcategory
  actions are the inherited structures, not newly supplied linear instances.
- The specified module direct image is `completedModuleDirectImage e.hom d`, whose
  definition is sectionwise pushforward with ring action via c_e^#. The left adjoint
  is `completedModulePullback e.hom d`, inverse image followed by canonical sheafified
  extension along c_e. These are the actual tensor/direct-image constructions.
- Four exactness theorems give `PreservesFiniteLimits` and `PreservesFiniteColimits`
  for both module functors. They are conclusions under precisely X,d,e, not extra
  hypotheses. They let the exact termwise derived functors be elaborated canonically.
- `sfCompletedCoefficientPullbackLinearity` asserts `.Additive` and `.Linear A`
  for both module functors and both `.mapDerivedCategory` functors, on all Hom groups.
  It also asserts these properties for `completedOrdinaryPullback e.hom d`, the
  separately recorded ordinary K-flat left-derived pullback, rather than silently
  equating it with exact termwise descent.
- Every finite generating tuple is bound as `(r : ℕ) (a : Fin r → A)
  (ha : Ideal.span (Set.range a) = d.ideal)`. No nonempty or positive-length
  restriction is made. `WfIsComplete X d r a ha` is the existing predicate
  `IsDerivedCompleteIntrinsic` for the published actual Koszul completion unit,
  using the localization preimage of the same object as its representative.
  `sfCompletedCoefficientPullback_preservesComplete` states preservation for
  every object `K : PbcCompletedDerived X d` and every such tuple.
- `sfCompletedCoefficientCompletePullback_linearity` supplies the restriction H
  to the entire `WfCompleteCategory X d r a ha`, with strict inclusion equation
  `H ⋙ ι = ι ⋙ completedOrdinaryPullback e.hom d`. Thus H is fixed on objects and
  maps as the restriction of this very ordinary derived functor. This equation
  excludes an arbitrary endofunctor or a mere choice of equivalence. The remaining
  conjuncts are `H.Additive`, `H.Linear A`, and, for every pair M,N, parallel f,g,
  and b, `H.map (b • f) = b • H.map f` and
  `H.map (f + g) = H.map f + H.map g`. Existentially stating the restriction avoids
  duplicating the library's already defined restrictions of exact transport.

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficients.ringSystem`,
  `AdicCoefficients.completedRing`, `completedReductionCoefficient` and its
  projections; the datum structure is reexported from `CompletedAdicCoefficientDatum`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction`,
  `proEtaleConstantDirectImageMap`, `proEtaleConstantInverseImageMap`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage_equivalence` and the reexported canonical
  `proEtaleIso_constantComparison` and `proEtaleIso_inverseLimitComparison`.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`; no lean record
  is needed for this Mathlib dependency.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`; its general tensor
  adjunction is specialized by the published pro-etale module constructions.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`; `Sheaf.Paper.IntrinsicCompletion`
  transports this exact unit to the coefficient presentation used here, via
  `intrinsicCompletionUnit` and `IsDerivedCompleteIntrinsic`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtale_profinite_coefficient_inverse_image`, including its finite constant
  comparisons, projection identity and invertible limit comparison.
- `Sheaf.Paper.RingedTopoiDerivedPullback`:
  `SheafOfModules.ringedTopoiDerivedPullback`, the ordinary K-flat derived functor
  and its normalized counit. `completedOrdinaryPullback` uses the published
  resolving-class realization of that ordinary derived construction.
- Additional definition dependencies: `def-weil-pbc-rational-category`
  (`Sheaf.Paper.PbcRationalCategory`, scalar sections and canonical linear actions),
  and `def-weil-pbc-completed-pullback` (the ordinary constructions in
  `Sheaf.Paper.CompletedTowerPullback`). The latter's recorded wrapper is not
  imported solely for citation; the actual construction module is imported.
- `def-sf-complete-derived-subcategory` now owns the existing concrete
  `WfIsComplete` and `WfCompleteCategory` declarations in
  `Sheaf.Paper.WeilCompletedTensorReflector`. This is ownership of definitions,
  not a use of the reflector theorem.
- `def-sf-completed-module-direct-image` now owns the existing concrete
  `completedCoefficientDirectImageMap` and `completedModuleDirectImage` declarations
  in `Sheaf.Paper.CompletedTowerDirectImage`. The definitions use the adjunction
  unit and sectionwise pushforward; neither is chosen from a theorem.
- Proof imports: `CategoryTheory.ringed_presentation_transport`,
  `DerivedCategory.instLinear`,
  `CategoryTheory.Functor.instLinearDerivedCategoryMapDerivedCategory`, and
  `SheafOfModules.ringedDerivedPullback_linear`. The proof dependency
  `lem-sf-automorphism-completion-unit-comparison` has no recorded declaration,
  so there is no module to import for it. Its mathematical comparison is stated
  in the proof plan, and no missing notion or helper is assumed in the signatures.

Edge cases checked before drafting: e = identity uses the same canonical coefficient
maps without requiring literal identity of chosen limits. The empty scheme and zero
ring are admitted. I = A gives zero quotient rings and zero completed coefficients;
no nonzero scalar or faithful action is assumed. I = 0 admits r = 0 and the empty
generating tuple; the tensor unit and completion unit remain the published ones.
Arbitrary redundant generating lists are admitted. b = 0 and b = 1 obey the ordinary
Hom-module action. Objects and morphisms are unbounded and need not be constructible.
The distinction between the original A, the constant A sheaf and its completed sheaf
is retained even when A is not I-adically complete.

Searches before writing:

- `msearch.py ... leanfinder "The pullback by an automorphism with completed adic
  coefficient sheaves preserves scalar maps and is linear on intrinsically complete
  derived objects"`: eight hits concerning `AdicCompletion.map`, congruences and
  finite module completion; no completed ring-sheaf scalar squares or functor statement.
- `msearch.py ... loogle "Functor.Linear, SheafOfModules"`: no hits (unknown
  `Functor.Linear` in that search index).
- A follow-up `msearch.py ... loogle '"SheafOfModules", "Linear"'` returned one
  unrelated size instance for sectionwise module limits, not a linearity theorem.
- `msearch.py ... grep 'pullback.*[Ll]inear|[Ll]inear.*pullback' CategoryTheory`:
  no Mathlib hits. Mathlib `Linear.Basic` and `DerivedCategory.ExactFunctor` were
  read directly for the structures and exact derived functor instance.
- `rg` of `lean/WeilConjectures` for the item id, `pbcCompletedScalar`,
  `wfCoefficientScalar`, and `wfCompletePullback_linear`: no matching upstream
  declaration. `rg` of `lean/Sheaf` finds `WeilTensorProduct.wfCompletePullback_linear`
  (in namespace `AlgebraicGeometry.Scheme`), which proves only linearity of the
  complete exact-transport restriction. Its scalar-square lemmas are private,
  and it does not expose the node's combined squares, module and derived clauses.
  Importing this downstream parent to state its own proof dependency would create
  an import cycle once the parent imports this item. Its underlying coefficient
  and completeness definitions were traced to their separate owning modules and
  reused. Other hits concern p-adic-field specializations and arbitrary completed
  scalar extensions, not this full node.
- The repair searches and definition ownership are recorded under New nodes below.
  There is no dependency-interface replacement or new Lean definition.

There is no statement correction and no STATEMENT-DISPUTED issue. Relative to the
current main node, the item changes only `lean` and adds four definition dependencies:
`def-weil-pbc-rational-category`, `def-weil-pbc-completed-pullback`, and the two new
ownership nodes listed below. The original eight statement dependencies, mathematical
statement and all proof steps remain unchanged.

## Repair of the independent return at af4f9f84d1df

H2: removed `lem-weil-pbc-ringed-koszul-completion-reflector` and
`prop-weil-pbc-direct-image-limits` from the added statement dependencies. They were
incorrectly cited only because their modules contain plain definitions. The two
new definition nodes record those exact existing definitions with `existing: true`;
there is no duplicate construction or extra theorem dependency.

H9: removed the unused citation-only imports `Sheaf.Paper.PbcQbarCompletedPullback`
and `Sheaf.Paper.CompletedDirectImageLimits`. Retained `CompletedTowerPullback`,
`CompletedTowerDirectImage` and `WeilCompletedTensorReflector`, whose actual definitions
occur in the signatures. No theorem signature or proof docstring changed.

H11: replaced the former checklist with the detailed reading immediately below,
made with the node, all eight signatures and the two new ownership records open.
The dispatcher requires this work to be done without starting other agents.

Initial saved-packet dry run: commit `bfacfe53b79` printed OK. This was a mechanical
pass and did not repair the independent return; the ownership and report changes
above were therefore made before the final compile and dry run.

## Second reading by Q06

I read the current item's full statement, the blueprint's second sentence defining
tensor Frobenius, the eight Lean declarations, and each new definition node against
its existing Lean bodies. The clause correspondence is as follows.

| Node hypothesis or clause | Lean rendering and reading result |
| --- | --- |
| A scheme X; its chosen small pro-etale site | Each signature binds `X : Scheme.{u}`. `X.ProEt` retains object universe `u+1` and morphism universe `u`. No Noetherian or finite-dimensional assumption on X occurs. |
| Commutative Noetherian adic datum with finite perfect positive quotients | `{A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)` supplies the actual datum fields, not hypotheses about an arbitrary completed ring. No assumption that A itself is complete is added. |
| Completed sheaf and constant scalar map with quotient projections | The signatures use `pbcCompletedScalar X d`; its body uses the existing normalized constant/completed comparison. `pbcAdicCompletion` is the actual inverse limit, indexed by exponent `n+1`, covering exactly the positive powers. A and its completion remain distinct. |
| Automorphism e of X | `(e : Aut X)` occurs in every signature. Both source and target scheme are X; `e.hom` is used in every coefficient and module map. The identity automorphism is included. |
| Constant rho_A, its adjoint c_A, and canonical completed c_e | In the first theorem these are `proEtaleConstantDirectImageMap`, `proEtaleConstantInverseImageMap`, and `completedCoefficientMap`. The last is `limit.lift` of the actual inverse-image projections and finite comparisons. There is no arbitrary comparison map binder. |
| Completed adjunct c_e^# | `completedCoefficientDirectImageMap` is literally the adjunction unit followed by the image of `completedCoefficientMap`. The new definition node states exactly this formula and records this existing declaration. |
| First scalar square | The first conjunct of `sfCompletedCoefficientScalarSquares` is `c_A ≫ pbcCompletedScalar = inverseImage.map pbcCompletedScalar ≫ completedCoefficientMap`, with the node's orientation and endpoints. |
| Second scalar square | Its second conjunct is `pbcCompletedScalar ≫ completedCoefficientDirectImageMap = proEtaleConstantDirectImageMap ≫ directImage.map pbcCompletedScalar`. No inverse or extra isomorphism is inserted. |
| Scalar section equation for every U and b | Its third conjunct quantifies `U : X.ProEtᵒᵖ` and `b : A`; evaluation of the adjunct at `pbcCompletedSection X d U b` equals the same scalar at `((proEtaleBaseChange e.hom).op.obj U)`. This is exactly evaluation at u_e(U), including all sections of this scalar form. |
| A-actions on all module Hom groups | `pbcCompletedModulesLinear`, supplied by `PbcRationalCategory`, uses the section maps just read. The statements do not quantify a replacement A-linear structure. Derived and full-subcategory actions are inherited. |
| Specified module direct image and its left adjoint | `completedModuleDirectImage` is sectionwise pushforward with action restricted along c_e^#. `completedModulePullback` is inverse image followed by extension along the same c_e. The direct-image ownership node reproduces the actual section and action formulas; no arbitrary left adjoint is substituted. |
| Exact module functors | The four `sfCompletedModule...preservesFinite...` declarations conclude finite-limit and finite-colimit preservation for both functors. They have only X,d,e as hypotheses. Their instance attributes permit the exact derived functors to be stated; exactness is never assumed. |
| Additivity and A-linearity on modules and their exact derived functors | The ten conjuncts of `sfCompletedCoefficientPullbackLinearity` give `.Additive` and `.Linear A` for module direct image, module pullback, their two `.mapDerivedCategory` functors, and `completedOrdinaryPullback`. `.Linear A` quantifies over every derived morphism, without a boundedness restriction. |
| Ordinary K-flat pullback Le^* | The last two conjuncts and the last two theorems use `completedOrdinaryPullback e.hom d`. Its published universal-left-derived pair belongs to the very module pullback already read. This avoids imposing the `Category.{u}` restriction of the generic ringed-topoi theorem and preserves the actual small-site universes. |
| Any finite generating tuple, including the empty tuple | Both final signatures bind `(r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)`. There is no `0 < r` or nonzero-generator assumption. |
| Full intrinsic complete subcategory and preservation | `WfIsComplete` unfolds to `IsDerivedCompleteIntrinsic` with `DerivedCategory.Q.objPreimage K` and `objObjPreimageIso K`; its unit is the existing intrinsic Koszul unit. `WfCompleteCategory` is precisely its full subcategory. `sfCompletedCoefficientPullback_preservesComplete` quantifies over every ambient K and concludes completeness of the actual ordinary pullback. The new ownership node states these same constructions, with no reflector property added. |
| Restriction H_comp of that pullback | The existential H has domain and codomain the full complete category. The strict equation `H ⋙ ι = ι ⋙ completedOrdinaryPullback` fixes its underlying objects and maps. This is the restriction required by the node, not an unrelated endofunctor with the same properties. |
| Restriction additivity, A-linearity and both map equations | The final theorem concludes `H.Additive ∧ H.Linear A`, followed by universal quantification over complete M,N, parallel f,g and b. Its two equations are exactly `H.map (b • f) = b • H.map f` and `H.map (f + g) = H.map f + H.map g`. No object or morphism is omitted. |

The two new node records were also read clause by clause. In
`def-sf-complete-derived-subcategory`, the datum and tuple binders come from the
module's explicit variable block; its representative, localization isomorphism,
invertible-unit predicate and full-subcategory construction are exactly the bodies
of `wfCompletionRepresentative`, `WfIsComplete` and `WfCompleteCategory`. In
`def-sf-completed-module-direct-image`, the explicit X,Y,f,A,d variables are the
module's variable block; the unit-composite adjunct and the restricted sectionwise
module action are exactly the two recorded definitions. Neither record asserts any
reflector, derived direct-image or limit-preservation theorem.

The reading found the three process defects described in the repair section and
fixed them. It found no mathematical signature mismatch. In particular, e=id,
empty X, zero A, I=A, I=0 with r=0, redundant tuples, and b=0 or 1 remain admitted.
The strict inclusion square and the actual ordinary left-derived functor are retained.

## New nodes

`def-sf-complete-derived-subcategory` owns the existing `WfIsComplete` and
`WfCompleteCategory` in `Sheaf.Paper.WeilCompletedTensorReflector`, with
`wfCompletionRepresentative` also listed. Its source is the intrinsic-completeness
clause of this item's blueprint coefficient transport, built on
`def-weil-pbc-intrinsic-completion`. The new node does not restate the reflector
lemma: it names only its concrete predicate and full subcategory. DAG grep found
these names only under theorem nodes; no definition node owned this packaging.
`blueprint_refs.py search 'complete full subcategory'` returned 0 matches.

`def-sf-completed-module-direct-image` owns the existing
`completedCoefficientDirectImageMap` and `completedModuleDirectImage` in
`Sheaf.Paper.CompletedTowerDirectImage`. Its source is the adjunct/module-direct-image
clause of the same coefficient transport. It builds on the adic datum, pro-etale
adjunction and completed coefficient map, states the unit-composite adjunct and
restricted sectionwise action, and asserts no direct-image theorem. No DAG definition
node recorded these declarations; `blueprint_refs.py search 'completed module direct
image'` returned 0 matches. Both nodes use `existing: true` and add no Lean module.

For both ownership nodes, the prescribed searches were run again on 2026-10-21:
LeanSearch query "The full subcategory of derived complete module sheaves and the
sectionwise direct image of modules over an adic completed coefficient sheaf" gave
8 hits, including general `SheafOfModules.pushforwardSections`, limits and abelianness,
with no exact completed-coefficient definition. LeanFinder query "Canonical adjunct
ring map for completed coefficient sheaves, module direct image with restricted scalar
action, and full subcategory of intrinsically derived complete objects" gave 8 hits
concerning tilde, condensed free modules and adjunctions, with no exact match.
`msearch.py ... grep 'WfIsComplete|WfCompleteCategory|completedCoefficientDirectImageMap|completedModuleDirectImage'`
gave 0 Mathlib hits. Direct `rg` of `lean/WeilConjectures` found no names; `lean/Sheaf`
contains the exact definitions above, so they are reused. The raw query strings,
returned names and dates are recorded in each new node's `mathlib_searches` and
in the prescribed search log.

Final repair validation: the prescribed `scompile.py` compiled the changed module
in sandbox mode (6.7 seconds) and library mode (6.9 seconds), with no errors or
warnings. The repaired packet's server preflight, existing-declaration checks and
per-file compilation all passed: dry-run commit `7931a697d9a` printed OK. The
packet has one Lean module, two existing-definition ownership records, the item
record and this report; no live library source was edited.
