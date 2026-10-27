## Worker report

The module `Sheaf.Paper.PurTateUnitFlatModelDomains` states
`WeilConjectures.PurityFiniteSetting.tateUnitFlatModelDomains`. Its only new theorem has
proof `sorry`. Eleven data definitions/abbreviations only enumerate or compose the existing
unit, Tate line, exact sheaf tensor, single-complex, reduction and shift constructions.
No definition contains `sorry`. The repair adds one existing-declaration definition ownership node; no dependency module is needed.

Sources read: the item's complete DAG statement and five proof steps; all its statement
dependency records and the recorded source declarations; current blueprint
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/` files
`sk-thm-purity-transport.proof.md` (Steps 3–4), and
`sec-proetale-coefficients/sk-def-sp-tate-twist/def-coefficient-twists-detailed.md`;
`sec-six-functors-basics/sk-prop-sf-existence/prop-weil-twist-preserves.proof.md`.
The current blueprint uses condensed coefficients; the auxiliary DAG item explicitly
uses the already recorded completed-sheaf/tower presentation. The module states precisely
that presentation and its ordinary/completed comparison, without changing the item.

Hypothesis and clause correspondence:

- Global finite-field datum and prime ell different from p: `P : PurityFiniteSetting`;
  `P.field` and `P.coefficients` retain the recorded field and coefficient conventions,
  including primeness and `different`. The finite level and finite extension bundled in P
  impose no condition on the arbitrary extension E or any reduction index in this theorem.
- Finite extension L/Q_ell, its canonical valuation ring and uniformizer: E with `[Field E]`,
  `[Algebra (Padic P.coefficients.l) E]`, `[FiniteDimensional ... E]`. All coefficient
  sheaves use the recorded `Padic.coefficientExtensionRing` and completed limit constructions.
- Separated finite-type k-scheme S: `[S.Over (Spec (.of P.field.k))]`,
  `[LocallyOfFiniteType (S ↘ ...)]`, `[QuasiCompact (S ↘ ...)]`, `[IsSeparated (S ↘ ...)]`.
  `include hft hqc hsep` retains all three in the theorem. No nonemptiness hypothesis occurs.
- Small pro-etale site: the actual `Scheme.ProEt.topology S`. At common input size u,
  its objects remain in Type (u+1), its arrows in Type u, and modules in size u+1.
  No equality of the site's object and morphism universes is imposed.
- m >= 0 and integer n: `m : ℕ`, `n : ℤ`. The natural exponent is cast to ℤ only
  when invoking the recorded signed twist definitions. Every nonnegative m occurs.
- R_L, J_L and R_L tensor J_L: `tateFlatModelModule m i`, for i = 0,1,2. These
  unfold respectively to `SheafOfModules.unit` of the completed coefficient sheaf,
  `integralTwistLine ... (m : ℤ)`, and `integralSheafTwist ... .obj` of that unit.
  Their single complexes and every integer shift are `tateFlatModel m i s`.
- K-flatness and termwise flatness: the existential proof hP of the existing
  `integralOperationsGoodComplex ... (tateFlatModel ... s)`. This predicate is exactly
  `IsKFlatIndependentCoefficients` conjoined with `∀ r, IsFlatOnSite (P.X r)`.
  The existential is a conclusion, never an assumed flatness condition.
- The canonical multiplication between the third and second model is the unique mu
  whose hom sends every local pure tensor a tensor z to a • z. Invertibility also
  fixes its inverse z ↦ 1 tensor z. The same mu is used in all reduction arrows.
- Identity resolutions compute ordinary derived extension: `IsIso (completedScalarCounit
  ... (tateFlatModel ... s))`, for every finite H and specified algebra embedding iota.
  The counit's source is the actual `completedDerivedScalarExtension` of Q of that very
  model, and its target is Q of its termwise `completedOrdinaryScalarComplex` extension.
- The specified chi, strict quotient tower and identity inclusion: `IsIso` of the actual
  `completedScalarComparison` component. The following equality relates it to the strict
  `integralScalarExtensionComparisonOfUniverses`, universal scalar counit and the actual
  `completedScalarChainComparison`. The separate identity equation uses
  `AlgHom.id`, `completedScalarIdentityMultiplication`, and `completedScalarIdentityUnit`.
  No condition excludes iota = identity. Completeness of all these model objects is also
  asserted, as in Step 5 of the node's proof.
- The actual U,V,W: `tateFlatDomainObject m n i`, i = 0,1,2, is exactly
  `integralConstantCoefficientObject`, its image under `sfIntegralTwistingFunctor`, and
  that image shifted by n. V is not replaced by an arbitrary copy of the Tate line.
- Membership in D^b_ctf: `finiteTorConstructibleIntegral` of each actual object; this
  includes the recorded derived completeness, constructible reductions and uniform bounds.
- All positive reductions: j : ℕ denotes quotient exponent j+1, so precisely every
  j_source >= 1 occurs. `IsIso (tateFlatReductionMap ... mu i)` gives an actual
  canonical derived isomorphism, not only a cohomology comparison. Its codomain is
  `tateFlatReductionObject`, respectively A_j[0], A_j(m)[0], and A_j(m)[0][n].
- The reduction arrows have real data. For U the arrow is the published
  `constantCoefficientReductionMap`. For J it is the transpose through the published
  derived scalar/restriction adjunction of the uniquely normalized `TwistReductionMaps`
  witness. That witness is selected from a uniqueness theorem, not from mere existence.
  For V it is composed with the standard exact-functor single-complex comparison and
  single(mu). For W it is shifted by the same universal derived-change-of-rings witness.
  These definitions make the asserted isomorphisms specifically the source's canonical maps.
- Each quotient identity model computes reduction: the final conjunct is invertibility
  of `scalarReductionCounit` on every displayed model and every shift, at every level.
- Arbitrary degree-zero M: `∀ M : scalarReductionTarget ... j`, with no constructibility,
  flatness or finite generation restriction. The actual intrinsic derived tensor of the
  actual reduction with `(DerivedCategory.singleFunctor _ 0).obj M` is isomorphic to
  `tateFlatTestTensor`. This target is M[0], (M tensor A_j(m))[0], or its n-shift.
  The harmless shift-by-zero in the first two targets is the standard shift functor.
- The intervals [0,0], [0,0], [-n,-n]: `HasProEtaleTorAmplitude` on the actual reductions,
  with both endpoints `-tateFlatReductionShift n i`; the shift function is 0,0,n.
  The quantifier over j is inside the already fixed interval, so these bounds are uniform.
  This is containment of cohomological support, not a claim of exact nonzero support.

Residue invertibility required by the published twist API is constructed inside the data
definitions from `P.coefficientPrime_isUnit_stalk` and the residue ring map, exactly as the
existing purity consumers do. It is not an extra assumption. Coefficient and geometric
objects use a common input universe, as the recorded integral constructible and finite-Tor
interfaces do; arbitrary finite extensions and schemes can be placed in that common
universe. The pro-etale site retains its two different universe levels.

Dependency declarations used (module — names):

- `Sheaf.Paper.PurityFiniteSetting` — `PurityFiniteSetting`, `coefficientPrime_isUnit_stalk`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale` — `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` — coefficient extension ring and
  finite-dimensional coefficient-field conventions (publicly reexported constructions).
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` — reexported
  `completedIntegralCoefficientSheafUnrestricted`, `completedIntegralCommRingSheafUnrestricted`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` — `DerivedCategory`, Q, singleFunctor;
  the exact-functor single and ordinary shift comparisons are Mathlib's.
- `Sheaf.CategoryTheory.RingedSiteModules` — the recorded SheafOfModules presentation.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` — `integralTwistLine`,
  `integralSheafTwist`, `sfIntegralTwistingFunctor`, `finiteCoefficientTwist`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` — the K-flat predicate used by
  `integralOperationsGoodComplex`; no private K-flat predicate is introduced.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` — the retained ringed-site
  universal derived-change-of-rings construction, used by the scalar functors/counits.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison` — `completedDerivedScalarExtension`,
  `completedScalarCounit`, `completedScalarComparison`, `completedScalarChainComparison`,
  `completedScalarIdentityMultiplication`, `completedScalarIdentityUnit`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses` —
  `integralScalarExtensionComparisonOfUniverses`, and the published good representative class.
- `Sheaf.Paper.SfIntegralConstructible`, `Sheaf.Paper.FiniteTorAmplitudeSites` —
  `sfIntegralConstructible`, `finiteTorConstructibleIntegral`, `HasProEtaleTorAmplitude`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` — `scalarReductionSource`,
  `scalarReductionTarget`, `scalarReductionDerivedExtension`, `scalarReductionCounit`,
  `scalarReductionDerivedExistence`, `derivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.TwistPreservesFiniteness` — the uniquely normalized `TwistReductionMaps`
  component of `twist_preserves_finiteness`.
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible` —
  `finiteConstantCoefficientObject`, `integralConstantCoefficientObject`,
  `constantCoefficientProjection`, `constantCoefficientReductionMap`.
- `Sheaf.Paper.DerivedPullbackTensorHom` — `finiteIntrinsicDerivedTensor`, the existing
  intrinsic presentation of the ordinary K-flat derived tensor on quotient module sheaves.
- Proof imports retain `LocallyFreeDerivedScalars`, `BoundedAboveFlatSheafKFlat`,
  the recorded upstream finite-coefficient `Derived.Tensor`, and `IntegralCtfTriangulated`.

The additional stmt_deps are `prop-weil-twist-preserves` (the uniquely normalized
quotient line map), the new `def-weil-constant-coefficient-objects` (the unit object and
normalized unit reduction), and `def-weil-derived-pullback-tensor-hom` (the intrinsic
quotient tensor interface). The constant-coefficient constructibility theorem remains
in proof_deps and is not used to own plain definitions.
This adds dependency edges only; the informal statement and proof are unchanged.

Edge cases checked before writing and on rereading: m=0, n=0, positive and negative n,
j=0 (source exponent 1), arbitrary large j, H=E with iota identity, empty S, and M=0.
For empty S or zero M all cohomology vanishes; the specified intervals still contain it.
The quantifiers over i run over all three displayed models or all three displayed objects,
not an extra family. No finite level is dropped and no strict-inclusion assumption appears.
There is no disputed statement or corrected node.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Completed integral Tate unit and positive Tate lines have
  shifted K-flat models, finite derived reductions, and uniform Tor bounds"`: eight
  results, including BDeRhamPlus, BDeRham, adic-completion flatness and perfectoid
  completion lemmas; none is this sheaf-theoretic statement.
- `msearch.py ... loogle '"KFlat", "HasProEtaleTorAmplitude"'`: zero hits.
- `msearch.py ... grep 'Tate.*[Tt]or|[Tt]ate.*[Kk][Ff]lat'`: 25 unrelated results;
  no completed Tate-unit model/domain theorem.
- `msearch.py ... leansearch "Tate coefficient unit has K-flat line models and uniform
  Tor amplitude for all reductions"`: eight module-flatness criteria; none is this result.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the exact item id, `tateUnitFlatModelDomains`, and the new tateFlat helper prefixes:
  no existing declaration. Broader Tate/flat-model searches located the existing
  `PurShiftedTateUnitScalarCoherence` consumer and scalar/line interfaces, which were read.
  The consumer covers the special shift 2d and coherence equations, not this full node.
  It is deliberately not imported: the DAG has this item as its proof prerequisite.
- The recorded `CompactObject.lean` example is now a withdrawn module, with no declarations;
  its JSON record and the current module-mode convention were read. This delivery follows
  the explicit `module`, `public import`, `@[expose] public ... section` convention.

Validation: all compiler calls use the prescribed `scompile.py Q91
lem-pur-tate-unit-flat-model-domains` wrapper. The module compiles in sandbox and library
modes with no errors or warnings apart from any expected sorry diagnostic. The only
elaboration fixes concerned field-projection line breaks in the shift and comparison
expressions. No statement was weakened to repair an elaboration error.

## Second reading by Q91

I reread the final node statement and the final module clause by clause. This is a worker
self-check; the maintainer supplies the independent delivery review. The index tables
were expanded: model 0 is R, model 1 is J, model 2 is R tensor J; object 0 is U, object 1
is the actual U(m), object 2 is that object[n]. The reduction table is A_j[0], A_j(m)[0],
A_j(m)[0][n]; the Tor degrees are 0,0,-n. The test-module quantifier ranges over every
finite-coefficient module sheaf, and the theorem's first model quantifier covers every
integer shift. The positive reduction encoding is j+1 throughout.

The first draft only asserted existence of reduction isomorphisms. On rereading the word
"canonically", I replaced that clause by invertibility of explicit reduction arrows built
from the uniquely normalized line map, actual coefficient-projection transpose, standard
single/shift comparisons and the uniquely pure-tensor-normalized multiplication mu.
The ordinary-versus-strict comparison now also includes its exact representative equation
and the identity-inclusion normalization, rather than invertibility alone. The original
node statement is unchanged. The data choices all come from the existing uniquely
characterized constructions, and no arbitrary isomorphism or flatness hypothesis was added.


## Repair of independent return 17c3159ee905

R1 (H2): added `def-weil-constant-coefficient-objects`, with `lean.existing: true`
and all four existing definitions from `Sheaf.Paper.ConstantCoefficientObjectsConstructible`.
Replaced the theorem edge in stmt_deps with this definition edge; the theorem remains
in proof_deps. The twist-preserves edge remains genuine: the line reduction selects
its uniquely normalized `TwistReductionMaps` witness. No existing source was rewritten.

R2 (H3): replaced the conjunction-wide `∃! μ` by `∃ μ, (∀ μ', pureTensor μ' ↔ μ' = μ) ∧ rest`.
Here pureTensor is written out sectionwise, not defined privately. Thus every isomorphism
satisfying the pure-tensor equation equals μ, independently of all later conclusions.
Taking μ' = μ also entails the equation for μ itself. All later reduction maps still
use that same μ; no later clause or hypothesis was changed. The module source header
now names the node's agent-auxiliary source place (Old Steps 1–3).

## New nodes

`def-weil-constant-coefficient-objects` owns the existing finite and integral regular
module objects in degree zero, the completion projection as a linear map, and its
normalized adjunction transpose. Its source is the blueprint coefficient-sheaf paragraph
and the already used Bhatt–Scholze completed-sheaf presentation (§§3.5, 6.5, 6.8).
No module is added: the four definitions at lines 55–93 of
`Sheaf.Paper.ConstantCoefficientObjectsConstructible` give exactly this construction.
LeanSearch and LeanFinder with query “finite constant coefficient object completed
coefficient regular module degree zero and canonical derived reduction map” each gave
eight unrelated hits; Mathlib grep of the four exact names gave zero hits. Project rg
found these four definitions, upstream rg none; DAG name/ownership searches and
`blueprint_refs.py search 'constant coefficient'` found related nodes but no definition
node for these four constructions. The existing theorem node records constructibility
and scalar normalization rather than owning these plain definitions. Its theorem is
retained for the proof. The new node makes no claim of constructibility or invertibility.

## Repair second reading by Q91

I reread the changed theorem and ownership node against the return and source signatures.
The new node permits every scheme Y, every finite E, and all positive levels n+1;
its objects and maps are exactly the four recorded real definitions. The coefficient
projection sends 1 to 1, and the derived map is its adjunction transpose including the
single-functor comparison. The adjunction theorem is used for its actual normalized
adjunction witness, not as an owner of unrelated plain definitions. Empty Y and the
first positive quotient are included. For the item, μ is now unique from the pure-tensor
formula alone. Specializing μ' = μ recovers that formula; arbitrary μ' with the formula
must equal μ even without the later conditions. The remainder still quantifies over
all three models, shifts, finite coefficient inclusions (including identity), reductions,
and arbitrary test modules, with the same intervals 0,0,-n. The saved packet was first
validated unchanged by a dry run; its successful mechanical check did not discharge
the two mathematical/dependency return points, which are repaired above.


Repair validation: `scompile.py` passed both modes (14.1 s sandbox, 11.3 s library).
The first repaired dry run required the new-node schema field `import_flags`; added
its empty array. Its advisory also revealed the live ancestor path has one additional
node, `lem-pur-adic-purity-scalar-naturality`; updated the new node's via to the live
path. The twist-preserves theorem-edge warning is the point explicitly approved in
the independent return: the actual uniquely pinned theorem witness is used.
