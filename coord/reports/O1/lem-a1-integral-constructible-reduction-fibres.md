## Worker report

The new module is `Sheaf.Paper.IntegralConstructibleReductionFibres`, namespace
`AlgebraicGeometry.Scheme.A1Integral`. Its principal statement is
`integralConstructibleReductionFibres`. No natural-language statement changes,
new DAG nodes, or dependency record repairs are proposed.

The helper definitions construct the ordinary quotient functors, quotient projections,
quotient transitions, their etale direct-image towers, their stalk towers, and the
ordinary inverse-limit functors. All data are real constructions. The only postponed
proofs are the principal theorem and `regularCounit_isIso`, the flat-unit counit
normalization needed to construct the actual vector 1 in its completed coefficient fibre.
That helper is part of the coefficient/section normalization of this node, with its
own source and proof docstring; it does not choose a module, fibre, or comparison from
mere existence. Inverting its specified counit postpones only the inverse-law proof.

Hypotheses and clauses, in the order of the DAG statement:

- The field is `{k : Type u} [Field k]`. The coefficient prime is
  `(l : ℕ) [Fact l.Prime]`; `[Fact (IsUnit (l : k))]` is precisely invertibility in k.
- `W : PerAdic.Base k` is the dependency's existing bundle of a k-scheme, its structure
  morphism, locally finite type, quasi-compactness, and separatedness. There is no
  connectedness, nonemptiness, finite-field, smoothness, or freeness hypothesis.
  `PerAdic.baseNoetherian`, `baseDimension`, and `basePrimeUnit` give the derived
  finiteness hypotheses already supplied by finite type over a field.
- `E : Type u` with `Field`, `Algebra (Padic l) E`, and `FiniteDimensional` is the finite
  coefficient extension. `PbcIntegralRing l E` is the recorded ULift of its valuation
  ring, and `pbcUniformizer l E` is the lift of its recorded chosen uniformizer.
  ULift changes no algebraic data. The inclusion into E is `PerAdic.integerToField`.
- The completed ring is `pbcAdicCompletion W.scheme (pbcIntegralDatum l E)` in the
  recorded PBC coefficient presentation. The normalized coefficient comparisons in
  the imported completed-coefficient and presentation-transport modules identify
  this with the inverse limit in `def-weil-completed-integral-coefficients`.
  `pbcCompletedScalar` and `adicLisseConstantUnit` supply the actual constant action;
  `scalars` retains the original sections and restriction maps.
- The source explicitly regards the integral heart object as its degree-zero sheaf.
  `Heart` is exactly that sheaf presentation: the existing predicate
  `PbcIsBoundedConstructibleComplete` applied to `DerivedCategory.singleFunctor _ 0`.
  The predicate still includes derived completeness, uniformly bounded constructible
  reductions and existence of compatible etale-origin witnesses. The imported
  `pbc_integral_tstructure` identifies these sheaves with the integral standard heart.
  This abbreviation imposes no condition on their ordinary module torsion.
  `toIntegral` places exactly this sheaf in degree zero in the recorded integral category.
- Index `n : ℕ` denotes the positive exponent n+1, so every n≥1 of the source occurs.
  `quotient l E T n` is the cokernel of scalar multiplication by ϖ^(n+1) in the
  functor category of completed-coefficient module sheaves. Evaluation computes this
  cokernel pointwise, so it is the ordinary sheaf quotient F/ϖ^(n+1)F.
  `quotientProjection` is its actual cokernel projection.
- `etaleTower` is canonically `comparisonLowerStar` applied to these ordinary
  quotients after restriction to constant A-scalars. The first theorem conjunct
  asserts invertibility of the actual comparison adjunction counit, giving
  ν*G_n ≅ F_n with the canonical map, rather than an arbitrarily chosen origin.
- A finite quotient coefficient module is encoded as its A-module annihilated by
  `(Ideal.span {pbcUniformizer l E})^(n+1)`. This is the existing encoding in
  `Padic.adicLimit_finite_modules` and `IsLisseIntegralDiagram`. The first conjunct
  asserts this annihilation on every etale section. Such an action has a unique
  descent to A/ϖ^(n+1), and A-linearity is exactly quotient-ring linearity.
- `quotientTransition` is `cokernel.desc` of the lower quotient projection, so its
  composite with the higher projection is the lower projection. `Functor.ofOpSequence`
  retains every composite, identity, and cocycle; direct image preserves these maps.
  The second conjunct supplies a zero-composite proof and the cokernel universal
  property for the actual etale transition G_(n+1)→G_n under multiplication by ϖ^(n+1).
  This says that its induced ordinary quotient isomorphism is the specified one.
- The third conjunct supplies one `FiniteLocallyClosedStratification W.scheme` for M,
  before quantifying over all levels. It includes the actual scheme immersions.
  On each stratum and each level, the two displayed covers give isomorphisms of module
  sheaves to constant `N : ModuleCat A` with `Finite N`, respectively on the pro-etale
  and etale sites. This is local constancy with finite module values, not freeness and
  not merely finite generation over the infinite ring A. Etale constructibility follows
  on this finite partition; its locally closed strata are constructible because W is
  Noetherian. Both assertions use exactly the same partition.
- The geometric point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ W.scheme)`. `stalkTower` uses the existing
  `(pointSmallEtale x).sheafFiber`, whose diagram is precisely
  `pointedEtaleStalkDiagram`. `sectionResidue` uses `pointedEtaleGerm` of the final
  etale neighbourhood. These are the recorded etale stalks.
- `limitFiber` is `lim` of that strict stalk tower, so its value is exactly P_x.
  The fourth conjunct gives `Module.Finite A P_x`. Its projections are surjective and
  have kernel `(ϖ)^(n+1) • ⊤`; the first isomorphism theorem therefore gives precisely
  the projection-induced isomorphisms P_x/ϖ^(n+1)P_x ≅ (G_n)_x.
- The final conjunct supplies a natural isomorphism `c` from
  `toIntegral ⋙ pbcRationalization ⋙ PerAdic.fiber` to the inverse-limit stalk functor
  followed by `ModuleCat.extendScalars (PerAdic.integerToField l E)`.
  This is the dependency's actual raw rational category and normalized fibre.
  Extension of scalars uses E⊗_A P; the standard tensor symmetry identifies this
  canonically with the displayed P⊗_A E of the node, without changing its vectors
  or linear maps. A natural isomorphism, rather than unrelated objectwise isomorphisms,
  expresses naturality in every integral sheaf morphism.
- `rawFiberComparison` is obtained from the equality in the recorded
  `PerAdic.fiber_existsUnique`, not an additional assumed comparison. It identifies
  the sheaf formula with exactly the fibre of Q applied to its single complex.
- For every actual sheaf morphism `a : coefficientUnit ⟶ M.obj`, `sectionResidue`
  applies a to 1, takes the actual ordinary quotient projection, restricts to the
  final etale object, and takes its germ. The final clause gives an element b whose
  every limit projection is that residue. Limit projections are jointly injective,
  so these values determine b uniquely. An A-linear section of a sheaf annihilated
  by ϖ^(n+1) uniquely factors through the constant A/ϖ^(n+1) module, giving exactly
  the induced finite-coefficient maps in the node. Their compatibility is retained
  by the constructed quotient tower. `coefficientOne` is the genuine point pullback
  of 1 through the ordinary derived counit and completion unit, tensored with 1.
  The final equality says c carries the fibre of Qa at this vector to 1⊗b,
  equivalently b⊗1 in the node's tensor order. It is an actual normalization equation,
  not a chosen arbitrary trivialization of the source fibre.
- Every quotient is an ordinary cokernel. No clause asserts that the derived finite
  reduction is concentrated in degree zero.

Recorded dependency declarations used, with their modules:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionRing` and their source data.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the unchanged completed
  coefficient sheaves, with the normalized PBC coefficient-presentation comparisons.
- `Sheaf.Paper.IntegralTStructure`: `pbcIntegralTStructure`, `pbc_integral_tstructure`.
- `Sheaf.Paper.IntegralUniformCoefficient` and its imported
  `Sheaf.Paper.BoundedConstructibleComplete`: the preserved general
  `PbcIsBoundedConstructibleComplete`, `PbcBoundedConstructibleComplete`,
  `PbcIntegralRing`, `pbcIntegralDatum`, and `pbcUniformizer`.
- `Sheaf.Paper.PbcRationalCategory`: `pbcRationalization`, `pbcCompletedScalar`,
  `pbcCompletedSection` and the actual completed-module linearity instance.
- `Sheaf.Paper.AdicHeartIntrinsicFibres`, reexporting
  `Sheaf.Paper.AdicHeartPullbackFibres`: `PerAdic.Base`, `PerAdic.fiber`,
  `PerAdic.fiber_existsUnique`, `PerAdic.pointSections`, `PerAdic.integerToField`.
  This uses the preserved original PBC interface, so no intrinsic-sf coefficient
  transport is introduced by this delivery.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and its constructible-sheaf imports:
  the small etale site, sheaf encoding, and etale inverse image.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: the recorded module comparison,
  through `AlgebraicGeometry.ProEtale.comparisonLowerStar`, `comparisonUpperStar`,
  and `comparisonAdjunction` with exactly the original small sites.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, with no extra constructibility condition.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleGerm`; the diagram and
  `pointSmallEtale.sheafFiber` are the same pointed-neighbourhood colimit.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`/`SheafOfModules`;
  ordinary quotients are in their unchanged abelian category.
- Mathlib `IsAlgClosed`, `Scheme.SpecToEquivOfField` (geometric point convention),
  `Module.Finite` (finite generation), `cokernel`, `CokernelCofork.ofπ`, `limit.π`,
  `ModuleCat.extendScalars`, and `DerivedCategory.singleFunctor`.
- For coefficientOne: the already recorded `pbcActualModuleUnitSection`,
  `pbcActualPullComplexCounit`, `pbcActualCompletedPullUnit`, and Mathlib's
  `mapCochainComplexSingleFunctor`, `singleFunctorCompHomologyFunctorIso`.

All proof-only dependency modules are imported without `public`; dependencies also
used by the statement are publicly imported. Mathlib proof matches are imported at their recorded source
modules. No proof-dependency import cycle with the newly introduced module exists.

Edge cases checked against the source before writing:

- The empty scheme is allowed. A zero-stratum partition is valid, covering clauses
  are vacuous, and all sheaf/stalk assertions have their usual empty-site interpretation.
- The zero heart sheaf has zero ordinary quotients, zero stalk limit and zero rational
  fibre; the zero section satisfies the displayed residue and fibre formula.
- n=0 in Lean is the first positive quotient A/ϖ. No positive level is dropped.
- A torsion local model N=A/ϖ^r has quotient N/ϖ^nN, inverse limit N, and zero rational
  tensor fibre. The statement retains this case and does not ask N to be free or
  derived reduction to be concentrated in degree zero.
- A free rank-one model recovers A/ϖ^n, A and E, and the canonical vector 1.
- Finite covers may use varying finite module models; the one stratification is
  independent of n, while the trivializing covers may depend on n as the node permits.
- Arbitrary integral sheaf maps are included. Naturality is on the full category of
  sheaves satisfying the integral predicate, and the section clause quantifies over
  every sheaf morphism from the actual regular coefficient module.
- The base k is any field with l invertible; no finite-field datum is introduced.

Searches made (2026-10-18):

- `msearch.py ... leanfinder "integral constructible adic sheaf finite ordinary quotients
  geometric fibre inverse limit"`: eight hits, including AdicCompletion and local
  cohomology, but no sheaf quotient/origin/fibre comparison statement.
- `msearch.py ... loogle "SheafOfModules, cokernel"`: zero hits; service reports unknown
  identifier cokernel. Direct Mathlib reading supplies its categorical cokernel API.
- `msearch.py ... grep "adic.*fibre|integral.*constructible.*reduction"`: zero hits.
- `rg` for the node id and integral-constructible-reduction names in the upstream
  WeilConjectures tree and side Sheaf tree: only the downstream proof reference in
  `AdicSectionClosedSupport`; no existing declaration of this statement.
- Direct `rg` of Mathlib's site, module-sheaf, derived-single and change-of-rings
  sources, and of the project's coefficient, integral-heart, stratification,
  finite-origin and adic-limit modules, located the constructions reused above.
- Read the exact module/signature/docstring records of every statement dependency.
  Read the source PDF with pdftotext at 5.1.5, 6.8.2, 6.8.10--6.8.11 and 6.8.14;
  these explicitly permit finitely presented torsion local models.

No STATEMENT-DISPUTED flag, counterexample, or natural-language node fault was found.

## Second reading by N1

Independent maintainer reading of immutable delivery d044f2e8c27bc9a1747cf4b39ce0699781070fcc,
2026-10-18. The reviewer did not author or previously second-read this delivery.
Read packet.md, the complete check-brief2.md, the snapshot item and all fourteen
statement dependency records, the delivered module and report, and the exact reused
Lean declarations in the read-only group/source trees.

Clause and hypothesis checks:

- Arbitrary field k, prime l invertible in k: Field, Fact l.Prime and the explicitly
  included Fact (IsUnit (l : k)); no finite-field or characteristic-zero assumption.
  PerAdic.Base has exactly separatedness, locally finite type and quasi-compactness
  over Spec k. These imply the source's Noetherian and finite-dimensional hypotheses.
- E is a finite-dimensional extension of Padic l. PbcIntegralRing and pbcUniformizer
  reuse the recorded valuation ring and chosen uniformizer through ULift. No extra
  topology, freeness or coefficient choice is assumed.
- pbcAdicCompletion is the inverse limit of the recorded finite coefficient sheaves;
  pbcCompletedScalar fixes the constant-scalar action. The original small pro-etale
  site is retained, with object universe u+1 and morphism universe u. All variables
  are bound with autoImplicit and relaxedAutoImplicit disabled. The common u follows
  the recorded Scheme/Spec and PerAdic interfaces; the coefficient modules are in u+1.
  No equality of the site's object and morphism universes is imposed.
- Heart is the sheaf presentation of the existing full integral standard heart:
  the single complex satisfies the original three-part complete/constructible/
  compatible-origin predicate. toIntegral and underlying keep its actual arrows.
  The integral t-structure's explicit heart characterization justifies this presentation.
- quotient is the ordinary cokernel of uniformizer^(n+1), and quotientProjection is
  its actual projection. n=0 represents the first positive exponent. etaleTower is
  comparisonLowerStar of these same sheaves with their constant-scalar action.
  The first conjunct states that the actual comparison counit is invertible and that
  the ideal power kills all etale sections. This is exactly a sheaf of modules over
  the finite quotient ring, encoded as an annihilated A-module.
- quotientTransition is induced by the lower cokernel projection; the strict sequence
  retains composites and identities. The second conjunct asserts the cokernel property
  for the actual transition. It gives G_(n+1)/uniformizer^(n+1) = G_n in the shifted
  indexing, including the canonical quotient map and its compatibilities.
- The third conjunct chooses one FiniteLocallyClosedStratification before all levels.
  Both pro-etale and etale cover clauses use that same partition and constant modules
  with Finite underlying type, not merely finite generation over A. This gives exactly
  the two finite local constancy assertions. Noetherianity makes the strata constructible.
- The point is Spec Ω -> T for an algebraically closed field. stalkTower uses the
  recorded pointed-etale-neighbourhood colimit (pointSmallEtale.sheafFiber), and
  limitFiber is its ordinary limit. The fourth conjunct states Module.Finite and
  surjectivity/kernel equations for the actual limit projections. Thus it gives the
  required projection-induced reduction isomorphisms, including torsion.
- The last conjunct is a natural isomorphism from the actual raw rationalization
  followed by PerAdic.fiber to limitFiber followed by extension of scalars. E tensor P
  is canonically P tensor E by tensor symmetry. rawFiberComparison uses the prescribed
  equality in fiber_existsUnique; it introduces no arbitrary fibre or trivialization.
- For every actual map from the regular coefficient module, sectionResidue takes
  the ordinary quotient of a(1) and its pointed germ. The final clause gives b with
  exactly these projections and the displayed equation for its rational fibre image.
  Joint injectivity of limit projections gives uniqueness and compatibility. integralOne
  is the explicit section pulled through the ordinary derived counit and completion
  unit; coefficientOne tensors it with 1. No arbitrary map replaces this construction.
- No derived finite reduction is asserted to be concentrated in degree zero.

Dependency/source checks:

Read CoefficientExtensionFinite and CoefficientExtension; CompletedIntegralConstantMapOfUniverses
and CompletedIntegralCoefficients; IntegralTStructure; IntegralUniformCoefficient and
BoundedConstructibleComplete; PbcRationalCategory; AdicHeartIntrinsicFibres and the
reexported AdicHeartPullbackFibres; the group's WeilConjectures/AlgebraicGeometry/EtaleSheaves;
ProEtaleSiteComparison and the group's exact WeilConjectures/SixFunctors/ProEtale/Comparison/Defs;
FiniteLocallyClosedStratification; PointedEtaleStalk and geometricStalkFunctor in the group's
StrictHenselization module; RingedSiteModules; Mathlib IsAlgClosed, SpecToEquivOfField and
Module.Finite. The scheme-properties dependency is explicitly a convention collector.
These are the same notions used in the statement. The set-only local-constancy predicate
is not misapplied to module sheaves: the module conclusion supplies the actual constant
module charts. Read pefw-upstream-framework.md and used the group's side sources.

Read Bhatt--Scholze PDF pp. 34-35 and 58-62: Lemmas 5.1.2, 5.1.4, Corollary 5.1.5,
Lemma 6.8.2, Proposition 6.8.4(1), Definition 6.8.10, Propositions 6.8.11(3) and 6.8.14(2).
Definition 6.8.10 allows finitely presented torsion modules. Read Stacks proetale.tex
lemma-compare-locally-constant (line 4121, Tag 099Y) and lemma-compare-constructible
(line 5239, Tag 09AK); the finite quotient rings meet its Noetherian hypothesis.
Read the local-model interface in IntegralStratifiedPerfectCharacterization, the
completed reduction and finite-ring origin interfaces, AdicLimitFiniteModules and
PbcCompletedPullbackActual's explicit unit/counit/completion constructions.

Independent searches with rg in Mathlib, the read-only upstream WeilConjectures tree
and the group's Sheaf tree for A1Integral, integralConstructibleReductionFibres,
ordinary quotient/fibre comparisons and constant-module presheaf transport found no
existing theorem replacing this item. Reused cokernel, constantSheaf, scalar restriction,
limit, module finite generation and stalk APIs instead of duplicating those notions.
The worker's three search kinds are recorded. No new independent prerequisite or
universe repair is needed. No statement_change was proposed, so no citer audit is due.

Edge cases: empty scheme and zero strata; zero sheaf and zero section; first positive
level; torsion A/uniformizer^r and mixed torsion/free local models; rank one and its
vector 1; arbitrary allowed characteristic; covers and models varying with level;
all integral morphisms. No connectedness, nonemptiness, smoothness, flatness of F,
or torsion-free hypothesis is introduced.

Findings and repairs:

H6 (local proof and proof-separation gate): the delivered scalarPresheaf identity/composition laws, scalars naturality,
quotientTransition zero-composite proof and rawFiberComparison equality were proved
locally. Move these obligations to five named sorry theorems with source, blueprint
and proof-plan docstrings, using the transparent scalarData helper. Use the existing
Category.comp_id proof for the pointed-neighbourhood triangle. The integralOne tactic
block only unfolds the irreducible pointSections and returns the explicit vector;
it proves no proposition and contains no sorry data. Every explicit proposition proof
in the corrected module is now a named theorem with only sorry. All helper declarations
are listed in the replacement lean record and belong to this node's constructions.

H11: the delivered second-reading section honestly recorded only worker cross-checking.
This replacement supplies the independent reading and retains the entire Worker report.
No mathematical statement, hypothesis, conclusion or dependency list changed.
The principal lean.statement was checked byte-for-byte against the immutable module's
signature and remains byte-for-byte identical after repair. All lines are at most
100 characters; declaration and module source/blueprint docstrings are present.

Route pivot: read origin/newtargets-dag:coord/route-pivot-dropped.txt with git show;
its intersection with the item's statement/proof dependencies is empty. There is no
repair note at coord/repair-notes/lem-a1-integral-constructible-reduction-fibres.json.
The proof uses ordinary derived pullback, K-flat normalization, completion and raw
scalar localization; no infinity/dg/model-category machinery is reintroduced.

Compiler evidence is recorded in review.md. No global build, direct SSH command,
live Lean write, repository edit, branch change, claim, delivery or merge was performed.

## Independent compiler validation

The worker recorded successful scompile.py and deliver2.py --no-push checks, the latter
at dry-run commit 1d55dc00a0. The maintainer independently reproduced compilation of
the immutable snapshot, then the complete corrected module through the prescribed
scompile.py wrapper, without changing timeout settings. Both final invocations exited 0
with empty diagnostic bodies for sandbox and library-path compilation.

Immutable command:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N1 lem-a1-integral-constructible-reduction-fibres snapshot/lean/Sheaf/Paper/IntegralConstructibleReductionFibres.lean`

Corrected command:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N1 lem-a1-integral-constructible-reduction-fibres fixes/lean/Sheaf/Paper/IntegralConstructibleReductionFibres.lean`

The installed wrapper announces server checking, and returns a private side-overlay
sandbox compile and a library-path compile. Snapshot output: sandbox [30.4 s], library
[76.2 s]. Corrected output: sandbox [15.9 s], library [104.9 s]. These are the wrapper's
reported elapsed totals; the wrapper announces a 60-second compile limit after slot
acquisition. Neither invocation reported a timeout or error. No global build was run.
An intermediate corrected version failed because a direct expression did not unfold
irreducible pointSections; restoring the original explicit unfolding fixed this.
The final compiler run checks all five added theorem signatures and all real constructions.
