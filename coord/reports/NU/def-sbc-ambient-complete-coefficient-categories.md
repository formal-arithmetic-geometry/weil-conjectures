## Worker report

The delivery defines the ambient and constructible coefficient categories with both
finite-stage and outer Karoubi envelopes, canonical scalar transitions, coherent
inclusion comparisons, and the descended constructible-to-ambient functor. It reuses
the published raw complete and constructible categories. The main declaration is
`AlgebraicGeometry.Scheme.pbcConstructibleCompleteQbarInclusion` in
`Sheaf.Paper.AmbientCompleteCoefficientCategories`.

The node's hypotheses and clauses are rendered as follows:

1. The prime and chosen closure are `(l : ℕ) [Fact l.Prime]`, `Padic l`,
   `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`;
   `Padic.FiniteCoefficientFields l Ω` is the recorded finite intermediate-field set.
2. The scheme is `(W : Scheme.{u}) [IsNoetherian W]`, with
   `[Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]` and
   `[Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]`. Universes `u v` are independent.
3. `pbcAmbientCompleteStage` is the published `PbcRationalComplete` on
   `PbcComplete`, the full subcategory cut out by `PbcIsIntrinsicallyComplete`;
   its completed ring and uniformizer come from `pbcIntegralDatum` and `pbcUniformizer`.
4. Raw localization retains integral objects and uses `Localization.Away p ⊗[A] Hom`;
   the canonical localization of the integer ring is the coefficient field.
   `pbcAmbientCompleteKaroubiStage` is its actual Mathlib Karoubi envelope.
5. `pbcConstructibleCompleteStage` is `PbcRationalConstructible`, hence exactly
   `PbcRationalCategory` of `PbcBoundedConstructibleComplete`;
   `pbcConstructibleCompleteKaroubiStage` takes its finite-stage Karoubi envelope.
6. Mathlib `Karoubi` supplies arbitrary projectors, projector-compatible arrows,
   projector identities and underlying composition at each envelope.
7. `pbcConstructibleCompleteInclusion` extends the published `pbcRationalInclusion`,
   whose Hom map is scalar base change of the actual integral full inclusion.
8. `pbcAmbientCompleteIntegralTransition` restricts actual ambient tensor;
   `pbcAmbientCompleteRawTransition` is its uniquely characterized localization,
   normalized to the identity at equal fields. Constructible transitions use
   the recorded `pbcScalarExtension`. The two Karoubi transitions extend these.
9. The integral and raw unit/comparison/associator declarations fix the canonical
   balanced tensor comparisons. `pbcAmbientCompleteRaw_laws`,
   `pbcCompleteKaroubi_cocycle`, and `pbcCompleteSystem_units` state the inherited
   addition, unit and tower equations. The two named systems assemble those data.
10. `pbcCompleteRawInclusionComparison` is fixed by the identity integral comparison;
    its actual Mathlib extension `pbcCompleteKaroubiInclusionComparison` retains the
    projector-sandwich components and inverse. `pbcCompleteInclusion_coherent`
    states the unit and tower equations for the same comparison through the systems.
11. Each system's existing `StageSystem.PairCategory` uses common-field representatives,
    associator-conjugated transport and eventual equality; identities, addition and
    composition are its published operations. The additive-transition and
    finite-biproduct declarations expose the additive structures.
12. `pbcAmbientCompleteQbarCategory` and `pbcConstructibleCompleteQbarCategory` are
    Karoubi envelopes of the respective systems of finite-stage Karoubi categories.
    Thus objects are `((E,(K,p)),e)`, with both projectors retained.
13. `pbcCompletePairInclusion` applies the uniquely representative-characterized
    `StageSystem.coefficientPairFunctor`; its formula is source comparison, stage
    inclusion, inverse target comparison. The primary declaration applies
    `Idempotents.functorExtension₂` to this functor, retaining both projectors.
14. `pbcRawAmbientStageToComplete` and `pbcRawConstructibleStageToComplete` are
    identity-projector inclusions. `pbcRawPairToComplete` uses their canonical
    comparisons and `pbcRawQbarToComplete` adds the outer identity projector.
    No equivalence with a raw category is asserted, and no constructible bound
    is imposed on the ambient objects.

Dependency declarations used: `Padic.FiniteCoefficientFields`
(`Sheaf.NumberTheory.Padics.FiniteCoefficientFields`);
`completedReductionTower` (`Sheaf.Paper.AdicCoefficientDatum`);
`IsCompletedIntrinsicallyDerivedComplete` (`Sheaf.Paper.IntrinsicCompletionCompleted`);
`ScalarLocalization` (`Sheaf.CategoryTheory.ScalarLocalization`);
`CategoryTheory.Idempotents.Karoubi` and `functorExtension₂` (Mathlib);
`pbcScalarExtension`, `pbcScalarAssociator`, `pbcAmbientScalarExtension`,
`pbcAmbientScalarUnit`, `pbcAmbientScalarAssociator` (`Sheaf.Paper.PbcScalarExtension`
and its published `FiniteStagePairCategory` interface);
`PbcBoundedConstructibleComplete` (`Sheaf.Paper.BoundedConstructibleComplete`);
`PbcRationalCategory` (`Sheaf.Paper.PbcRationalCategory`);
`pbcQbarCategory` (`Sheaf.Paper.PbcQbarCategory`);
`pbcIntegralDatum`, `pbcUniformizer` (`Sheaf.Paper.IntegralUniformCoefficient`);
`Padic.finite_coefficientExtensionRing` (`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`);
`PbcComplete`, `PbcRationalComplete`, `PbcRationalConstructible`, `pbcRationalInclusion`
(`Sheaf.Paper.SbcCompletedOperations`); and the original
`CommonStage.coherent_pair_functor_descent` (`Sheaf.CategoryTheory.CoherentPairFunctorDescent`),
transported to the published `StageSystem.PairCategory` interface as documented below.
The size dependency is metatheoretic and is rendered by explicit universes.

Edge cases checked: empty schemes, zero objects, zero and nonidentity projectors at
both layers, equal coefficient fields and repeated fields in associators, the base
coefficient field as a common-stage witness, and independent scheme/closure universes.
There is no nonemptiness assumption on W and no ambient constructibility bound.
No statement correction or STATEMENT-DISPUTED flag is needed.

Searches retained in `searches.jsonl` include LeanFinder for complete coefficient-field
pair categories (no exact match), Loogle for Karoubi and functor extensions (generic
ingredients only), LeanSearch for rationalized derived complete categories (no exact
match or service unavailable), and grep/rg on Mathlib, upstream and `lean/Sheaf`
(only the published component interfaces, no full construction). The detailed queries
and results for the new node and dependency transport are recorded below.

Current repair validation (2026-10-16): all three delivered modules compiled with the
prescribed `scompile.py` in dependency order, with no errors or disallowed warnings.
The previous missing `ProEtale.upperStar/lowerStar` prerequisite failure no longer
reproduces. The current full pass compiled the descent interface in 2.8 s, raw scalar
system in 10.7 s, and main coefficient categories in 22.5 s. The saved truncated
`lean.statement` for the descent theorem is now the full verbatim signature, and
all three node signatures were checked against the source. The new-node section now
has the required heading. The earlier second reader's detailed review follows.

## Earlier second reading (a previous round; superseded)

I read the complete node and its sketch32 source, not a Stacks tag: the source
is `literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex`,
“Ambient and constructible E-coefficient categories” (1191–1228), “Finite-stage
pair categories over Qbar” (1291–1338), and “The two Qbar-coefficient categories”
(1413–1439), with the preceding adic hypotheses and following smooth-base-change
application. The source really takes a Karoubi envelope at each finite stage
and then another one after the pair category. The node already says this
correctly. No statement correction is needed, and no node statement was changed.

My object/hypothesis/conclusion list and the Lean matching it are:

1. Prime ell, Q_ell, chosen algebraic closure, finite intermediate fields,
   independently sized scheme and algebraic closure: `(l : ℕ) [Fact l.Prime]`,
   `Padic l`, `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
   [IsAlgClosure (Padic l) Ω]`, `(W : Scheme.{u})`, and
   `Padic.FiniteCoefficientFields l Ω`. Verdict: exact. I opened
   `FiniteCoefficientFields.lean`: it is the subtype of intermediate fields
   finite-dimensional over Q_ell, with compositum and base-field witnesses.
2. W noetherian, finite-dimensional, ell invertible: `[IsNoetherian W]`,
   `[Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]`, and
   `[Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]` in the primary definition.
   Verdict: exact; stalkwise invertibility is the node's condition. Earlier
   category aliases make sense more generally, without strengthening the main
   declaration's assumptions.
3. Completed coefficient ring, uniformizer and intrinsic-complete integral
   category B_E: `pbcStageDatum`, `pbcStageUniformizer`, and the existing
   `WeilConjectures.PbcComplete l (pbcFiniteField l Ω E) W`. I opened
   `PbcFiniteCompletedCoefficientMap.lean`, `BoundedConstructibleComplete.lean`,
   `IntrinsicCompletionCompleted.lean`, `IntrinsicCompletion.lean` and
   `SbcCompletedOperations.lean`. `PbcComplete` is the full subcategory defined
   by `PbcIsIntrinsicallyComplete` on the actual completed-ring derived category;
   that predicate uses the published completion under its canonical coefficient
   comparison. Verdict: exact, with no boundedness predicate in the ambient category.
4. Raw localization R_E, with unchanged integral objects and tensor Hom:
   unchanged `pbcAmbientCompleteStage` reuses `PbcRationalComplete`. I opened
   `ScalarLocalization.lean`: its carrier stores an integral object, its Hom is
   `Localization.Away p ⊗[R] Hom`, and composition is the bilinear pure-tensor
   formula. The coefficient extension interfaces identify this localized ring
   with E. Verdict: exact. No equivalence to a Karoubi envelope is assumed.
5. Constructible integral B^c_E and its raw R^c_E: unchanged
   `pbcConstructibleCompleteStage` reuses `PbcRationalConstructible`, which is
   exactly `PbcRationalCategory` on the existing
   `PbcBoundedConstructibleComplete`. I read that predicate's completeness,
   uniform reduction bounds and compatible etale-origin clauses, and the
   `IntegralUniformCoefficient` and `PbcRationalCategory` recorded interfaces.
   Verdict: same objects as the dependency nodes; no private constructibility notion.
6. Finite-stage categories C_E = Kar(R_E), C^c_E = Kar(R^c_E), their arbitrary
   projectors, projector-compatible arrows, composition, and projector identities:
   unchanged `pbcAmbientCompleteKaroubiStage` and
   `pbcConstructibleCompleteKaroubiStage`, using Mathlib `Idempotents.Karoubi`.
   I read Karoubi.lean (carrier, Hom, category identity/composition) and
   FunctorExtension.lean. Verdict: exact, including nonidentity projectors.
7. j_E, its localized Hom map, and J_E on (K,p): unchanged
   `pbcConstructibleCompleteInclusion` applies Mathlib `functorExtension₂` to
   the existing `WeilConjectures.pbcRationalInclusion`. That raw functor is
   `ScalarLocalization.between` of the actual integral full inclusion, using
   base change of its linear Hom maps. Verdict: exact tensor-Hom formula, and
   the inner projector is sent to its image rather than to an identity.
8. Canonical integral coefficient extension and raw rational extension:
   `pbcAmbientCompleteIntegralTransition` restricts the existing
   `pbcAmbientScalarExtension` along its completeness property.
   `pbcAmbientCompleteRaw_exists` characterizes the raw functor uniquely by
   its equality after integral localization, and
   `pbcAmbientCompleteRawTransition` uses that functor with a literal identity
   branch at E=F. I read `PbcScalarExtension`'s ambient tensor/completeness
   declarations and `FiniteStagePairCategory`'s actual completed maps,
   constructible restrictions and rational normalizations. Verdict: repaired;
   no arbitrary transition datum remains.
9. Specified tensor associators, repeated-field unit equations and pentagon:
   `pbcAmbientCompleteIntegralUnit`,
   `pbcAmbientCompleteIntegralComparison`,
   `pbcAmbientCompleteIntegralAssociator`, and
   `pbcAmbientCompleteRawAssociator` are fixed uniquely by the published
   section-normalized ambient unit/balancing and localization equations.
   `pbcAmbientCompleteRaw_laws` states the unit/additive/pentagon clauses.
   Verdict: repaired, retaining canonical comparisons rather than merely some
   associating isomorphisms. Every postponed law has its source, proof plan
   and this matching definition node in its docstring.
10. Extend transitions and associators to all finite-stage projectors:
    `pbcAmbientCompleteKaroubiTransition` and
    `pbcConstructibleCompleteKaroubiTransition` apply Mathlib's actual extension.
    Their named Karoubi associators apply `functorExtension₂.mapIso` to the
    specified raw balancing maps, with the composition identity adapter.
    `pbcCompleteKaroubi_cocycle` states the inherited pentagons.
    `pbcAmbientCompleteSystem` and `pbcConstructibleCompleteSystem` assemble
    precisely these data. `pbcCompleteSystem_units` records literal identity
    transitions and both repeated-field associators. Verdict: repaired;
    neither system is an unconstrained parameter.
11. Coherent inclusion comparisons b: `pbcCompleteRawInclusionComparison`
    is uniquely fixed as identity on the common integral tensor object, then
    `pbcCompleteKaroubiInclusionComparison` is constructed directly by Mathlib
    `functorExtension₂.mapIso` and its composition identity isomorphisms.
    `pbcCompleteInclusionComparison` re-expresses this exact isomorphism through
    the named systems, fixed uniquely by HEq of the whole datum. Its
    components are exactly the two-projector sandwiches. `pbcCompleteInclusion_coherent` states the unit and tower equations.
    Verdict: repaired, with the comparison orientation matching the node:
    `J_E ⋙ T_amb ≅ T_c ⋙ J_F` in Lean composition order.
12. Pair objects (E,(K,p)), representatives at a common overfield, equality
    after further transport, common-stage composition/addition, and outer
    Karoubi: `pbcAmbientCompleteQbarCategory` and
    `pbcConstructibleCompleteQbarCategory` are Karoubi of the respective
    canonical Karoubi-stage system's `PairCategory`. I read
    `WeilConjectures/CategoryTheory/StageSystem/Basic.lean`: its representatives,
    associator-conjugated transport, eventual-equality Setoid, Quotient Hom,
    identity, and composition are exactly these formulas. The existing
    `StageSystem.pairPreadditive` uses the normalized common-stage addition;
    the two additive-transition instances expose it here. I also read
    `CoherentPairFunctorDescent`'s `Diagram`, `Rep`, `transport`, `Hom`,
    `IsCanonical`, `Family.rep`, `IsDescent` and descent theorem. Verdict:
    repaired; the first worker paired the raw stages, so its claimed finite-stage
    Karoubi layer was missing on both sides.
13. J_pair and J_Qbar on every object/projector/represented arrow:
    `StageSystem.coefficientPairFunctor_exists` fixes both the object formula and every
    represented map as b_source, then J_M(u), then b_target inverse. It selects
    the unique functor so characterized. `pbcCompletePairInclusion_additive`
    records preservation of common-stage addition. The primary
    `pbcConstructibleCompleteQbarInclusion` is the actual `functorExtension₂`
    of that functor, with source and target the two full nested categories.
    Verdict: repaired; the first worker had no pair/outer inclusion at all.
14. Raw finite-stage and raw Qbar embeddings: `pbcRawAmbientStageToComplete`
    and `pbcRawConstructibleStageToComplete` are `toKaroubi`; the existing
    `pbcQbarCategory` remains the raw pair category. The new
    `pbcRawStageToCompleteComparison`, `StageSystem.coefficientPairFunctor_exists`, and
    `pbcRawQbarToComplete` apply the finite-stage identity projectors and then
    the outer identity projector. Verdict: repaired. An arbitrary inner or
    outer projector in the full categories is never replaced by an identity.

Edge cases: the empty scheme is permitted (no Nonempty scheme hypothesis), and
there is no ambient cohomological/constructibility bound. Zero objects, zero
projectors, arbitrary nonidentity projectors, and their projector identities
are retained by both Karoubi layers. Finite coefficient fields always include
the base field, so an empty collection of representatives has a common stage;
no empty-index failure is hidden. E=F and repeated fields use literal identity
transitions and the specified unitors. No special residue characteristic or
extra field/Noetherian assumption is added. Level zero in the existing reduction
interfaces is quotient by the first positive power, consistent with their
n+1 convention; this definition imposes no new n restriction. Scheme universe
u and closure universe v remain independent. `pbcFiniteField` transports a
finite-dimensional coefficient field through `Shrink`, not a universe equality;
the completed coefficient ring remains in u+1, with the existing small pro-etale
site's object/Hom universe distinction preserved.

Independent searches actually run in this reading, recorded by msearch.py in
searches.jsonl: LeanFinder “Idempotent completed category of derived complete
sheaf complexes with finite coefficient field transition tensor functors” gave
generic idempotent-complete complex/condensed-module/derived linearity results;
Loogle `CategoryTheory.Idempotents.functorExtension₂` found exactly the generic
extension ingredient, whose declaration and formulas I opened; grep
`complete.*(stage|coefficient)|Karoubi.*(Pbc|Complete)|AmbientComplete` found only
generic Karoubi/module-completion results. LeanSearch “Derived complete coefficient
categories formed by central localization and nested idempotent completion over
finite l-adic fields” found generic derived-category, localization and
idempotent-completeness declarations, not this construction. Direct rg on Mathlib,
the upstream WeilConjectures tree, this project's Sheaf tree, and the existing
StageSystem files found no duplicate complete coefficient system. I inspected
the upstream ClosedImmersionStages candidate: it uses a small-etale derived
complete rational category, not this completed pro-etale coefficient system and
its common-stage nested Karoubi inclusion, so it is not an existing match.

Mismatches repaired: arbitrary ambient StageSystem; omitted canonical tensor
and normalized coherence; raw instead of finite-Karoubi stages in both pair
categories; absent coherent inclusion comparisons; absent pair and outer
constructible inclusions; absent raw-to-nested embeddings. I kept the correct
raw stage aliases and finite-stage inclusion. The primary declaration is now
an actual constructed functor, not an unconstrained package. Choice is used only
for uniquely normalized constructions; definitions contain no sorry data or
unspecified nonempty choice. All law statements are construction clauses of their owning definition node,
listed in its lean.declarations. The raw ambient coherent scalar system is now
a separate new definition dependency, reviewed below. No target statement,
existing dependency statement, or mathematical proof was changed.
The node's lean.statement is copied verbatim from the primary file signature.

Additive-structure completion of clause 12: `pbcCompleteStages_finiteBiproducts`
states the finite biproducts for both finite-stage Karoubi categories, with
a proof plan through finite sums in the complete/constructible integral
subcategories, localization and Mathlib Karoubi biproducts. The two associated
instances let the existing generic `StageSystem.pbcPairFiniteBiproducts` provide
the pair biproducts; Mathlib's Karoubi biproducts then supply the outer ones.
This repairs a further omission in the initial package's claim of additive
pair categories. The pair inclusion's additive theorem is exposed as an instance.

Elaboration detail: the named tensor/comparison definitions and the two system
constructors are irreducible, retaining their real data while avoiding repeated
expansion of derived tensor/localization and the entire StageSystem record.
`pbcCompleteKaroubiInclusionComparison` is the actual Mathlib construction:
`Idempotents.coefficientCompositionIso` is `Iso.refl` on the identical
composition formulas; its inverse, `functorExtension₂.mapIso` of the fixed raw
comparison, and the other composition identity construct b. Its projector
sandwich and inverse are Mathlib's actual map on natural transformations.
`pbcCompleteInclusionComparison_exists` only re-expresses this exact datum
through the opaque system interface, uniquely fixed by HEq to the whole
constructed isomorphism. `pbcRawStageToCompleteComparison_exists` likewise
fixes the whole Mathlib identity-projector comparison, whose components and
inverse have underlying identity arrows. Neither statement selects an
unspecified isomorphism. The same-object normalization equations use HEq where
presentations have propositionally equal endpoints. The primary term is named
`pbcConstructibleCompleteQbarInclusion` in Mathlib's lower-camel convention.

Compilation profiling identified repeated torsion-free instance searches through
flatness. `pbcCompleteCoefficientTorsionFree` directly specializes the existing
`DivisionSemiring.to_moduleIsTorsionFree` instance at the p-adic base field.
It adds no assumption or new mathematical notion and changes no coefficient
structure; it exposes the already inferred proof with higher priority.

## New nodes

New definition node review under §1(A):
`def-sbc-ambient-complete-raw-scalar-system` / `AmbientCompleteRawSystem.lean`
defines the reusable raw ambient coherent scalar diagram before either Karoubi
completion. The original dependency `prop-weil-pbc-scalar-extension` supplies
completed integral ambient tensor and the constructible raw diagram; its existing
`pbcCoherentScalarExtension` signature does not give this ambient raw diagram.
The new node introduces its own prime, closure, independent universes, finite
fields, noetherian finite-dimensional base and stalk invertibility, completed
coefficient ring, complete integral subcategory and raw localization. Its Lean
uses precisely `pbcAmbientCompleteStage`, the actual integral tensor restricted
by `pbcAmbientCompleteTensor_preserves`, the unique localization functor,
identity normalization, uniquely fixed integral/localized unit and balancing
comparisons, and `pbcAmbientCompleteRaw_laws` (additivity, both unit equations,
pentagon). `pbcAmbientCompleteRawSystem` assembles those prescribed transitions
and associators. No boundedness, constructibility, Karoubi projector, pair
category or parent declaration occurs in this prerequisite. Thus it introduces
no dependency cycle and makes no duplicate of the parent's Karoubi notions.
Each postponed theorem has this new node's source/blueprint and proof docstring;
its data choices are unique specifications, not mere existence choices.

I checked the new node against sketch32 1191–1228 and 1291–1338, including the
source's ambient completed tensor and repeated-field normalization. Empty W,
zero objects, repeated fields, and independent coefficient/base universes remain
covered. Its record has exactly §5's new-definition fields, exact cited stmt_deps,
empty proof/proof_deps, null proof_origin/mathlib_match, matching chapter/unit,
master/slopmaster2 audit state none, nearest blueprint ancestor, and via through
the item. The item gains this one stmt_dep and imports this module; the item
statement is unchanged. Each file has exactly one owning node and declarations
are not duplicated.

New-node searches: `blueprint_refs.py search 'ambient complete scalar'` found
zero blueprint nodes; DAG rg found only the parent, the existing integral/raw
constructible scalar-extension proposition and unrelated category interfaces.
LeanSearch “Canonical coherent scalar extension system on rationalized ambient
derived complete sheaf categories over finite p-adic coefficient fields” found
eight ordinary ModuleCat scalar-extension/adjunction/descent or intermediate-field
results. The ordinary module pseudofunctor has different objects. LeanFinder
“Rational localization of derived complete sheaves with normalized finite
coefficient extension and tensor associator pentagon” found eight LightCondensed
monoidal/sheaf-free-presentation declarations. Mathlib grep
`ambient.*(rational|complete).*system|complete.*raw.*transition` had zero hits.
Direct project/upstream rg and the already read PbcScalarExtension and
FiniteStagePairCategory signatures give only integral ambient tensor, raw
constructible systems and generic StageSystem. None is an existing exact raw
ambient coherent diagram. The new node records these three search kinds.

## Dependency modules

`lem-sbc-coherent-pair-functor-descent`: supplied
`Sheaf.CategoryTheory.StageSystemFunctorDescent` as a §1(B) interface repair.
The previously recorded `CommonStage.Diagram`/`PairStructure.Obj` and explicit
quotient are a different carrier from the independently existing upstream
`StageSystem.PairCategory` used by the coefficient nodes. The original module
is publicly imported intact: its complete theorem still supplies all additive
structure, transformation and outer Karoubi clauses. The new module adds the
canonical functor descent interface directly on the existing upstream quotient;
it defines no replacement category. `pairFunctorCoherent` is the node's exact
tower equation; `coefficientPairFunctorObject` keeps the stage and applies the
specified stage functor. `coefficientPairFunctor_exists` fixes the object formula
and every common-stage representative by the node's b-source/map/b-target-inverse
formula. Its proof docstring checks further transport, eventual equality,
composition, identities and uniqueness on quotient representatives. The identity
representative already extends both endpoints along the same repeated-stage
transition, so b and its inverse cancel without an extra unit hypothesis.
The original normalized-unit cases are retained by the parent system/comparison
laws. The bridge covers all independent object/Hom universes, zero arrows,
empty indexing categories, repeated stages and arbitrary projectors.

Second reading of this dependency module against its whole node: all of the
original declarations and their full theorem remain available through the public
import, including canonical additive pair operations, additive descended functors,
compatible natural transformations, identities/composition of families, and
Karoubi extension. The supplemental unique-functor theorem transports the same
specified representative construction to the already used upstream quotient.
No data are chosen from the original bare Nonempty theorem. The new selected
functor is uniquely determined by every object and representative; its existence
has the dependency node's blueprint/source and full proof plan. Only the
existing dependency's lean record changes. No mathematical statement changes.

The parent's `pbcCompletePairInclusion` now applies this generic descent to
`pbcConstructibleCompleteInclusion` and `pbcCompleteInclusionComparison`, using
the already stated comparison tower. `pbcRawPairToComplete` applies the same
construction to identity-projector stage inclusions and their fixed Mathlib
comparisons, with the named `pbcRawPairToComplete_coherent` tower law. These
replace the two redundant concrete unique-functor statements while preserving
the exact object and representative formulas in the dependency interface.

Validation: prescribed `scompile.py NU def-sbc-ambient-complete-coefficient-categories`
compiled all three sibling modules separately in dependency order against the
current overlay. `StageSystemFunctorDescent.lean` compiled in 2.6 seconds,
`AmbientCompleteRawSystem.lean` in 8.5 seconds, and
`AmbientCompleteCoefficientCategories.lean` in 18.8 seconds, with no errors
or disallowed warnings. I checked by eye that section variables and independent
universes are bound, and checked the node lean.statement strings against their
file signatures verbatim. All lines are at most 100 characters; every file has
one owning node and its declarations have that node's source/blueprint.

## Second reading by NU

I independently opened the item node, sketch32 lines 1191--1228, 1291--1345,
and 1412--1438, then checked the complete signatures in all three delivered
modules. The item statement is unchanged and the Lean declaration is
`AlgebraicGeometry.Scheme.pbcConstructibleCompleteQbarInclusion`.

The statement list and verdicts are:

1. The prime, base field, algebraic closure, finite intermediate fields, and
   independent universes render as `l`, `[Fact l.Prime]`, `Padic l`, `Ω`, its
   field/algebra/closure instances, `Padic.FiniteCoefficientFields l Ω`, and
   universes `u v`; this is exact, including the base-field witness.
2. The scheme hypotheses render as `(W : Scheme.{u})`, `[IsNoetherian W]`,
   `[Fact (∃ n, topologicalKrullDim W ≤ n)]`, and
   `[Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]`; no nonemptiness or
   extra constructibility assumption is present.
3. The ambient integral complete stage is
   `pbcAmbientCompleteStage := WeilConjectures.PbcRationalComplete`, and its
   Karoubi category is `pbcAmbientCompleteKaroubiStage`; this is the full
   intrinsically complete category followed by raw central localization and
   Karoubi completion.
4. The constructible stage is
   `pbcConstructibleCompleteStage := PbcRationalConstructible`, with
   `pbcConstructibleCompleteKaroubiStage` its actual Karoubi envelope. The
   published bounded-constructible predicate is reused, with no private copy.
5. `pbcConstructibleCompleteInclusion` is Mathlib's
   `Idempotents.functorExtension₂` applied to the published
   `WeilConjectures.pbcRationalInclusion`; it maps projector objects and
   projector-compatible arrows as required.
6. Ambient transitions use `pbcAmbientCompleteRawTransition` from the raw
   scalar-system module, and constructible transitions use the published
   `pbcScalarExtension`; both are extended by `functorExtension₂` to arbitrary
   projectors. Equal fields use the literal identity branch.
7. The ambient and constructible associators are the specified raw/integral
   associators extended through `functorExtension₂`; the cocycle theorem and
   `pbcCompleteSystem_units` expose the pentagon and both repeated-field unit
   normalizations. These are canonical data, not unconstrained choices.
8. `pbcCompleteRawInclusionComparison` is fixed by its identity integral
   comparison; `pbcCompleteKaroubiInclusionComparison` is its actual Karoubi
   extension, and `pbcCompleteInclusion_coherent` gives the unit and tower
   equations. The comparison orientation is exactly
   `J_E ⋙ T_amb ≅ T_c ⋙ J_F`.
9. `pbcAmbientCompleteQbarCategory` and
   `pbcConstructibleCompleteQbarCategory` are the outer Karoubi envelopes of
   the respective `StageSystem.PairCategory`s. Their objects therefore retain
   both the finite-stage projector and the outer projector; common-stage
   transport, eventual equality, identity, addition, and composition come from
   the existing pair-category implementation.
10. `pbcCompletePairInclusion` is the generic
    `StageSystem.coefficientPairFunctor` with the representative formula
    `b_source ≫ J_M.map f ≫ b_target⁻¹`; its outer extension is the primary
    `pbcConstructibleCompleteQbarInclusion`. Neither projector is replaced by
    an identity.
11. `pbcRawAmbientStageToComplete` and
    `pbcRawConstructibleStageToComplete` are the identity-projector embeddings.
    `pbcRawPairToComplete` and `pbcRawQbarToComplete` give the raw Qbar map into
    the nested constructible category, preserving the raw object and arrow
    formulas. No raw/Karoubi equivalence is asserted.

The edge cases are covered: an empty scheme is allowed; zero objects, zero and
nonidentity inner and outer projectors, zero arrows, equal and repeated fields,
the base field as a common stage, and empty common-stage representative sets
are all retained. No residue-characteristic restriction, ambient
constructibility bound, or equality of the independent scheme and closure
universes is introduced. The coefficient `Shrink` transport preserves the
small coefficient universe without identifying it with `Ω`.

I searched Mathlib, the upstream `WeilConjectures` tree, this repository's
`lean/Sheaf`, and the stage-system sources using LeanFinder, LeanSearch,
Loogle, `rg`, and `grep`. The results were only generic Karoubi, localization,
module, and pair-category ingredients; no exact ambient complete coefficient
system or nested common-stage inclusion exists. I also checked the new
raw-system node against sketch32 and its three recorded search kinds; it is the
missing ambient raw diagram and does not duplicate the parent. The dependency
repair was checked against its full node: the imported `CommonStage` interface
remains available, while `StageSystemFunctorDescent` supplies the same
canonical representative formula on the already-used upstream
`StageSystem.PairCategory` carrier.

No mismatch was found, so no Lean or node statement was changed. The three
files were compiled separately in dependency order with the prescribed
`scompile.py`; all completed without errors or disallowed warnings, and every
`lean.statement` was checked verbatim against its declaration signature.
