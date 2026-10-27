## Worker report

The module `Sheaf.Paper.FiniteStageSupportedGeneration` states
`AlgebraicGeometry.ProEtale.FiniteStageGeneration.finite_stage_supported_generation`.
Its only postponed proof is this named theorem, whose docstring gives the nine
steps of the accepted DAG proof. All auxiliary definitions have real bodies;
`Comparisons` is comparison data asserted to exist by the theorem, not assumed.
The current H4/H12 repair retains the coefficient-inclusion ownership node and uses the landed section-comparison ownership node. No Lean declaration, dependency module, or mathematical statement correction is needed. The earlier H2 repair history below is superseded where indicated.

Clause-by-clause rendering:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The base is `(k : Type u) [Field k]`,
  `[CharP k p]`, `hp : 0 < p`, and `hpℓ : p ≠ ℓ`. Finite type and separatedness
  are `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`
  for `X : Over (Spec (.of k))`. No characteristic-zero or connectedness assumption
  enters. CharP of a field and positive p supplies primality when needed downstream.
- The algebraic closure with extended norm is the existing `PadicAlgCl ℓ`.
  `Profinite.padicAlgClRingObj ℓ` is C, the finite-subextension-valued sheaf,
  not the sheaf of all continuous functions.
  `Profinite.continuousMapRingObj (PadicAlgCl ℓ)` is B.
  `Profinite.continuousMapRingObj E` is A_E, with
  `E : PadicAlgCl.FiniteIntermediateField ℓ`. The maps are the existing
  `Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E`,
  `NormAlgclComparison.coefficientInclusion ℓ`, and their actual composite.
- `QuotientChange.Modules R T` unfolds to `Mod` of abelian sheaves on T's
  small pro-etale site over `condensedRingObj R T`, the pullback of R from the
  point. All categories are ordinary unbounded `DerivedCategory`, without completion.
  The sheaf and module universes are the existing `Ab.{u+1}` convention over
  `Scheme.{u}`; no extra universe equality is imposed.
- Constructibility is exactly `constantModelBoundedConstructible`, from the
  recorded finite constant scalar-model definition. In particular it does not
  substitute the upstream arbitrary finite-presentation predicate.
  `IsLisseCoefficientModule` is the recorded finite-free pro-etale local predicate.
- `support R j i` is termwise exact open extension by zero followed by the
  actual total right derived closed pushforward. The two `closed_exact` fields
  of `Comparisons` assert closed exactness under the theorem's scheme assumptions,
  so this is the derived extension of the specified ordinary i_* j_!.
- `QuotientChange.D φ T` is the existing total left derived ordinary extension.
  `ScalarAssertions` asserts invertibility of the universal `compute` map for
  every K-flat representative, for all three coefficient maps and every T.
  Its `ExactScalarUnit` existential gives a shift structure with triangulated D,
  triangulated exact termwise restriction V, and shift-compatible scalar unit
  and computation counit. `V₀` is asserted to preserve finite limits and colimits.
  `scalarAdj` is the existing adjunction to V. The representative unit equation
  equates its image under `compute` with the localized ordinary extension/restriction
  unit, which sends v to 1 tensor v, not an arbitrary unit.
- `SectionAgreement` asserts existence of the section localizations and the
  existing `SectionScalarComparison` satisfying `SectionScalarNormalized`.
  These encode the actual section extension, restriction and derived comparison,
  including balanced generators and the K-flat computation equation. Section
  localizations are conclusions, not new assumptions on coefficients or schemes.
- `Comparisons.supported` is a natural isomorphism of R'_X-module-valued functors
  `support R j i ⋙ D φ X ≅ D φ S ⋙ support R' j i` for every open-then-closed
  factorization into X. Thus it states the claimed linear comparison for every K
  in the entire unbounded category, not just on cohomology or lisse objects.
- `singleComparison` is the actual universal computation map followed by the
  canonical single-complex comparison. The last clause of `ScalarAssertions`
  makes it invertible for every lisse M and asserts ordinary extension is lisse.
  It therefore gives the required degree-zero formula.
- `Comparisons.pull` and `pull_normalized` use the recorded `PullNormalized`
  representative equation for inverse image along every scheme morphism.
  `TowerCompatible` supplies the same family of scalar transitivity isomorphisms
  normalized by `SuccessiveNormalized` and the composite scalar units. Its next
  equations state compatibility with those pullback comparisons, those support
  comparisons, and the specified lisse degree-zero map. The tower's ordinary
  contraction is the recorded `ordinaryComp`, not an unconstrained isomorphism.
- `generator ℓ j i E M` is exactly a_!(C tensor^L_A_E M[0]). `IsGenerator`
  quantifies every S,Z,j,i,E,M with open j, closed i, constructible composite
  image, lisse input and an isomorphism to that specified generator. This is
  its replete class; it imposes no positive rank or nonempty-support condition.
- `GenerationAssertions` asserts that Dbc(X,C) is replete and triangulated,
  contains all generators, and is contained in every replete triangulated object
  property containing them. Since its morphisms are those of the ambient derived
  category, these are exactly the smallest full replete triangulated subcategory
  clauses, using `ObjectProperty.IsTriangulated` from Mathlib.
- Its final equivalence with `FiniteConstruction` records an actual finite
  list `F : Fin (N+1) → D(C_X)` ending at K up to isomorphism. Each entry is
  zero, a generator, a shift of a strictly earlier entry, or the middle of a
  distinguished triangle with both ends strictly earlier. The initial zero
  case permits constructions with no nonzero generators; no infinite coproduct,
  infinite extension, or retract closure is inserted.
- The theorem's last clause is an isomorphism in D(B_X) from the specified
  J_X(generator) to the degree-zero ordinary i_* j_! of the ordinary A_E-to-B
  extension of M. It uses the actual composite inclusion. This is precisely
  the displayed generator formula with its [0] convention.
- The first two conjuncts assert `IsNoetherian X.left` and, for every immersion
  `a : S ⟶ X.left`, `IsNoetherian S`, `LocallyOfFiniteType (a ≫ X.hom)`,
  `QuasiCompact (a ≫ X.hom)` and `IsSeparated (a ≫ X.hom)`, without requiring
  a reduced or a canonical subscheme structure on S.

Recorded statement dependency declarations read and used:

| Node | Module and declaration |
| --- | --- |
| sk-def-sfb-dc-setting | WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible; explicit Over/finite-type/separated binders follow its setting; its compactification choice is not used by this lemma |
| sk-def-sfb-qlbar-condensed | WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic; Profinite.padicAlgClRingObj and padicAlgClCondensedRing |
| def-sfb-continuous-map-condensed-ring | Sheaf.Topology.ContinuousMapCondensedRing; Profinite.continuousMapRingObjOfUniverse, specializing definitionally to the published continuousMapRingObj at coefficient universe zero |
| sk-def-sfb-pulled-back-coefficients | WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic; coefficientRing, condensedRingObj |
| sk-def-sfb-module-objects | Mathlib.CategoryTheory.Monoidal.Mod; CategoryTheory.Mod |
| sk-def-sfb-derived-categories | Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions; total derivation convention, with DerivedCategory and published rightDerivedFunctor on these Grothendieck module categories |
| sk-def-sfb-constructible | Sheaf.Paper.CondensedConstantConstructibility; constantModelBoundedConstructible |
| sk-def-sfb-derived-extension-of-scalars | WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars; Mod.derivedExtendMapDerivedCategoryAdjunction and universal K-flat computation |
| def-sfb-lisse-coefficient-module | Sheaf.Paper.CoefficientHeartStratificationDefs; IsLisseCoefficientModule |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion; IsOpenImmersion |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion; IsClosedImmersion; IsImmersion for the final geometric clause |
| def-sfb-module-open-lower-shriek | WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs; CondensedRing.openImmersionLowerShriek and its exactness instances |
| def-sfb-module-lower-star | WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs; CondensedRing.lowerStar |
| def-weil-triangulated-subcategory | Mathlib.CategoryTheory.Triangulated.Subcategory; ObjectProperty.IsTriangulated (mathlib_match, no lean record required) |

The added statement dependencies now cite definition owners exclusively:
`def-sfb-norm-algcl-coefficient-inclusion` owns the three existing coefficient
inclusion declarations in `Sheaf.Paper.NormAlgclCohomologyTopologyComparison`;
`def-sfb-internal-section-scalar-pullback-comparison-data` owns the existing `SectionScalarComparison`
and `SectionScalarNormalized` in `Sheaf.Paper.InternalScalarPullbackNormalization`;
`def-sfb-internal-derived-scalar-comparisons` remains the landed owner of Modules,
D, V, scalarAdj, compute, PullNormalized, ordinaryComp and SuccessiveNormalized.
The conclusions of the two surrounding theorem nodes are not used or cited as
statement dependencies. No definition is reimplemented.
All recorded proof-dependency modules are imported, with plain imports for proof-only
ones and public imports where definitions enter the statement. Mathlib proof leaves
are imported via Adjunction.Mates, Adjunction.Unique, FiniteType, Proper,
Noetherian, RingTheory.FiniteType and Spectrum.Prime.Noetherian.

Edge cases checked before finalizing: empty X and empty locally closed S are never
excluded; the finite construction can consist of zero alone (N=0); ranks zero are
allowed by the recorded lisse predicate and no positivity assumption is introduced.
Shifts are arbitrary integers, K-flat representatives and supported complexes are
unbounded, finite fields include Q_ell itself, and the geometric clause allows
arbitrary subscheme structures. No coefficient inclusion is assumed flat. The base
universe is arbitrary. Choosing the standard algebraic closure with its extended norm
uses the library's existing coefficient presentation, as in every dependency.

Searches: the sandbox searches.jsonl records the original msearch results verbatim.
`grep` query `triangulatedClosure|finiteStageSupported|derivedExtendScalars` in
Mathlib CategoryTheory returned zero hits; Loogle query
`ObjectProperty.triangulatedClosure, Functor.leftDerivedFunctor` returned no hits
(the former identifier is absent); LeanFinder query `Derived scalar extension commutes
with locally closed extension by zero and finite field lisse generators generate bounded
constructible derived category` returned only unrelated solid/finite-type sheaf results;
LeanSearch query `derived extension of scalars triangulated category sheaf generators`
returned ordinary sheaf generators and the ambient derived triangulated instance.
Direct rg searches for FiniteStageGeneration, finite_stage_supported_generation,
FiniteConstruction and the item id in WeilConjectures and Sheaf found no declaration
of this statement. The nearby continuousQbar_constructible_generators theorem uses
B and arbitrary B-lisse generators, with no finite coefficient stage and none of these
scalar comparisons; its finite-construction predicate is specialized to that different
coefficient ring and generator class. RationalRealizationFiniteConeModels is specialized
to integral coefficient objects. BoundedFiniteModelGeneration's generic finite-building
helpers are private. Thus none supplies this node's finite-stage predicate or theorem.

No STATEMENT-DISPUTED finding or source correction. The original source paragraph (3)
and the extracted nine-step DAG proof were read; all nine steps are in the theorem
docstring. The source's missing exact norm-topology reference is an inherited literature
tracking note, not an omitted hypothesis.

Validation: scompile.py compiled the draft cleanly in both sandbox and library modes;
the final module is recompiled by the required delivery dry run.

## Second reading by NN

This dispatched worker was instructed not to start other agents. I performed a second
clause-by-clause reading of the node and finished file; the maintainer's independent
review remains the external reading. I checked in particular that C and B remain
separate, that the last isomorphism lands in D(B_X), that supported comparisons are
natural isomorphisms for all unbounded inputs, that the finite construction has strictly
earlier ends, and that Noetherian/finite-type/separatedness are conclusions for S.
The reread found one missing explicit proof import (InternalSectionScalarAdjunction),
which was added; the clause mapping above records every binder and conclusion.
No mathematical statement or dependency declaration was changed.

## New nodes

- `def-sfb-norm-algcl-coefficient-inclusion`: `existing: true` on the unchanged
  `Sheaf.Paper.NormAlgclCohomologyTopologyComparison` module. Its main declaration
  is `AlgebraicGeometry.ProEtale.NormAlgclComparison.coefficientInclusionRing`;
  its declaration list also records `coefficientInclusion` and
  `coefficientInclusion_isMonHom`. The prime binder and arbitrary profinite
  universe come from the source section. C is exactly the finite-subextension
  subring sheaf, B the all-continuous sheaf, the ring map is the ULift-conjugated
  subring inclusion, and its image under sheafCompose gives the underlying
  ring-object map with the existing IsMonHom instance. The three definition
  dependencies own C, B and ring objects. This node makes no cohomology assertion.

The retained new node follows paragraph (3) of the current direct-image proof,
where these coefficient changes enter finite-stage generation. The blueprint
ancestor command returns None for this extracted item; the new node preserves
that ancestor and prepends this item to its via. The section interface is now
owned by the already-landed node, not a new node in this delivery.

Search audit: searches.jsonl records both new LeanSearch and LeanFinder queries
and the Mathlib grep verbatim. The inclusion query returned eight general
continuous-function results in each service, without this coefficient inclusion.
The section-comparison query returned eight ordinary module/sheaf results in each
service, without this normalized interface. Mathlib grep
`coefficientInclusionRing|coefficientInclusion_isMonHom|SectionScalarComparison|SectionScalarNormalized`
returned zero hits. At the original H2 repair, direct rg of DAG, WeilConjectures and Sheaf found
the published helper declarations and the surrounding theorem records. The
subsequently landed section-comparison owner is reused in this repair. Blueprint searches `coefficient inclusion`
and `scalar comparison` returned two and three unrelated nodes respectively.
The retained coefficient-inclusion node is an existing-declaration ownership
node with no new module; the duplicate section-comparison node has been removed.

New-node edge checks: inclusion is defined on the empty profinite set and includes
constant functions without a nonempty-domain condition; no finite-image condition
replaces the finite-subextension condition. Section comparison permits a=id,
empty schemes, zero modules and unbounded complexes; it assumes neither flatness
of a nor boundedness of the inputs. Its normalization is a Prop on given data,
not a choice of data from a postponed existence theorem.

## Repair of immutable head e55b77c4d6c4

H2: removed `lem-sfb-norm-algcl-cohomology-topology-comparison` and
`lem-sfb-internal-scalar-pullback-normalization` from the saved packet's added
statement dependencies. They were used solely to obtain plain definitions.
Added the two definition-owner nodes above and cited them instead; retained
`def-sfb-internal-derived-scalar-comparisons`. Compared the saved node against
current main without Git commands: before this repair only lean and stmt_deps
differed. Current-main item fields other than these two remain identical.
The accepted Lean is retained byte-for-byte, SHA-256
`986dbeed080bf6552ea07f476067cab74694e2c1df0d5f6bb8e502ea09e103af`.
The initial saved-packet dry run passed preflight and both sandbox and library
compilation (dry-run commit 1fd8b54feb4). The repaired packet passed scompile.py cleanly (sandbox 19.1 s; library 13.0 s)
and the required deliver2.py --no-push run passed server preflight and compilation
with dry-run commit 2245b9f2544. The push wrapper repeats its required checks.

## Second reading by NN (repair)

Read both full existing definitions and their section binders again, alongside
the new node statements and the consumer's SectionAgreement and theorem signature.
Checked that coefficientInclusionRing is the literal sectionwise inclusion, that
coefficientInclusion is its underlying ring-object map and that the instance is
only its multiplicative compatibility, with no cohomology theorem used. For the
section data, matched all four structure fields and each of the three predicate
clauses, including the K-flat and termwise-flat hypotheses, balanced sheafification
generators and order of the computation/localization factors. Checked the new
node's own dependency owners for each such construction. The return has one
numbered defect, H2, and the replacement definition owners repair it completely;
the Lean, all hypotheses, all conclusions and the earlier mathematical self-check
are unchanged. No STATEMENT-DISPUTED finding or statement correction.

## Repair of immutable head 60bdbbf705fe

H4/H12: deleted the new `def-sfb-section-scalar-comparison-data` node. Replaced
its entry in the item's `stmt_deps` with the landed
`def-sfb-internal-section-scalar-pullback-comparison-data`, as the return
explicitly requires. That Q96 node (PASS cb908946e, 2026-10-22) owns
`SectionScalarComparison` with the identical `lean.statement`, and also owns
`SectionScalarNormalized` in `Sheaf.Paper.InternalScalarPullbackNormalization`.
Read the landed node and the full structure and predicate with their section
binders: the four comparison fields and all three normalization clauses are
the same definitions already used by `SectionAgreement`. No duplicate node is
needed. `def-sfb-norm-algcl-coefficient-inclusion` is retained unchanged, as are
`def-sfb-internal-derived-scalar-comparisons` and the accepted Lean source.
This section supersedes the earlier repair history's references to two new nodes.

Compared the saved packet with current main using JSON parsing without Git
commands: the item differs only in `stmt_deps` and `lean`; all other node fields
are identical. The prescribed delivery wrapper refreshes and rebases onto the
live `sheaf-dag` branch. No direct Git command or live-source edit was used.
The accepted module's SHA-256 remains
`986dbeed080bf6552ea07f476067cab74694e2c1df0d5f6bb8e502ea09e103af`.
The initial saved-packet dry run passed (dc1813edcd4); the ownership repair is
still necessary despite that mechanical pass.

## Second reading by NN (H4/H12 repair)

Re-read the landed owner's `lean` record against the actual source declarations
and the consumer's `SectionAgreement`. The replacement owns both used names
and preserves their exact types, universes and normalization conditions. Checked
that the duplicate file is absent, the item cites the landed owner once, the
coefficient-inclusion node is unchanged, and no mathematical statement, proof
plan, or Lean bytes have changed. The return's advisory that the supported-tower
clause is vacuous because c is existential is recorded; the return explicitly
requires Lean unchanged and accepts the substantive statement review. No new
STATEMENT-DISPUTED finding or statement correction is made in this ownership repair.

Validation for H4/H12: the unchanged delivered module passed the required
`scompile.py` in both sandbox (9.5 s) and library (8.4 s) modes, without errors
or warnings. The signature was re-extracted and checked byte-for-byte against
`lean.statement`; all current statement dependencies resolve to DAG node files.
