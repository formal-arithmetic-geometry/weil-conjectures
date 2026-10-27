## Worker report

The item is stated by `WeilConjectures.NativeBidualRealization.bidual_evaluation_realization`
in `Sheaf.WeilSheaf.NativeBidualEvaluationRealization`. Both delivered theorem proofs are `sorry`; the comparison-data module contains
only real definitions and inherited structure-property instances. The natural-language
statement is unchanged. The comparison constructions now belong to the new definition node
`def-sf-weil-dual-realization-comparison-data`, the sole addition to stmt_deps.
`lem-sf-weil-dual-realization-comparison` remains only in proof_deps; neither its
node record nor a module for its theorem is delivered. The base shared node files
and recorded upstream sources were reread; delivery2 rebases the packet onto
current main without direct Git mutation.

Clause-by-clause correspondence:

- The finite field, its arbitrary fixed closure, and the coefficient prime are
  `D : FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]`.
  `Space D` packages exactly a separated finite-type model over `D.k₀`; its
  `LocallyOfFiniteType` and `QuasiCompact` fields together mean finite type.
  `geometric D X` is the actual geometric fiber over the specified `D.k`.
- `R : AdicQbarRealization.Family l D` is the evaluation-normalized coefficient
  realization supplied by the recorded realization theorem. Its target modules
  are section modules over the native finite-extension-valued continuous-function
  sheaf. The fixed coefficient closure is the framework's `PadicAlgCl l`.
  Neither constant discrete coefficients nor all continuous functions into the
  topological closure replace this sheaf.
- `NativeExceptionalForgetful.W D l X` is definitionally `WeilComplex D.k₀ l X.base.left`,
  the full bounded constructible subcategory of `DerivedCategory (ProEtaleWeilSheaf ...)`.
  No Frobenius fixed-pair category in the ordinary derived category is substituted.
  All morphisms are the actual native derived morphisms.
- `A : NativeDualRealization.Datum D l R X` bundles the choices already fixed in
  the statement: the exceptional comparison package, the structural exceptional
  system and compactification, the specified native right adjoint and its
  adjunction, and the normalized native closed comparison. Its right adjoint
  is adjoint to the existing `nativeShriek`, hence to the actual
  `WeilComplex.derivedLowerShriek`. No existence or reflexivity of another
  right adjoint is postulated.
- `nativeOmega` is `A.right.obj (constant D l (point D))`. The constant is the
  existing coefficient Weil sheaf in degree zero, with its canonical Frobenius.
  `commonOmega` is the exceptional system's actual structural exceptional image
  of `geometricPointOmega` at literal `Spec D.k`.
- `nativeHom` is the first-variable functor of
  `A.closed.native.homModels.weilHom` into nativeOmega. Its `nativeModel` isomorphism
  identifies this exact functor with the recorded `ProEtaleWeilSheaf.derivedHom`.
  The retained native Hom representatives use product-total internal Hom into
  K-injective targets. The model is not arbitrary object or map data.
- `model` and `counit` are the fixed inverse-realization model `M_K` and its
  natural counit `j_K` from `A.exceptional.model X`.
  This retains all the fixed inverse-equivalence identifications: a fully faithful
  realization determines each common-stage arrow uniquely by its realized arrow.
- `dualizingComparison` is `Package.actualSpecialization` for this same native
  right adjoint and ordinary structural exceptional system. It is the dependency's
  structural comparison `h` at the specified adjoint.
- `Permitted` is not assumed in the item: the conclusion starts
  `∃ hp : Permitted D l R X A`. This is the permittedness supplied mathematically
  by thm-coef-qbar-verdier. `commonDual ... hp` is the existing common-stage
  Hom functor into commonOmega, restricted by those permitted pairs. It applies
  to every common-stage object, including its first and second duals.
- `comparison` in the new definition module is literally the required composite:
  transported native forgetful Hom comparison, ambient Hom map induced by
  `(counit K).hom` contravariantly and `dualizingComparison.hom` covariantly,
  and the inverse `realizationHomIso`. The latter is the existing
  evaluation-transpose `homComparison`, made into an isomorphism with its
  recorded invertibility proof. The entire composite c_K is directly an Iso:
  `asIso` uses `A.closed.hom_isIso`; `ambientHom.mapIso` applies to the product
  of j_K.op and h; the final factor is `realizationHomIso.symm`. No theorem
  supplying IsIso c_K, and no `.choose` from that theorem, is used. The item does not hypothesize arbitrary c maps.
- `h : Closed ...` is exactly the stated closure hypothesis for native Hom into
  omega. `dualX ... h` is its real full-subcategory restriction. This closure
  predicate is on the recorded two-variable Hom model, identified by nativeModel
  with the statement's native derivedHom; transport across that specified natural
  isomorphism gives the identical closure condition and restricted functor.
- `firstDualIso ... hp` is the unique full-faithful preimage of `j_(D_X K)` followed by
  `c_K`. Consequently it is precisely the statement's inverse-equivalence unit
  transport t_K, including its orientation. `secondComparison ... hp` is
  `c_(D_X K)` followed by `rho.mapIso (D_Y.mapIso t_K.symm.op)`, exactly b_K.
- After permittedness, the existential `delta : 𝟭 W ⟶ dualX.rightOp ⋙ dualX` supplies the natural
  transformation, with naturality over every native derived arrow built into
  its type. Its first clause fixes its component to the existing `nativeBidual`.
  The second clause is the displayed characterization by evaluation, with the
  actual signed `weilSymmetry.braiding K (D_X K)` on the right-hand side.
- `commonBidual` is the same transpose in the common-stage category:
  `podCommonClosed.transpose` applied to `pullbackTensorCommonBraiding` followed
  by `podCommonClosed.evaluation`. It is an actual arrow rather than a freely
  chosen or per-degree biduality map.
- The third clause is exactly the requested equality, in Lean's composition
  order: `j_K.hom ≫ U.map (delta.app K) ≫ b_K.hom = rho.map (commonBidual M_K)`.
  These are arrows in the full ordinary module-derived category.
- The fourth clause states naturality of b explicitly. Together with naturality
  of j and delta, it makes the displayed component equalities a natural equality.
  There is no IsIso assertion for delta, no inverse delta, and no assumption of
  faithfulness of derived forgetting.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`;
  the native category uses the existing geometric Galois Frobenius over the
  library closure, transported by `NativeExceptionalForgetful.closureMap`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`; `Sheaf.Paper.CompletedCondensedCoefficients`:
  `AlgebraicGeometry.ProEtale.completedCondensedIntegral` and coefficient construction.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `CategoryTheory.Endofunctor.IsoAlgebra`; Mathlib's `DerivedCategory` and
  `CochainComplex.IsKInjective`. The actual native derived category uses these
  notions via the upstream `WeilConjectures.WeilSheaf.Category` and `DerivedHom`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport`, the finite compact-support node's recorded
  construction; the native operation is the already-existing
  `WeilComplex.derivedLowerShriek` (LowerShriek), as the item's statement specifies.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, raw
  localization with no completion; `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedInternalHom`,
  `commonStageHomPairs`, `commonStageDerivedTensor`; `Sheaf.SixFunctors.CoefQbarVerdier`:
  `CoefQbarVerdier.homDual`, `coef_qbar_verdier` (proof prerequisite).
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`; its actual structural G defines omega_Y.
- `Sheaf.Paper.AdicQbarConstructibleRealization`: `adic_qbar_constructible_realization`
  and the re-exported `AdicQbarRealization.Family`; `NativeAdicRealizationData`:
  `ordinary`, `ambientHom`, `homComparison`, `HomLaws` and its transpose normalization.
- `Sheaf.Paper.NativeWeilClosedForgetful`: `native_closed_forgetful`,
  `NativeClosedComparison`, `nativeBidual`; its retained model data specify the
  native Hom and signed tensor structure.
- `Sheaf.WeilSheaf.NativeExceptionalForgetful`: `Package`, `U`, `W`, `Space`,
  `StructuralSystem`, `actualSpecialization`, and the recorded
  `native_exceptional_forgetful` existence theorem.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.ringedDerived_closed_symmetric_monoidal` (ambient transpose
  injectivity in the proof plan).

Edge cases checked before writing: K=0 and empty X require no nonzero or nonempty
assumption. At a geometric point in degree zero the arrows reduce to ordinary
bidual evaluation. Odd cohomological shifts retain the Koszul symmetry in both
nativeBidual and commonBidual, so a sign is not silently omitted. The arbitrary
fixed algebraic closure is transported along closureMap; no k-linearity of
Frobenius is assumed. A nonsplit native Frobenius extension remains a genuine
morphism because every functor and naturality quantifier uses the native
localization. The source has Hom universe u+1 and the section-module target u+2;
the new comparison helpers bind those universes independently instead of
identifying them.

Searches (2026-10-25):

- msearch leanfinder, "Weil derived double dual evaluation transpose compatible
  with forgetful functor and coefficient realization": eight finite-module or
  Module.Dual results, no match.
- msearch loogle, `"nativeBidual"`: zero hits.
- msearch leansearch, "Symmetric monoidal functor preserving internal Hom preserves
  the canonical double dual evaluation transpose": eight hits including
  `CategoryTheory.ihom.ev`, `rightAdjointMate` and rigid-category tensor/Hom
  identities, none with the native/common-stage comparison objects or normalizations.
- msearch grep, `bidual|doubleDual|evaluation.*[Tt]ranspose` in CategoryTheory:
  zero hits.
- rg of the same pattern in lean/WeilConjectures and lean/Sheaf, and the item ID
  in lean/WeilConjectures: nativeBidual and the ambient forgetful compatibility
  exist, as do abstract Verdier biduality and other module-duality results.
  None states the required coefficient-realization equality with j,c,b,h.
  The upstream biduality isomorphism theorem asserts a different result.
- `scompile.py --source Sheaf.WeilSheaf.NativeDualRealizationComparison` confirmed
  that guessed module was unavailable; the DAG prerequisite also had no lean
  record, so the first packet supplied it. H2 repair removes that theorem delivery and
  supplies only the requested definition owner.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md`, particularly
"Naturality of evaluation proves its equivariance, and transposition gives the
same conclusion for delta" and the scalar-tensor/dualizing-counit/evaluation
paragraph. The six-step DAG refinement is included in the item docstring.
No statement correction or mathematical dispute is required.

## Dependency modules

`lem-sf-weil-native-closed-forgetful`: the new module
`NativeSectionClosedForgetful` imports and preserves the existing
`NativeWeilClosedForgetful` interface. It adds its transport to the specified
algebraic closure and section-module presentation, retaining the original native
closed comparison and all its representative normalization. The original
`nativeHomComparison` and symmetry compatibility require equal source/target
category universes, which do not hold for internal modules versus section modules.
`sectionHomComparison` and `SectionSymmetryCompatibility` generalize those
formulas literally to independent universes. The only new postponed theorem is
`native_section_closed_forgetful`, whose proof plan transports K-flat totals,
K-injective Hom and evaluation through the two exact equivalences. Together
with the imported original theorem it renders all clauses of the dependency node.
Only this dependency node's lean record is repaired.

## New nodes

`def-sf-weil-dual-realization-comparison-data` owns `Datum`, the actual omega_X,
omega_Y, M,j,h, native Hom and permittedness predicate, common-stage dual, Hom
pairs, realization comparison, c_K and both evaluations. Its module is
`Sheaf.WeilSheaf.NativeDualRealizationComparisonData`; it asserts no permittedness,
closure or comparison theorem. c_K is the direct composite Iso of the three
specified invertible factors, with no additional postponed theorem. The node
statement cites exactly its prerequisite notions, retains arbitrary algebraic
closure and independent source/target category universes, and has no proof steps.
Source: current blueprint cor-coef-verdier-weil-equivariance, first-map paragraph
and final coefficient-descent paragraph, as fixed in the item. The new definition
is an owner for that specified construction, not a new form of internal Hom.
`blueprint_refs.py search 'dual realization comparison'` returned zero nodes;
`ancestor` returned None, as for the existing item's native-derived provenance.
DAG grep for a dual comparison-data owner found none. Source rg for
`NativeDualRealization|nativeHomComparison` found NativeWeilClosedForgetful and
ConstructibleInternalHomContinuity, neither this composite or its datum.
Logged msearch: leansearch query `native Weil dual realization comparison data
with fixed exceptional adjunction and coefficient realization` returned eight
module-dual, root-pairing and comonad comparison hits; no exact match. Loogle
`"nativeHomComparison"` and Mathlib CategoryTheory grep
`NativeDualRealization|nativeHomComparison` returned zero hits. The three actual
logged searches are recorded in the new node with their original queries.

## Returned delivery repaired

H2: removed the theorem node from the item's stmt_deps, retained it in proof_deps,
and removed its node/module from the packet. Moved every comparison notion to
the new definition-node module. The new node is the only stmt_deps addition.
Changed c_K from an arrow with theorem-chosen invertibility to the literal
composite Iso using the existing `hom_isIso`, Hom mapIso, and realizationHomIso.
Removed the theorem-chosen permittedness definition. The item now concludes
`∃ hp : Permitted, ∃ delta, ...`, so it does not silently assume the Verdier
permittedness assertion or take it from an unrelated statement dependency.

H13: `Comparison.tensor_transport` pins every component to the image of
`native.tensorComparison` followed by `transportTensor`. `TransportNormalized`
pins that transport to the actual ordinary K-flat representative maps. It requires
preservation of K-flatness, the pure-section identity x tensor y ↦ x tensor y in
every summand of total degree p+q, and a localization square against the recorded
ordinary tensor model and the realization's section tensor model. The localization
factor is fixed by the actual right-derived unit and section localization factor,
not free data. `SectionTensorCoherence` supplies associator and both unit equations;
`SectionSymmetryCompatibility` retains the signed braiding. The imported
`AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful` remains explicitly in
the dependency's lean.declarations alongside native_section_closed_forgetful.
Thus the Nonempty theorem now asserts the canonical normalized transport, not
existence of an unpinned natural tensor iso. Zero objects, empty sites and odd shifts
still satisfy the same pure-summand and signed equations; no universe equality
was introduced.

## Second reading by Q05

This is a second pass by the same worker; no independent agent was started, in
accordance with the dispatcher's explicit instruction. The maintainer's independent
review remains required. I reread the complete statement beside the three repaired modules and the new
node. The additional quantified hp is in the conclusion; helper definitions are
parameterized by hp, while native closure remains the original sole hypothesis.
The comparison-data module contains no theorem and no choice from the removed
dual-realization theorem. The original native closed theorem is retained in the
record. I checked tensor_transport's direction: transport of native tensor first,
then ordinary-to-section tensor, hence exactly the tensor used in the Hom transpose.
The representative equation has Q,P in the target tensor, because the curried
ordinaryTensorBifunctor convention gives Q tensor P on inputs P,Q. Its generator
formula has x in Q^q, y in P^p and total degree p+q; the target generator is indexed
q,p with q+p=n. Both unit equations use the same transported unit. This fixes the
rescaling freedom identified by the reviewer. The native delta and commonBidual
clauses remain unchanged apart from the explicit hp argument.
The inverse first-dual orientation was checked: t has source M_(D_X K) and target
D_Y M_K, so D_Y(t inverse) goes from D_Y M_(D_X K) to D_Y D_Y M_K. I checked j's
orientation in both c and the final equality. Both transposes use Hom-first
uncurrying and the explicit signed symmetry. No invertibility of delta is present.
The comparison model preserves native extension morphisms. During compilation,
I repaired missing realization invertibility witnesses, bound source/target
universes independently, and supplied the structure map's scheme-property
instances. These are elaboration/interface repairs, with no change to hypotheses
or conclusions of the mathematical statement.

Validation after repair: the three modules compiled through scompile.py in
dependency order. The only remaining unused-variable warning was removed by
renaming the intentionally proof-only Q-flatness binder before the final checks.
