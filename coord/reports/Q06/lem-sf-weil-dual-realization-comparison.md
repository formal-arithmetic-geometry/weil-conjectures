## Worker report

The new module `Sheaf.WeilSheaf.DualRealizationComparison` states
`WeilConjectures.NativeDualRealization.dual_realization_comparison`.
It compares actual native derived internal Hom into the specified native exceptional
image of the constant with the recorded coefficient-passage Hom, naturally and with
the specified evaluation square. Only this theorem has `sorry`; no data is chosen
from its proof. The item node is changed only in `lean`. There are no new DAG nodes
or dependency-record repairs.

### Hypotheses and objects

- The finite field, its prime characteristic, and the arbitrary algebraic closure
  are `D : FiniteFieldDatum.{u}`. The prime is `l` with `[Fact l.Prime]` and
  `[Fact (l ≠ D.p)]`. `NativeExceptionalForgetful.coefficientCharacteristic`
  supplies the existing native library's `ringChar D.k₀ ≠ l` instance. The
  coefficient closure is the recorded native ring's `PadicAlgCl l`, exactly as in
  both comparison dependencies; no discrete coefficient ring is substituted.
- `X : NativeExceptionalForgetful.Space D` bundles an object over `Spec D.k₀`
  with separated, locally finite type and quasi-compact structural morphism.
  `geometric D X` is the specified base change to D.k. The native library uses
  its chosen algebraic closure. `transport` retains the dependency's actual
  `closureMap`, followed by `sectionDerived`, so the arbitrary closure in D is
  retained without identifying its universe or its carrier with the library's.
- The finite-extension-valued coefficient ring and ordinary module category are
  those of `R : AdicQbarRealization.Family l D`; `modules`, `ambientHom`,
  `ordinary`, `sectionDerived` and `boundedConstructible` are reused. Their small
  pro-etale site has object universe u+1, morphism universe u and coefficient
  universe u+1. No equality of site universes is imposed.
- `W D l X` is exactly `AlgebraicGeometry.WeilComplex D.k₀ l X.base.left`.
  Its objects lie in D of the abelian fixed-pair category. Its morphisms are all
  native derived morphisms, not morphisms of fixed pairs in an ordinary derived
  category. `forget` is ambient termwise native forgetting followed by the same
  closure and section presentation as the existing restricted functor `U`.
- `structureArrow D X` is the actual structure morphism into `point D`. The
  three property instances are the model's existing separatedness and finite
  type; they add no assumptions. `G` and `adj : nativeShriek ... ⊣ G` specify
  any right adjoint and its adjunction, which is the data version of the node's
  `HasUpperShriek` assumption, without choosing or assuming a different adjoint.
- `nativeOmega` is G applied to the existing degree-zero constant Weil complex.
  `S : StructuralSystem D l X` and `c` specify the recorded constructible
  exceptional operation for the literal geometric structure morphism into
  Spec D.k. `coefficientOmega` is its G applied to `geometricPointOmega`.
- `P : Package D l R` is the fixed native exceptional comparison. The definition
  `omegaComparison` is exactly `P.actualSpecialization` at the structure morphism,
  the specified G and adj. Thus h comes from the cited comparison, not from a new
  existential isomorphism. `V : ForgetModel D l R X` fixes M_K = V.functor.obj K
  and j_K = V.realization.app K. The fully faithful rho makes these precisely
  the restriction of any chosen inverse equivalence, with its counit; its unit
  is uniquely determined. Quantification over V covers every such choice.
- `N : NativeClosedComparison ...` and `hN : N.Compatible` are the supplied
  native closed Hom comparison, including its product-total representative,
  evaluation and tensor normalizations. These are fixed comparison data already
  available from `native_closed_forgetful`, not hypotheses of a new existence
  theorem about closed structures.

### Conclusions, clause by clause

- `Comparison.presentation` exposes the tensor and Hom changes of ordinary
  presentation. `Presentation.hom_normalization` fixes its Hom component to the
  transpose of transported ordinary evaluation, using `closed.transpose` with
  the two actual morphism universes. This avoids the equal-universe restriction
  of the generic `nativeHomComparison` helper, without changing its formula.
- `Presentation.alpha` first uses the nativeModel identification with the actual
  upstream `ProEtaleWeilSheaf.derivedHom`, then the recorded N.homComparison,
  then ordinary closure/section presentation. It is the first comparison alpha.
- `Comparison.permitted K` says `(M_K, omega_Y)` is in the actual
  `commonStageHomPairs` predicate. Hence `coefficientHom` is the actual
  `commonStageDerivedInternalHom` at this pair and belongs to C_Y. The Hom is
  not replaced by an arbitrary endofunctor or a global Hom complex.
- `Comparison.comparison` is a natural isomorphism from `nativeHom ⋙ forget`
  to `coefficientHom ⋙ rho`. `nativeHom` uses the existing derivedHom, in the
  ambient native derived category, with target nativeOmega. This gives every
  c_K in the node, as an isomorphism of derived objects rather than just an
  isomorphism of cohomology objects.
- `beta` is literally the recorded realization `homComparison`, with the fixed
  realization's units and tensor data. `Comparison.composite` says
  c_K followed by beta_K equals alpha_K followed by the ambient Hom map induced
  by j_K in the first variable and omegaComparison in the second. Since beta is
  an isomorphism by the realization family, this is exactly the specified
  three-arrow composite, including inverse beta. The contravariant arrow is
  `(V.realization.hom.app K).op`, so it precomposes with j_K, not its inverse.
- `Comparison.bounded` says U(H_X K) satisfies the existing ordinary
  `boundedConstructible` predicate. That predicate is the section realization
  of bounded native module complexes with a finite locally closed stratification
  and locally finite free restrictions. No perfectness or lisse-only restriction
  is added.
- Naturality is the naturality of `Comparison.comparison` itself on `(W D l X)ᵒᵖ`.
  `coefficientHom.map` is the recorded common-stage internal-Hom map applied to
  V.functor.map; j is a natural isomorphism. Thus the conclusion applies to all
  native derived arrows, including extension morphisms, and assumes no
  faithfulness of the native forgetful functor.
- `Comparison.evaluation` begins at the tensor of the forgotten native Hom
  model with rho(M_K). Its left side tensors with j_K, inverts the composed
  native/presentation tensor comparison, applies forgotten native evaluation,
  and postcomposes with the fixed h. Its right side uses the nativeModel
  identification and c_K, the actual rho tensorator, and rho of the recorded
  coefficient-passage evaluation. This is precisely the final evaluation clause.
  The nativeModel identification is explicit on the right, so the upstream
  unary derivedHom and the supplied native bifunctor are never silently equated.

### Dependency declarations read and used

Read every direct statement dependency node and its recorded signature/docstring.
The imports re-export their notions along the following recorded interfaces:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`;
  native `WeilSheaf.frobeniusPullback` remains the action in the native category.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing` and `padicAlgClRingObj`.
- `Sheaf.Paper.CompletedCondensedCoefficients`: `completedCoefficient` and
  `completedCondensedAlgebraicClosure`, the native coefficient interpretation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exactly Mathlib `SheafOfModules` with its inherited abelian structure.
- `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `CategoryTheory.Endofunctor.IsoAlgebra` and its faithful forgetful functor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, Q and
  localization at quasi-isomorphisms. The native module uses its existing
  `HasDerivedCategory` instance; ordinary modules retain theirs independently.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`;
  native `WeilComplex.derivedLowerShriek` is retained via `nativeShriek`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (Mathlib dependency, no Lean record needed).
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and common-stage pair arrows.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, the
  raw rational localization with no idempotent completion.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, via StructuralSystem.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageHomPairs`,
  `commonStageDerivedInternalHom`, `commonStageDerivedTensor`.
- `Sheaf.Paper.AdicQbarConstructibleRealization`:
  `AdicQbarRealization.Family`, `SpaceData`, `At`, `HomLaws`, `homComparison`.
- `Sheaf.Paper.NativeWeilClosedForgetful`: `NativeClosedComparison`,
  `NativeClosedComparison.Compatible`, `nativeForget`, nativeModel,
  homComparison, tensorComparison and the native closed evaluation.
- `Sheaf.WeilSheaf.NativeExceptionalForgetful`: `Space`, `W`, `U`,
  `ForgetModel`, `Package.actualSpecialization`, `constant`, `rho`,
  `geometricPointOmega`, `StructuralSystem`.
- Proof-only import `Sheaf.SixFunctors.CoefQbarVerdier`:
  `coef_qbar_verdier` and its `InternalHom` conclusion. All four proof dependency
  modules occur in the import closure; this last is imported without `public`.

### Edge cases and source reading

Read the current blueprint `latest/.../cor-coef-verdier-weil-equivariance.proof.md`,
including its displayed contragredient structure and its statement that evaluation,
transposition and exceptional units/counits use the same maps. The old node source
path thm-coef-qbar-verdier.proof.md no longer exists at that unit path in latest;
the current equivariance proof provides the cited native comparison intent.
No mathematical statement correction is needed.

Checked empty schemes (Space does not require nonempty), zero complexes, the point
and identity structural morphism, arbitrary chosen algebraic closures, arbitrary
native adjunction choices, both directions of the contravariant j arrow, all
integer cohomological degrees, and extension morphisms. No hypothesis excludes
these. l = p is explicitly excluded; no extra characteristic or dimension bound
is introduced. The resolution recipe is the dependency's product total Hom into
K-injectives, not an underived Hom of cohomology sheaves.

### Searches

Ran the prescribed msearch.py searches for this item:

- leanfinder: "Native derived Weil dualizing internal Hom comparison with
  constructible coefficient realization and evaluation". Eight hits: underived
  light-condensed ihom and finite-module evaluation; none is this statement.
- loogle: `"derivedHom"`. Zero hits.
- leansearch: "Forgetting native derived Weil sheaves identifies dualizing
  internal Hom with constructible coefficient realization and evaluation".
  Eight hits on ordinary sheaf forgetting, sheafification or evaluation; none
  identifies native derived duality with coefficient realization.
- msearch grep: `dualizingComplex|dualRealization|WeilComplex` in CategoryTheory.
  No matching native/constructible comparison.
- rg in `lean/WeilConjectures` for the item id and dual-realization names: no
  item declaration. Existing native VerdierDual states preservation and
  biduality, but not this specified realization composite. Existing ordinary
  Verdier duality has the wrong source category for this node.
- rg in `lean/Sheaf`: unrelated lisse linear-dual realization comparisons,
  and the two intended native comparison dependencies. No existing theorem
  supplies the three-arrow dual-realization composite.
- rg in `dag/lean_names_upstream.json` and both source roots for
  `dual_realization_comparison|NativeDualRealization`: no name collision.

### Verification

The module compiled cleanly through scompile.py in sandbox form (36.2 seconds)
and library form (25.6 seconds), with no errors or warnings. A final run through
deliver2.py --no-push checks the final module header, metadata and report.

### Worker clause audit

Re-read the node and final Lean source after compilation. Corrected the
contravariant naturality prose to the actual order of composition. Removed the
unneeded upstream VerdierDual import. The specified adjoint, structure morphism,
constant, h, j, coefficient Hom pair, three-arrow formula, boundedness,
naturality and tensor/evaluation square are each explicit above. This is the
worker's own clause audit; the independent review is the maintainer's delivery
review, as the dispatcher brief specifies. No independent second-reader review
is claimed and no other agent was started.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
