/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionRealization
import WeilConjectures.AlgebraicGeometry.Native.NativeBasicComparisons
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralProjectionFormulaLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperProjectionFormulaField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CommonFieldLatticeGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionModels
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryProperProjectionInvertible

/-! # Compact projection formula theorem

Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection (blueprint: lem-sf-derived-weil-compact-projection-formula).

## Main statements

* `AlgebraicGeometry.WeilComplex.native_compact_projection_formula`: the unchanged
  compactification projection formula, separated from its existing definitions so
  its future proof may import the native proper-projection theorem without a cycle.

All comparison and compactification definitions are reused from their original module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

set_option maxHeartbeats 800000 in
-- Elaborating the normalized comparison records exceeds the default heartbeat budget.

/-- All normalized comparisons for the native proper projection. These are output
data, not hypotheses on the morphism or on its constructible derived inputs.
Source: BS 6.8.14--6.8.15; native projection proof Steps 1--8
(blueprint: lem-sf-native-proper-projection-realization). -/
structure NativeProperProjectionRealization_legacy extends NativeProperProjectionModels k₀ l p where
  projection : properNativeProjectionSource k₀ l p ≅ properNativeProjectionTarget k₀ l p
  projectionMate : ∀ (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y),
    projection.hom.app (A, T) = nativeProjectionProperMate k₀ l p balanced A.obj T.obj
  projectionForget : ∀ (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y),
    (properSectionDerived k₀ l Y target).map
        (nativeProjectionProperMate k₀ l p balanced A.obj T.obj) ≫
      push.hom.app ((nativeDerivedTensor k₀ l Z).obj
        (A.obj, (nativeOpenPull k₀ l p).obj T.obj)) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
        (sourceTensor.tensor.hom.app (A.obj, (nativeOpenPull k₀ l p).obj T.obj) ≫
          sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (pull.hom.app T.obj))) =
    targetTensor.tensor.hom.app
        ((lowerStar k₀ l p).rightDerivedFunctor.obj A.obj, T.obj) ≫
      targetAt.closed.tensor.map (Prod.mkHom (push.hom.app A.obj) (𝟙 _)) ≫
      properOrdinaryProjection k₀ l p source target sourceAt targetAt
        comparison.operations comparison.tensor
        ((properSectionDerived k₀ l Z source).obj A.obj)
        ((properSectionDerived k₀ l Y target).obj T.obj)
  projectionRealization : ∀
      (K : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    (ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).map
        (properCommonProjection k₀ l p primeUnit K L) ≫
      comparison.b.hom.app
        ((commonStageDerivedTensor l (PadicAlgCl l)
          (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
          (K, (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj L)) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
        (sourceAt.tensor.inv.app (K,
          (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj L) ≫
          sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (comparison.a.hom.app L))) =
    targetAt.tensor.inv.app ((properCommonPush k₀ l p primeUnit).obj K, L) ≫
      targetAt.closed.tensor.map (Prod.mkHom (comparison.b.hom.app K) (𝟙 _)) ≫
      properOrdinaryProjection k₀ l p source target sourceAt targetAt
        comparison.operations comparison.tensor
        ((ordinary l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source).obj K)
        ((ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).obj L)

/-- The native proper projection is a natural isomorphism on arbitrary bounded
constructible derived inputs, and its actual counit mate has the stated ordinary
and common-stage realizations, with the proper identity-open normalization.
Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection; Bhatt--Scholze 6.8.14--6.8.15, pp. 61--62
(blueprint: lem-sf-native-proper-projection-realization).

Proof:
1. The coefficient-ring comparison of lem-sf-locally-finite-coefficient-ring-realization
identifies locally finite spans and locally finite extension values: a finite basis
lies in one finite subextension. Its coefficient-map square identifies precomposition.
The native closed-forgetful theorem and the constructible realization equivalence
supply common-stage lifts of the underlying A and T. Properness and separated finite
type are preserved by geometric base change.
2. Lift the actual sheaf inverse/direct-image adjunction using
lem-sf-fixed-pair-adjunction-lift and the native Frobenius mate relation. Exact and
conservative forgetting detects exact pullback. Equivariant K-flat and K-injective
resolutions are supplied by lem-sf-weil-frobenius-action-resolutions.
3. On A to I with I equivariant K-injective, forgetting computes both pushforwards
on the same complex. Exact pullback implies pushforward preserves K-injectives by
termwise homotopy adjunction; maps into these complexes compute derived Hom by
lem-weil-pbc-kinjective-hom-derived. Thus the actual derived counit is the localized
sheaf counit followed by the inverse augmentation, on both sides. This gives
pushRepresentative and counit, using lem-sf-fixed-pair-derived-forget-comparison.
4. Balanced tensor maps send b tensor (x tensor y) to (b tensor x) tensor (1 tensor y)
and inversely multiply the two coefficients. They commute with Frobenius. Totalize
with differential d tensor 1 plus (-1)^i 1 tensor d on equivariant K-flat flat-term
resolutions. The ringed pullback K-flat theorem and conservative forgetting allow
derived descent. This gives balanced, the section tensor generators and models,
and pullTensor; use lem-sf-ringed-forget-tensor-transposition.
5. Form the actual native counit mate. The preceding counit and tensor squares
identify its forgotten composite with the ordinary projection mate of
lem-weil-pbc-ringed-projection-mate-exact. This gives projectionForget by functoriality;
faithfulness of derived forgetting is not assumed.
6. Descend A and T to a common finite coefficient field. At field stages bounded
constructible equals bounded constructible finite-Tor, so thm-sf-pf-field applies
to every T in the statement. Use compactification (identity,p) in def-exchange-projection:
the identity-open tensor comparison is the identity, leaving properCommonProjection.
7. Substitute the normalized proper-realization counit, unit and tensor equations
of lem-sf-adic-proper-adjunction-realization in that common-stage mate. This gives
projectionRealization with its actual a and b, not merely an object isomorphism.
Since realization carries the field projection isomorphism to the ordinary mate,
the latter is invertible.
8. Conservative native forgetting detects invertibility. The inverse is natural
by multiplying the naturality square by the two inverses. Native tensor closure
and pullback/direct-image preservation place source and target in the bounded
constructible full categories. Their full inclusions restrict the same arrow and
inverse. No restriction to lisse sheaves or single-degree derived objects is used.
-/
theorem native_proper_projection_realization_legacy [IsProper p] :
    Nonempty (NativeProperProjectionRealization_legacy k₀ l p) := by
  obtain ⟨M⟩ := native_proper_projection_models k₀ l p
  let := M.sourceUnits
  let := M.targetUnits
  let UX := properSectionDerived k₀ l Z M.source
  let UY := properSectionDerived k₀ l Y M.target
  let F := nativeOpenPull k₀ l p
  let FB := ContinuousRational.derivedPull
    (NativeBaseChange.geometricMap k₀ p) M.comparison.operations.coefficient
  let RB := ContinuousRational.DirectImage.derivedPush
    (NativeBaseChange.geometricMap k₀ p) M.comparison.operations.coefficient
  have hforget (A : DerivedCategory (ProEtaleWeilSheaf k₀ l Z))
      (T : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :=
    projection_square (derivedUpperStarLowerStarAdjunction k₀ l p)
      M.comparison.operations.adjunction
      (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      M.targetAt.closed.tensor M.sourceAt.closed.tensor
      (fun P Q ↦ M.balanced.mu.hom.app (P, Q))
      M.targetTensor.tensor.hom M.sourceTensor.tensor.hom M.comparison.tensor.tensor.hom
      M.pull M.push M.pullTensor M.counit A T
  have hcommonTensor (P Q : generalAlgebraicallyClosedConstructibleCategory l
      (PadicAlgCl l) (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
      (ordinary l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber M.source).map
          (canonicalCommonStagePullbackTensor l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p) P Q).hom ≫
        M.sourceAt.tensor.inv.app
          ((commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj P,
           (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj Q) ≫
        M.sourceAt.closed.tensor.map
          (Prod.mkHom (M.comparison.a.hom.app P) (M.comparison.a.hom.app Q)) =
      M.comparison.a.hom.app
          ((commonStageDerivedTensor l (PadicAlgCl l)
            (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj (P, Q)) ≫
        FB.map (M.targetAt.tensor.inv.app (P, Q)) ≫
        M.comparison.tensor.tensor.hom.app
          ((ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber M.target).obj P,
           (ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber M.target).obj Q) := by
    exact inverse_tensor_square _ _ _ _
      (fun P Q ↦ (canonicalCommonStagePullbackTensor l (PadicAlgCl l)
        (NativeBaseChange.geometricMap k₀ p) P Q).hom)
      M.targetAt.tensor M.sourceAt.tensor M.comparison.tensor.tensor.hom
      M.comparison.a M.comparison.tensor_compatibility P Q
  have hrealization := fun K L ↦ projection_square
    (geometricCommonStageAdjunction l (PadicAlgCl l) (AlgebraicClosure k₀) M.primeUnit
      (NativeBaseChange.geometricMap k₀ p)) M.comparison.operations.adjunction
    (commonStageDerivedTensor l (PadicAlgCl l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (commonStageDerivedTensor l (PadicAlgCl l)
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    M.targetAt.closed.tensor M.sourceAt.closed.tensor
    (fun P Q ↦ (canonicalCommonStagePullbackTensor l (PadicAlgCl l)
      (NativeBaseChange.geometricMap k₀ p) P Q).hom)
    M.targetAt.tensor.inv M.sourceAt.tensor.inv M.comparison.tensor.tensor.hom
    M.comparison.a M.comparison.b hcommonTensor M.comparison.counit K L
  have hbc (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
      [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
      (S : LocallyFiniteAdicRealization.Realization l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (A : WeilComplex k₀ l X) :
      boundedConstructible l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber S
        ((properSectionDerived k₀ l X S).obj A.obj) := by
    refine ⟨(nativeForget k₀ l X).obj A.obj, ?_, ⟨Iso.refl _⟩⟩
    exact (native_closed_forgetful k₀ l X).2.2.2.1 A
  have hreflect : UY.ReflectsIsomorphisms := by
    let := M.targetPresentation
    let : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.target).Additive := M.target.sectionsAdditive
    let : (nativeForget k₀ l Y).ReflectsIsomorphisms :=
      (native_closed_forgetful k₀ l Y).2.1
    change (nativeForget k₀ l Y ⋙
      (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
        M.target).mapDerivedCategory).ReflectsIsomorphisms
    infer_instance
  let := hreflect
  have hiso (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y) :
      IsIso (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj) := by
    have hOrd := properOrdinaryProjection_isIso k₀ l p M.source M.target
      M.sourceAt M.targetAt M.primeUnit M.comparison (UX.obj A.obj) (UY.obj T.obj)
      (hbc Z M.source A) (hbc Y M.target T)
    let := hOrd
    have h := hforget A.obj T.obj
    have hpairPush : IsIso (Prod.mkHom (M.push.hom.app A.obj) (𝟙 (UY.obj T.obj))) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have hpairPull : IsIso (Prod.mkHom (𝟙 (UX.obj A.obj)) (M.pull.hom.app T.obj)) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have hcomp : IsIso
        (UY.map (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj) ≫
          M.push.hom.app ((nativeDerivedTensor k₀ l Z).obj (A.obj, F.obj T.obj)) ≫
          RB.map (M.sourceTensor.tensor.hom.app (A.obj, F.obj T.obj) ≫
            M.sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (M.pull.hom.app T.obj)))) := by
      rw [show UY.map (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj) ≫
          M.push.hom.app _ ≫ RB.map _ = _ from h]
      change IsIso (M.targetTensor.tensor.hom.app
          ((lowerStar k₀ l p).rightDerivedFunctor.obj A.obj, T.obj) ≫
        M.targetAt.closed.tensor.map (Prod.mkHom (M.push.hom.app A.obj) (𝟙 (UY.obj T.obj))) ≫
        properOrdinaryProjection k₀ l p M.source M.target M.sourceAt M.targetAt
          M.comparison.operations M.comparison.tensor (UX.obj A.obj) (UY.obj T.obj))
      infer_instance
    have hmapped : IsIso
        (UY.map (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj)) :=
      (isIso_comp_right_iff _ _).1 hcomp
    exact isIso_of_reflects_iso _ UY
  let := hiso
  let projection : properNativeProjectionSource k₀ l p ≅
      properNativeProjectionTarget k₀ l p :=
    NatIso.ofComponents
      (fun P ↦ asIso (nativeProjectionProperMate k₀ l p M.balanced P.1.obj P.2.obj))
      (by
        intro P Q f
        exact projection_naturality (derivedUpperStarLowerStarAdjunction k₀ l p)
          (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z) M.balanced.mu.hom
          f.1.hom f.2.hom)
  exact ⟨{
    toNativeProperProjectionModels := M
    projection := projection
    projectionMate := fun _ _ ↦ rfl
    projectionForget := fun A T ↦ hforget A.obj T.obj
    projectionRealization := hrealization }⟩

/-- Compact projection for arbitrary bounded constructible derived Weil inputs.
The isomorphism is in the full bounded constructible category, natural in both
variables. Its underlying ambient map is exactly the chosen-compactification
composite: proper counit mate, open tensor comparison, balanced compositor.
All comparison data occur in the conclusion, with their representative and unit
normalizations, rather than as additional assumptions.

Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection (blueprint: lem-sf-derived-weil-compact-projection-formula).

Proof:
1. Let X --j--> Z --p--> Y be the framework's chosen compactification.
By lem-sf-native-weil-basic-comparisons, exact extension by zero sends M to a
bounded constructible A. Its cohomology is j! H^r(M), and extending a finite
stratification by the closed complement with rank zero preserves constructibility.
The proper map p is finite type, so Z is finite type by
lem-sfb-finite-type-composition-base-change. The diagonal of Z factors through
Z times_Y Z: the first factor is closed by properness and the second is the base
change of the closed diagonal of Y. Closed immersions compose. Thus Z is separated;
lem-pod-separated-finite-type-base-change gives the same geometric domain.
2. Apply lem-sf-native-proper-projection-realization to (A,T). Its normalized
balanced comparison gives C and its counit transpose is nativeProjectionProperMate.
Apply lem-sf-native-open-derived-tensor to (M,p* T), using its normalized gamma.
Compose alpha with Rp*(gamma), then Rp*j!(1 tensor the balanced compositor).
This is precisely the formula below and the compactification defining Rf!.
Each map and inverse is an actual derived Weil arrow, natural in both variables.
3. Pullback preservation (lem-sf-native-weil-pullback-star-preservation), tensor
closure (lem-sf-derived-weil-tensor-hom-adjunction), and compact-support
preservation (lem-sf-native-weil-shriek-triangulated) put both sides in WC^der(Y).
Fullness restricts the ambient isomorphism, its inverse, and its naturality
identities. No lisse or degree-zero condition on T was used. -/
theorem native_compact_projection_formula :
    ∃ (C : ProEtaleWeilSheaf.NativeProjectionTensorComparison k₀ l
          (nativeProjectionCompactification k₀ f).g)
      (s : ProEtaleWeilSheaf.NativeOpenTensorData k₀ l
          (nativeProjectionCompactification k₀ f).i)
      (d : ProEtaleWeilSheaf.NativeOpenDerivedTensorData k₀ l
          (nativeProjectionCompactification k₀ f).i s)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l X)
          (ProEtaleWeilSheaf k₀ l (nativeProjectionCompactification k₀ f).Z))
      (pi : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f),
      ProEtaleWeilSheaf.NativeOpenPresentationCompatibility k₀ l
          (nativeProjectionCompactification k₀ f).i s d c ∧
      ∀ (M : WeilComplex k₀ l X) (T : WeilComplex k₀ l Y),
        (pi.hom.app (M, T)).hom =
          ProEtaleWeilSheaf.nativeProjectionProperMate k₀ l
            (nativeProjectionCompactification k₀ f).g C
            ((ProEtaleWeilSheaf.nativeOpenExtension k₀ l
              (nativeProjectionCompactification k₀ f).i).obj M.obj) T.obj ≫
          (ProEtaleWeilSheaf.lowerStar k₀ l
            (nativeProjectionCompactification k₀ f).g).rightDerivedFunctor.map
            (d.gamma.hom.app (M.obj,
              (ProEtaleWeilSheaf.nativeOpenPull k₀ l
                (nativeProjectionCompactification k₀ f).g).obj T.obj)) ≫
          (ProEtaleWeilSheaf.lowerStar k₀ l
            (nativeProjectionCompactification k₀ f).g).rightDerivedFunctor.map
            ((ProEtaleWeilSheaf.nativeOpenExtension k₀ l
              (nativeProjectionCompactification k₀ f).i).map
              ((ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).map
                (Prod.mkHom (𝟙 M.obj) ((nativeProjectionPullComp k₀ l f).hom.app T.obj)))) := by
  let q := nativeProjectionCompactification k₀ f
  let : QuasiCompact q.i := q.quasiCompact_openImmersion inferInstance
  let E := ProEtaleWeilSheaf.nativeOpenExtension k₀ l q.i
  let R := (ProEtaleWeilSheaf.lowerStar k₀ l q.g).rightDerivedFunctor
  let IX := (objectProperty k₀ l X).ι
  let IY := (objectProperty k₀ l Y).ι
  let J : WeilComplex k₀ l X ⥤ WeilComplex k₀ l q.Z :=
    (objectProperty k₀ l q.Z).lift (IX ⋙ E) (fun M ↦
      (nativeWeilBasicComparisons k₀ l).2.2.1 X q.Z q.i |>.2.2 M.obj M.property)
  obtain ⟨r⟩ := ProEtaleWeilSheaf.native_proper_projection_realization_legacy k₀ l q.g
  obtain ⟨s, d, c, hc⟩ := ProEtaleWeilSheaf.native_open_derived_tensor k₀ l q.i
  -- Apply proper projection to the bounded constructible extension of M.
  let alpha := Functor.isoWhiskerLeft (J.prod (𝟭 (WeilComplex k₀ l Y))) r.projection
  -- Apply the normalized open comparison to (M, p* T), then push forward.
  let beta := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      (IX.prod (IY ⋙ ProEtaleWeilSheaf.nativeOpenPull k₀ l q.g)) d.gamma) R
  -- Replace j* p* by f* using the actual balanced compositor.
  let pull := Functor.isoWhiskerLeft IY (nativeProjectionPullComp k₀ l f)
  let delta := Functor.isoWhiskerRight (NatIso.prod (Iso.refl IX) pull)
    (ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X ⋙ E ⋙ R)
  let ambient : nativeCompactProjectionLeft k₀ l f ⋙ IY ≅
      nativeCompactProjectionRight k₀ l f ⋙ IY :=
    alpha ≪≫ beta ≪≫ delta
  -- Fullness restricts both arrows and all naturality equations at once.
  let pi : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f :=
    ((objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso ambient
  refine ⟨r.balanced, s, d, c, pi, hc, ?_⟩
  intro M T
  change r.projection.hom.app (J.obj M, T) ≫ _ = _
  rw [r.projectionMate]
  rfl

end AlgebraicGeometry.WeilComplex
