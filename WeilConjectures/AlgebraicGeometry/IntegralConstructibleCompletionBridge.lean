/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalModels
import WeilConjectures.AlgebraicGeometry.IntegralSectionMemberModels
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison

/-!
# Integral constructibility and derived completion

Source: Bhatt--Scholze, Definition 6.5.1, Proposition 6.6.11 and
Proposition 6.8.11(3) (blueprint: lem-sfb-integral-constructible-completion-bridge).

The ordinary internal-module derived category is the ambient category. The detailed
integral predicate is evaluated under the existing projection-normalized coefficient
and section-action equivalence, without replacing K by its completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- General ring-object bounded constructibility, detailed integral constructibility,
and bounded constructibility with finite constant scalar models are equivalent.
The uniformizer is arbitrary; the existing coefficient construction chooses a generator
of the same maximal ideal, hence the same positive quotient tower. The lift of the finite
intermediate field only places its scalar carrier in the scheme universe.

Source: Bhatt--Scholze, Definition 6.5.1, Proposition 6.6.11 and
Proposition 6.8.11(3) (blueprint: lem-sfb-integral-constructible-completion-bridge).

Proof:
1. Transport the proved integral local-finite-presentation comparison through the
WithAbs-to-embedded and embedded-to-spectral coefficient isomorphisms. Restriction
along each isomorphism preserves finite presentations and finite constant local
models; its identity round trip reflects them. Apply this equivalence to each
cohomology sheaf, retaining boundedness, to identify (i) and (iii).
2. Apply integralSectionLocalModels to each cohomology sheaf. This compares the
finite scalar models under the fixed section-action and completed-ring restriction
functors. Exactness identifies the image of cohomology with the cohomology of the
image; the comparison of local models is invariant under this isomorphism.
3. Both ordinary functors are faithful and exact, so their derived functors preserve
and reflect boundedness. Given bounds a,b, replace them by min(a,b),b to ensure the
ordered interval required by IsIntegralBoundedConstructibleCohomology. Thus (iii)
is precisely the completed cohomological scalar-model condition on the transported K.
4. The two equivalences of integralStratifiedPerfectCharacterization identify that
condition with PbcIsBoundedConstructibleComplete. Its detailed-category clause
identifies the latter with (ii) under integralSectionDerivedEquivalence. These
functors transport K itself. Transitivity gives both displayed equivalences; no
completion or perfectness of K was assumed.
-/
theorem integralConstructibleCompletionBridge
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (_π : PadicAlgCl.integers l E)
    (_hπ : Ideal.span {_π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E))
    (Z : Scheme.{u}) [IsNoetherian Z]
    (_hdim : ∃ n : ℕ, topologicalKrullDim Z ≤ n)
    (_hinv : IsUnit (l : Γ(Z, ⊤)))
    (K : DerivedCategory (AdicCompletion.Modules l (ULift.{u} E.val) Z)) :
    (boundedConstructible (AdicCompletion.ring l (ULift.{u} E.val) Z) K ↔
      WeilConjectures.sfIntegralConstructible l (ULift.{u} E.val) Z
        ((integralSectionDerivedEquivalence l (ULift.{u} E.val) Z).functor.obj K)) ∧
    (boundedConstructible (AdicCompletion.ring l (ULift.{u} E.val) Z) K ↔
      constantModelBoundedConstructible (DerivedNakayama.integerRing l (ULift.{u} E.val))
        Z K) := by
  have hmod (M : AdicCompletion.Modules l (ULift.{u} E.val) Z) :
      IsConstructibleModuleObject (AdicCompletion.ring l (ULift.{u} E.val) Z) M ↔
        IsConstantModelConstructible (DerivedNakayama.integerRing l (ULift.{u} E.val)) Z M := by
    obtain ⟨e₁⟩ := integralCoefficientIso.{u} l E
    let e₂ := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (integerRingSheafIso l E)
    have : IsMonHom e₂.hom := Sheaf.isMonHom_sheafCompose_map _
      (integerRingSheafIso l E).hom
    let φ := e₁.hom.hom ≫ e₂.hom
    have : IsMonHom φ := inferInstance
    have : IsIso φ := inferInstance
    let ψ := coefficientMap φ Z
    have hp := integralLfpConstantModelComparison l (ULift.{u} E.val) Z
      ((Mod.comap ψ).obj M)
    have hgen :
        IsConstructibleModuleObject
          (condensedRingObj (integralCondensedRing l (ULift.{u} E.val)) Z)
          ((Mod.comap ψ).obj M) ↔
        IsConstructibleModuleObject (AdicCompletion.ring l (ULift.{u} E.val) Z) M := by
      constructor
      · intro h
        exact _root_.constructible_of_iso
          (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
            Mod.comapId _).app M) (_root_.constructible_comap (inv ψ) h)
      · exact _root_.constructible_comap ψ
    exact hgen.symm.trans (hp.trans (constantModel_comap_iff φ Z M))
  have hconst : boundedConstructible (AdicCompletion.ring l (ULift.{u} E.val) Z) K ↔
      constantModelBoundedConstructible (DerivedNakayama.integerRing l (ULift.{u} E.val)) Z K := by
    exact and_congr_right fun _ ↦ forall_congr' fun n ↦ hmod _
  let S := integralSectionFunctor l (ULift.{u} E.val) Z
  let R := SheafOfModules.restrictScalars.{u + 1}
    (Scheme.integralDetailedCoefficientComparison Z l (ULift.{u} E.val)).hom
  have : CategoryTheory.Limits.PreservesFiniteLimits R :=
    (Scheme.integralDetailedCoefficientRestriction_exact Z l (ULift.{u} E.val)).1
  have : CategoryTheory.Limits.PreservesFiniteColimits R :=
    (Scheme.integralDetailedCoefficientRestriction_exact Z l (ULift.{u} E.val)).2
  have : R.Faithful := ⟨by
    intro M N f g h
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h⟩
  let L := R.mapDerivedCategory.obj (S.mapDerivedCategory.obj K)
  have hb : DerivedCategory.TStructure.t.bounded K ↔
      ∃ a b : ℤ, a ≤ b ∧ L.IsGE a ∧ L.IsLE b := by
    constructor
    · intro h
      have hL := R.bounded_mapDerivedCategory_obj (S.bounded_mapDerivedCategory_obj h)
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hL
      exact ⟨min a b, b, min_le_right _ _,
        DerivedCategory.TStructure.t.isGE_of_ge L (min a b) a (min_le_left _ _), hb⟩
    · rintro ⟨a, b, _, ha, hb⟩
      exact S.bounded_of_bounded_mapDerivedCategory_obj
        (R.bounded_of_bounded_mapDerivedCategory_obj ⟨⟨a, ha⟩, ⟨b, hb⟩⟩)
  have hc : constantModelBoundedConstructible
      (DerivedNakayama.integerRing l (ULift.{u} E.val)) Z K ↔
      Scheme.IsIntegralBoundedConstructibleCohomology Z
        (Scheme.pbcIntegralDatum l (ULift.{u} E.val)) L := by
    apply and_congr hb
    apply forall_congr'
    intro q
    have e := R.mapIso ((S.mapDerivedCategoryHomologyFunctorIso q).app K) ≪≫
      (R.mapDerivedCategoryHomologyFunctorIso q).app (S.mapDerivedCategory.obj K)
    have hm := integralSectionLocalModels
      (DerivedNakayama.integerRing l (ULift.{u} E.val)) Z
      ((DerivedCategory.homologyFunctor _ q).obj K)
    have hlocal : IsConstantModelConstructible
        (DerivedNakayama.integerRing l (ULift.{u} E.val)) Z
        ((DerivedCategory.homologyFunctor _ q).obj K) ↔
        Scheme.IsIntegralStratifiedFinitelyPresented Z
          (Scheme.pbcIntegralDatum l (ULift.{u} E.val))
          (R.obj (S.obj ((DerivedCategory.homologyFunctor _ q).obj K))) := by
      apply hm.trans
      apply exists_congr
      intro s
      apply forall_congr'
      intro i
      apply exists_congr
      intro V
      apply and_congr_right
      intro hV
      apply forall_congr'
      intro U
      apply forall_congr'
      intro f
      apply imp_congr_right
      intro hf
      exact integralSectionMemberModels l (ULift.{u} E.val) (s.immersion i) U _
    refine hlocal.trans ?_
    exact ⟨fun h ↦ Scheme.finitelyPresented_iso Z _ e h,
      fun h ↦ Scheme.finitelyPresented_iso Z _ e.symm h⟩
  have hchar := Scheme.integralStratifiedPerfectCharacterization Z l
    (ULift.{u} E.val) _hdim _hinv L
  have hdetail := Scheme.integralStratifiedPerfectDetailed Z l
    (ULift.{u} E.val) _hdim _hinv
    ((integralSectionDerivedEquivalence l (ULift.{u} E.val) Z).functor.obj K)
  exact ⟨hconst.trans (hc.trans ((hchar.1.trans hchar.2).symm.trans hdetail.symm)), hconst⟩

end AlgebraicGeometry.ProEtale
