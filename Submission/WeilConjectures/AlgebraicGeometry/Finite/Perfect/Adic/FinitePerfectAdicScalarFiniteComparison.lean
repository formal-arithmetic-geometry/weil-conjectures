/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import all Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantResidueComparison
import all Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation
import all Submission.WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finite quotient comparison for ordinary scalar extension

Source: Stacks Project, Tags 093J and 093M.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing

private def directLifted
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{t + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
    {B : Type t} [CommRing B] {R S : Sheaf J RingCat.{t + 1}}
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (p : R ⟶ S) : ModuleCat.{t} B ⥤ SheafOfModules.{t + 1} R :=
  finitePerfectAdicScalarModelLift B ⋙ directConstant α ⋙ SheafOfModules.restrictScalars p

private def directFinite (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  directLifted (S := completedAdicFiniteRing X d n)
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))
    (completedAdicProjection X d n)

private def quotientLiftIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ⋙
        finitePerfectAdicScalarModelLift A ≅
      finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1)) ⋙
        ModuleCat.restrictScalars (liftedQuotientEquiv X d r a ha n).toRingHom ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk
          ((Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
            (n + 1))) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

private def targetDirectIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ⋙
        finitePerfectAdicScalarModelOrdinary X d ≅ directFinite X d n := by
  let B := ULift.{t + 1} A
  let I := Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : B)))
  let Q := B ⧸ I ^ (n + 1)
  let : IsNoetherianRing A := d.noetherian
  let : IsNoetherianRing B := isNoetherianRing_of_surjective A B
    (ULift.ringEquiv : B ≃+* A).symm.toRingHom ULift.ringEquiv.symm.surjective
  let e := completionRingIso X d r a ha
  let p : completedAdicCommRing X d ⟶ adicLisseConstantRing X Q :=
    e.inv ≫ limit.π (adicLisseRingSystem X I) (op n)
  let c := completedAdicScalar X d
  let hc := completionRingIso_scalar X d r a ha
  let z := scalarResidueMap X (Ideal.Quotient.mk (I ^ (n + 1))) c p (hc n)
  have (N : ModuleCat.{t + 1} Q) : IsIso (z.app N) :=
    scalarResidueMap_isIso X I e c hc n N
  have : IsIso z := NatIso.isIso_of_isIso_app _
  let L := finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1))
  let v := (liftedQuotientEquiv X d r a ha n).toRingHom
  let α := adicLisseConstantUnit X Q
  let β := ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n)
  let k := quotientRingIso X d r a ha n
  have hk (Z : X.ProEtᵒᵖ) : α.app Z ≫ k.hom.hom.app Z =
      RingCat.ofHom v ≫ β.app Z := by
    ext x
    exact quotientRingIso_unit X d r a ha n Z x
  have hp : (adicLisseForget X).map p ≫ k.hom = completedAdicProjection X d n := by
    dsimp only [p]
    rw [Functor.map_comp, Category.assoc, ← completionRingIso_projection]
    change (adicLisseForget X).map e.inv ≫
      (adicLisseForget X).map e.hom ≫ completedAdicProjection X d n = _
    rw [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  let z₀ := isoWhiskerRight (quotientLiftIso X d r a ha n)
    (adicLisseConstantModules X B ⋙ completedAdicChange X c)
  let z₁ := isoWhiskerLeft (L ⋙ ModuleCat.restrictScalars v) (asIso z)
  let z₂ := isoWhiskerLeft L (isoWhiskerRight
    (directCoefficientIso α β v k.hom hk)
    (SheafOfModules.restrictScalars ((adicLisseForget X).map p)))
  let z₃ : SheafOfModules.restrictScalars k.hom ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map p) ≅
      SheafOfModules.restrictScalars (completedAdicProjection X d n) :=
    NatIso.ofComponents (fun N ↦ finitePerfectAdicRestrictComp
      ((adicLisseForget X).map p) k.hom (completedAdicProjection X d n) hp N)
      (by intros; ext; rfl)
  exact z₀ ≪≫ z₁ ≪≫ z₂ ≪≫ isoWhiskerLeft
    (L ⋙ directConstant β) z₃

attribute [local irreducible] targetDirectIso

end AlgebraicGeometry.Scheme
