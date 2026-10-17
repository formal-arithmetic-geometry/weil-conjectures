/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Algebraizing a formal pullback isomorphism with quotient compatibility

Source: Stacks Project, Tag 088B, final complete-base paragraph; Tags 087W and 0883.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A formal pullback isomorphism over a complete affine base lifts to an algebraic
isomorphism, compatibly with the actual quotient projections.
Source: Stacks Project, Tag 088B, final complete-base paragraph; Tags 087W and 0883.
(blueprint: lem-weil-pbc-formal-comparison-algebraization-quotient-lift)

Proof: Tag 087W associates to G its finite module over the completion of A.
Since A is I-adically complete, restrict this module along the isomorphism
A -> its completion and take its tilde, a coherent module A0. The unit and inverse
comparison of the affine equivalence give e from G to the quotient system of A0. Pullback preserves
coherence on the Noetherian proper scheme and commutes with the quotient system;
the comparison is specified by the images of the quotient projections. Compose
it with the pullback of e.inv and beta. Tag 0883 lifts this isomorphism
and its inverse uniquely to maps between p* A0 and F. Injectivity on Hom makes
the lifted composites identities. The resulting isomorphism b has exactly the
displayed projection equation, since the quotient comparison sends the projection
to the pullback of the projection. The zero ring causes no exception: all these
categories and maps are zero. -/
theorem formalComparison_algebraization_quotient_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) [IsProper p]
    (G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (F : CoherentModules Z)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback p ≅
      formalCompletionSystem (J.comap p) F.obj) :
    ∃ (A₀ : CoherentModules (Spec (CommRingCat.of A)))
      (e : G.obj ≅ formalCompletionSystem J A₀.obj)
      (b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F.obj),
      ∀ n : ℕ,
        (Scheme.Modules.tensorPullback p).map (formalModuleQuotientπ J (n + 1) A₀.obj) ≫
          (Scheme.Modules.tensorPullback p).map (e.inv.app (op n)) ≫ β.hom.app (op n) =
        b.hom ≫ formalModuleQuotientπ (J.comap p) (n + 1) F.obj := by
  classical
  obtain ⟨E, _, _, _, _, _, ⟨c⟩⟩ := coherentFormalModules_affine A I J hJ
  let N := E.functor.obj G
  let M := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj
  let H := (tilde.functor (CommRingCat.of A)).obj M
  have : Module.Finite A (AdicCompletion I A) :=
    Module.Finite.equiv (AdicCompletion.ofLinearEquiv I A)
  let : Module (AdicCompletion I A) M := N.obj.isModule
  have : IsScalarTower A (AdicCompletion I A) M :=
    IsScalarTower.of_algebraMap_smul (fun a x ↦
      (ModuleCat.restrictScalars.smul_def (algebraMap A (AdicCompletion I A)) a x).symm)
  have : Module.Finite (AdicCompletion I A) M := N.property
  have : Module.Finite A M := Module.Finite.trans (AdicCompletion I A) M
  have : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj H) :=
    Module.Finite.equiv (tilde.isoTop (R := CommRingCat.of A) M).toLinearEquiv
  let : Module A Γ(H, ⊤) := inferInstanceAs
    (Module A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj H))
  let : Algebra A Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toAlgebra
  have : IsScalarTower A Γ(Spec (CommRingCat.of A), ⊤) Γ(H, ⊤) :=
    IsScalarTower.of_algebraMap_smul (fun a x ↦ (Scheme.Modules.smul_top_eq H a x).symm)
  have : Module.Finite A Γ(H, ⊤) := inferInstanceAs
    (Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj H))
  have : Module.Finite Γ(Spec (CommRingCat.of A), ⊤) Γ(H, ⊤) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hq : H.IsQuasicoherent := by
    exact (presentationTilde (R := CommRingCat.of A) M Set.univ
      (by simp) _ (Submodule.span_eq _)).isQuasicoherent
  have ht : H.IsFiniteType :=
    ((Scheme.Modules.quasicoherent_finite_type_affine _).2 H hq).2.1
      PUnit.{u + 1} (fun _ ↦ ⊤) (by simp) (fun _ ↦ isAffineOpen_top _)
      (fun _ ↦ inferInstance) |>.1
  let A₀ : CoherentModules (Spec (CommRingCat.of A)) :=
    ⟨H, (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mpr ⟨hq, ht⟩⟩
  let e : G.obj ≅ formalCompletionSystem J A₀.obj :=
    (ObjectProperty.ι (IsCoherentFormalModule J)).mapIso (E.unitIso.app G) ≪≫
      c.app (E.functor.obj G)
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  let P : CoherentModules Z := ⟨(Scheme.Modules.tensorPullback p).obj A₀.obj,
    coherent_pullback p A₀.obj A₀.property⟩
  let q : formalCompletionSystem (J.comap p) P.obj ≅
      formalCompletionSystem (J.comap p) F.obj :=
    (completionPullbackIso p J).app A₀ ≪≫
      Functor.isoWhiskerRight e.symm (Scheme.Modules.tensorPullback p) ≪≫ β
  let C := completion Z (J.comap p)
  have hbij (K L : CoherentModules Z) : Function.Bijective
      (fun v : K ⟶ L ↦ C.map v) := by
    subst J
    exact formalCompletion_map_bijective_of_proper I p K L
  let : C.Full := ⟨fun {K L} ↦ (hbij K L).2⟩
  let : C.Faithful := ⟨fun {K L} ↦ (hbij K L).1⟩
  let q' : C.obj P ≅ C.obj F :=
    (ObjectProperty.fullyFaithfulι (IsCoherentFormalModule (J.comap p))).preimageIso q
  let b' : P ≅ F := C.preimageIso q'
  let b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F.obj :=
    (ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace)).mapIso b'
  refine ⟨A₀, e, b, ?_⟩
  intro n
  have hb : formalCompletionMap (J.comap p) b.hom = q.hom := by
    change (ObjectProperty.ι (IsCoherentFormalModule (J.comap p))).map
      (C.map b'.hom) = q.hom
    simp [b', q']
  have hbn := congrArg (fun t ↦ t.app (op n)) hb
  have hπ := powerQuotientIso_π p J A₀.obj hq (n + 1)
  calc
    _ = formalModuleQuotientπ (J.comap p) (n + 1) P.obj ≫ q.hom.app (op n) := by
      dsimp only [q, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Iso.symm_hom]
      change _ = formalModuleQuotientπ (J.comap p) (n + 1)
        ((Scheme.Modules.tensorPullback p).obj A₀.obj) ≫
        (powerQuotientIso p J A₀.obj hq (n + 1)).hom ≫ _ ≫ _
      simpa only [Category.assoc] using
        congrArg (fun t ↦ t ≫ (Scheme.Modules.tensorPullback p).map
          (e.inv.app (op n)) ≫ β.hom.app (op n)) hπ.symm
    _ = b.hom ≫ formalModuleQuotientπ (J.comap p) (n + 1) F.obj := by
      rw [← hbn]
      exact cokernel.π_desc _ _ _

end
end AlgebraicGeometry
