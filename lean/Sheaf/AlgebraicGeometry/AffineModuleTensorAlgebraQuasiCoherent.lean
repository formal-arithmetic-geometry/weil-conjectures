/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.AffineModuleTensorBaseChange
import Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.Final.Type
/-! # Quasi-coherence of the affine tensor pushout algebra

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-algebra-quasi-coherent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

private def isoOfHomEquiv {C : Type*} [Category C] (M N : C)
    (e : ∀ P, (M ⟶ P) ≃ (N ⟶ P))
    (he : ∀ P Q (a : M ⟶ P) (b : P ⟶ Q), e Q (a ≫ b) = e P a ≫ b) : M ≅ N where
  hom := (e N).symm (𝟙 N)
  inv := e M (𝟙 M)
  hom_inv_id := by
    apply (e M).injective
    rw [he, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := he M N (𝟙 M) ((e N).symm (𝟙 N))
    simpa using h.symm

private theorem changeOfRings_unit_iso {T : TopCat.{u}} (C D : T.Sheaf CommRingCat.{u})
    (a : C ⟶ D) :
    Nonempty (SheafOfModules.changeOfRings.{u, u, u} a (SheafOfModules.unit (𝓡 C)) ≅
      SheafOfModules.unit (𝓡 D)) := by
  obtain ⟨E, h, adj, _⟩ := SheafOfModules.exists_changeOfRingsAdjunction T C D a
  let e (N : SheafOfModules.{u} (𝓡 D)) :
      (E.obj (SheafOfModules.unit (𝓡 C)) ⟶ N) ≃ (SheafOfModules.unit (𝓡 D) ⟶ N) :=
    (adj.homEquiv _ N).trans
      (((SheafOfModules.restrictScalars (𝓻 a)).obj N).unitHomEquiv.trans N.unitHomEquiv.symm)
  refine ⟨(eqToIso (h _)).symm ≪≫ isoOfHomEquiv _ _ e ?_⟩
  intro N N' k l
  dsimp only [e, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_right]
  erw [SheafOfModules.unitHomEquiv_comp_apply]
  exact (SheafOfModules.unitHomEquiv_symm_comp (M := N) (N := N')
    (((SheafOfModules.restrictScalars (𝓻 a)).obj N).unitHomEquiv
      (adj.homEquiv _ N k)) l).symm

set_option maxHeartbeats 800000 in
-- Transporting sections through three equivalences unfolds dependent module instances.
private theorem inverseImage_unit_iso {T T' : TopCat.{u}} (g : T ⟶ T')
    (C : T'.Sheaf CommRingCat.{u}) :
    Nonempty (TopCat.Sheaf.inverseImageModule g C (SheafOfModules.unit (𝓡 C)) ≅
      SheafOfModules.unit (𝓡 (TopCat.Sheaf.inverseImageRing g C))) := by
  let C' := TopCat.Sheaf.inverseImageRing g C
  let η : (𝓡 C) ⟶ ((Opens.map g).sheafPushforwardContinuous RingCat.{u}
      (𝓙 T') (𝓙 T)).obj (𝓡 C') := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g) CommRingCat.{u} (𝓙 T') (𝓙 T)).unit.app C)
  let Q := SheafOfModules.pushforward.{u} (F := Opens.map g) η
  obtain ⟨φ, _, _, hφ⟩ := SheafOfModules.moduleInverseImageAdjunction g C
  let se (N : SheafOfModules.{u} (𝓡 C')) : N.sections ≃ (Q.obj N).sections :=
    Equiv.ofBijective ((Opens.map g).op.sectionsPrecomp)
      (Functor.bijective_sectionsPrecomp (Opens.map g).op
        (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}))
  let e (N : SheafOfModules.{u} (𝓡 C')) :
      (TopCat.Sheaf.inverseImageModule g C (SheafOfModules.unit (𝓡 C)) ⟶ N) ≃
        (SheafOfModules.unit (𝓡 C') ⟶ N) :=
    (φ _ N).trans ((Q.obj N).unitHomEquiv.trans ((se N).symm.trans N.unitHomEquiv.symm))
  refine ⟨isoOfHomEquiv _ _ e ?_⟩
  intro N N' k l
  apply N'.unitHomEquiv.injective
  apply (se N').injective
  dsimp only [e, Equiv.trans_apply]
  erw [N'.unitHomEquiv.apply_symm_apply, (se N').apply_symm_apply,
    SheafOfModules.unitHomEquiv_comp_apply, N.unitHomEquiv.apply_symm_apply]
  change (Q.obj N').unitHomEquiv (φ _ N' (k ≫ l)) =
    se N' (SheafOfModules.sectionsMap l ((se N).symm ((Q.obj N).unitHomEquiv (φ _ N k))))
  erw [hφ, SheafOfModules.unitHomEquiv_comp_apply]
  have hs := (se N).apply_symm_apply ((Q.obj N).unitHomEquiv (φ _ N k))
  apply PresheafOfModules.sections_ext
  intro V
  exact congrArg (fun z ↦ l.val.app ((Opens.map g).op.obj V) (z.val V)) hs.symm

/-- The tensor pushout of the affine direct-image algebra is quasi-coherent.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h.
(blueprint: lem-weil-pbc-affine-module-tensor-algebra-quasi-coherent).

Proof: The algebra f_* O_U is quasi-coherent since f is affine. On each affine
open of X it is the tilde of its section algebra. Pulling this algebra to U gives
O_U tensor over f^{-1} O_X with f^{-1}(f_* O_U); pullback of its underlying
quasi-coherent module is quasi-coherent. The pushout universal property identifies
B, with its b action, with this tensor algebra, on pure tensors and hence on the
sheafification. Transfer quasi-coherence along the resulting O_U-module isomorphism.
This uses arbitrary affine morphisms and remains valid for the empty scheme and
zero section rings: the tensor and pushout universal properties hold there too. -/
theorem affine_module_tensor_algebra_quasiCoherent [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (hpush : IsPushout r₀ t₀ b t) :
    (Scheme.CommAlgebraSheaf.toModule (Under.mk b)).IsQuasicoherent := by
  classical
  let G := SheafOfModules.unit (𝓡 A)
  have hG : ((S).obj G).IsQuasicoherent := by
    let := IsSeparated.of_isAffineHom f
    have : (SheafOfModules.unit U.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit.{u, u, u}
    exact isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f
      (SheafOfModules.unit U.ringCatSheaf)
  let : ((S).obj G).IsQuasicoherent := hG
  let e : tensorPullback f ≅ pullback f :=
    (adj₀).leftAdjointUniq (pullbackPushforwardAdjunction f)
  have hT : ((tensorPullback f).obj ((S).obj G)).IsQuasicoherent :=
    (qU).prop_of_iso (e.app ((S).obj G)).symm (by infer_instance)
  obtain ⟨P, pobj, κ, _, _⟩ := affine_module_tensor_baseChange f B b t hpush
  have hP : ((SheafOfModules.restrictScalars (𝓻 b)).obj (P.obj G)).IsQuasicoherent :=
    (qU).prop_of_iso (κ.app G).symm hT
  obtain ⟨i⟩ := inverseImage_unit_iso f.base A
  obtain ⟨j⟩ := changeOfRings_unit_iso IA B t
  obtain ⟨E, hE, _, _⟩ :=
    SheafOfModules.exists_changeOfRingsAdjunction U.toTopCat IA B t
  let k : P.obj G ≅ SheafOfModules.unit (𝓡 B) :=
    eqToIso (pobj G) ≪≫ (eqToIso (hE (I G))).symm ≪≫ E.mapIso i ≪≫
      eqToIso (hE _) ≪≫ j
  exact (qU).prop_of_iso ((SheafOfModules.restrictScalars (𝓻 b)).mapIso k) hP

end
end AlgebraicGeometry.Scheme.Modules
