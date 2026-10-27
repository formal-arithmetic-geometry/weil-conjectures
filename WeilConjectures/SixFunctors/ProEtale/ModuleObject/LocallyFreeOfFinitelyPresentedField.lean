/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
public import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-!
# Locally finitely presented module objects over the field coefficients are locally free

On a scheme `Z` with noetherian underlying space, a pro-étale locally finitely presented module
object over `ℚ̲̄_ℓ,Z` (resp. over `E̲_Z` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`) is locally
free (`ProEtale.CondensedRing.isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace`,
`ProEtale.CondensedRing.ContinuousMapRingObj.isLocallyFree_of_isLocallyFinitelyPresented`): these
are the lisse sheaves of Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 6.8.6.
They are restatements of `condensedQbar_lfp_locally_free` and
`exists_finiteFree_cover_of_condensedField_lfp` for the coefficient rings
`Profinite.padicAlgClRingObj ℓ` and `Profinite.continuousMapRingObj E`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj Limits

/-- Restriction of scalars along an isomorphism of ring objects of pro-étale abelian sheaves
preserves free module objects of finite rank. -/
private lemma isFree_comap {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S} (h : Mod.IsFree S M) :
    Mod.IsFree R ((Mod.comap φ).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  exact ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫ Mod.finiteFreeIsoComap φ n⟩⟩

/-- A module object is free if its restriction of scalars along an isomorphism of ring objects
is free. -/
private lemma isFree_of_isFree_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree S M := by
  obtain ⟨n, ⟨e⟩⟩ := isFree_comap (inv φ) h
  exact ⟨n, ⟨(((Mod.comapComp (inv φ) φ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
    Mod.comapId S).app M).symm ≪≫ e⟩⟩

/-- Pro-étale local finite presentation is preserved by restriction of scalars along an
isomorphism of ring objects. -/
private lemma isLocallyFinitelyPresented_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented S M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨𝒰, h⟩ := h
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨n, m, f, ⟨e⟩⟩ := (h i).comap ((upperStar Ab.{u + 1} (𝒰.f i)).map φ)
  exact ⟨n, m, f, ⟨((upperStar Ab.{u + 1} (𝒰.f i)).mapModComapIso φ).app M ≪≫ e⟩⟩

/-- Local freeness is preserved by restriction of scalars along an isomorphism of ring
objects. -/
private lemma IsLocallyFree.comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S} (h : IsLocallyFree S M) :
    IsLocallyFree R ((Mod.comap φ).obj M) := by
  obtain ⟨𝒰, h⟩ := h
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := isFree_comap ((upperStar Ab.{u + 1} (𝒰.f i)).map φ) (h i)
  exact ⟨n, ⟨((upperStar Ab.{u + 1} (𝒰.f i)).mapModComapIso φ).app M ≪≫ e⟩⟩

/-- Local freeness is invariant under isomorphism of module objects. -/
private lemma IsLocallyFree.of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (h : IsLocallyFree R M)
    (e : M ≅ N) : IsLocallyFree R N := by
  obtain ⟨𝒰, h⟩ := h
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e'⟩⟩ := h i
  exact ⟨n, ⟨((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).mapIso e.symm ≪≫ e'⟩⟩

end AlgebraicGeometry.ProEtale

namespace Profinite

open Opposite

/-- The condensed ring `C(-, E)` is isomorphic to the condensed ring `C(-, ULift E)` of
continuous maps into the universe lift of `E`. -/
private noncomputable def continuousMapRingSheafIsoULift (E : Type) [TopologicalSpace E]
    [Ring E] [IsTopologicalRing E] :
    continuousMapRingSheaf.{u} E ≅ continuousCoefficientRingSheaf (ULift.{u} E) where
  hom := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((ULift.ringEquiv.symm : E ≃+* ULift.{u} E).toRingHom.compLeftContinuous
        S.unop continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  inv := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((ULift.ringEquiv : ULift.{u} E ≃+* E).toRingHom.compLeftContinuous
        S.unop continuous_uliftDown).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

end Profinite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- On a scheme with noetherian underlying space, a pro-étale locally finitely presented module
object over `ℚ̲̄_ℓ` is locally free. -/
theorem isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) M) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) M := by
  obtain ⟨𝒰, h𝒰⟩ := condensedQbar_lfp_locally_free ℓ Z M hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  let φ := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) (𝒰.f i)
  obtain ⟨r, ⟨e⟩⟩ := h𝒰 i
  exact isFree_of_isFree_comap (inv φ)
    ⟨r, ⟨((Mod.extendScalarsIsoComapInv φ).app _).symm ≪≫ e⟩⟩

/-- On a scheme with noetherian underlying space, a pro-étale locally finitely presented module
object over `E̲`, for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, is locally free. -/
theorem ContinuousMapRingObj.isLocallyFree_of_isLocallyFinitelyPresented
    (E : FiniteIntermediateField ℓ) (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) Z) M) :
    IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) Z) M := by
  let E' := ULift.{u} E
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (fun _ a b ↦ ULift.ext _ _ (mul_comm a.down b.down))
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (Profinite.continuousMapRingSheafIsoULift E)
  let φ := (upperStarFromPoint Z).map e.hom
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafIsoULift E).hom
  have : IsMonHom φ := inferInstance
  exact (IsLocallyFree.comap φ (exists_finiteFree_cover_of_condensedField_lfp ℓ E' Z
    ((Mod.comap (inv φ)).obj M) (isLocallyFinitelyPresented_comap (inv φ) hM))).of_iso
    (((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId _).app M)

end AlgebraicGeometry.ProEtale.CondensedRing
