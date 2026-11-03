/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.CategoryTheory.Monoidal.Conjugate

/-!
# Monoidal pullback and restriction along a pro-etale object

Source: Stacks Project, Pro-etale Cohomology, Tag 098T; Sites and Sheaves,
Tags 00Y0 and 03EH; Modules on Sites, Section 03DH
(blueprint: lem-sfb-proetale-object-pullback-restriction).

All restrictions below are the existing sectionwise pushforward along composition
of site objects. Its lax maps are those induced by objectwise tensor followed by
sheafification. The pullback comparison is the existing canonical adjunction comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pullback along a site object is sectionwise restriction, monoidally, and the
canonical restriction tensor and unit maps are invertible.
Source: Stacks Tags 098T and 00Y0
(blueprint: lem-sfb-proetale-object-pullback-restriction).

Proof: the distinguished initial Kan index identifies the sheafified left Kan
extension with restriction. Under this identification its adjunction unit at T is
restriction along T ×_Y W → T. The oplax tensor map is the mate of the pushforward
lax tensor map after the two units. Both sides of the monoidal comparison equation
send a pure tensor a ⊗ b to the sheafification image of the restricted a ⊗ b.
These tensors generate the presheaf tensor, and maps out of sheafification are
uniquely determined there. The unit calculation sends 1 to 1. The mate bijection
therefore gives both monoidal equations. Restriction commutes with sheafification
on the localized site and with objectwise tensor, so its comparison maps are
invertible. Finally composition of site objects gives the displayed section formula,
including at the final object W → W.
-/
theorem proEtaleObjectPullbackRestriction (Y : Scheme.{u}) (W : Y.ProEt) :
    NatTrans.IsMonoidal (upperStarIsoSheafPushforward Ab.{u + 1} W.hom W.prop).hom ∧
    IsIso (Functor.LaxMonoidal.ε
      (@Functor.sheafPushforwardContinuous W.left.ProEt _ Y.ProEt _
        (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop) Ab.{u + 1} _
        (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.isContinuous_overMap W.prop))) ∧
    (∀ F G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1},
      IsIso (Functor.LaxMonoidal.μ
        (@Functor.sheafPushforwardContinuous W.left.ProEt _ Y.ProEt _
          (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop) Ab.{u + 1} _
          (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
          (Scheme.ProEt.isContinuous_overMap W.prop)) F G)) ∧
    (∀ (F : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (V : W.left.ProEt),
      ((localizationRestriction Ab.{u + 1} W.hom W.prop).obj F).obj.obj (op V) =
        F.obj.obj (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj V))) := by
  let e := upperStarIsoSheafPushforward Ab.{u + 1} W.hom W.prop
  refine ⟨inferInstance, ?_, ?_, fun _ _ ↦ rfl⟩
  · have hi : IsIso (Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} W.hom) ≫
        e.hom.app (𝟙_ _)) := inferInstance
    exact (NatTrans.IsMonoidal.unit (τ := e.hom)) ▸ hi
  · intro F G
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) F G
    have hi : IsIso ((e.hom.app F ⊗ₘ e.hom.app G) ≫
        Functor.LaxMonoidal.μ _ F G) := by
      rw [← h]
      infer_instance
    exact @IsIso.of_isIso_comp_left _ _ _ _ _
      (e.hom.app F ⊗ₘ e.hom.app G) _ inferInstance hi

end AlgebraicGeometry.ProEtale
