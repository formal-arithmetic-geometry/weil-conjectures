/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal

/-!
# Tensor coherence for a Cech pullback functor

Source: Stacks Project, sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-cech-pullback-tensor-coherence).

The tensor comparison and its unit compatibility are isolated here so that the
ordinary-complex assembly can use them as a single piece of data. The tensor
products are the canonical ones, `SheafOfModules.monoidalCategory`, which are
the tensor products of `ringedExtendedCech`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- A natural tensor comparison `F (X ⊗ Y) ≅ F X ⊗ F Y` together with identifications of
`U`, `V` with the tensor units under which `u` is compatible with the comparison at the
unit and the left unitor. -/
structure TensorCoherence {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (U : A) (V : B) (u : F.obj U ≅ V) where
  tensor : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y
  naturality : ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
    F.map (f ⊗ₘ g) ≫ (tensor X' Y').hom =
      (tensor X Y).hom ≫ (F.map f ⊗ₘ F.map g)
  unitA : U ≅ 𝟙_ A
  unitB : V ≅ 𝟙_ B
  unit : (tensor (𝟙_ A) (𝟙_ A)).hom ≫
      ((F.map unitA.inv ≫ u.hom ≫ unitB.hom) ⊗ₘ
        (F.map unitA.inv ≫ u.hom ≫ unitB.hom)) ≫
      (λ_ (𝟙_ B)).hom =
    F.map (λ_ (𝟙_ A)).hom ≫ F.map unitA.inv ≫ u.hom ≫ unitB.hom

/--
For the canonical tensor products of sheaves of modules, the supplied left adjoint `F` of
`h.modules` carries a tensor comparison normalized at `v`.

Proof. By uniqueness of left adjoints, `F` is isomorphic to the module pullback along `h`,
which preserves tensor products (Stacks 03EL; lem-weil-pbc-ringed-topoi-module-pullback-tensor);
transporting that comparison through the isomorphism gives `tensor`, natural in both variables.
Take `unitA`, `unitB` the identities (`SheafOfModules.unit` is the tensor unit). The canonical
comparison satisfies the unit equation with the canonical unit comparison `v0`; `v = v0 ≫ a`
for an automorphism `a` of the target unit, i.e. a unit global section acting centrally, and
multiplying the tensor comparison by `a⁻¹` keeps it natural and turns the unit equation for
`v0` into the one for `v`.
(blueprint: lem-weil-pbc-cech-pullback-tensor-coherence)
-/
theorem cech_pullback_tensor_coherence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (h : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    [F.PreservesZeroMorphisms] (hF : F ⊣ h.modules)
    (v : F.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :
    Nonempty (@TensorCoherence _ _ _ _
      (SheafOfModules.monoidalCategory R) (SheafOfModules.monoidalCategory S) F
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) v) := by
  sorry

end CategoryTheory
