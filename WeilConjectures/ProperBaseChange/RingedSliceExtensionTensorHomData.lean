/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! The Hom-equivalence data for the ringed-slice tensor projection formula. -/

@[expose] public section


universe uC u v

open CategoryTheory

namespace SheafOfModules

namespace RingedSliceTensor

section HomData

universe vD vE vB vK uD uE uB uK
variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {B : Type uB} [Category.{vB} B] {K : Type uK} [Category.{vK} K]

-- Compose Hom equivalences without unfolding their constructions in the naturality proofs.
private structure HomData (A : D ⥤ B) (T : E ⥤ B) (A' : D ⥤ K) (T' : E ⥤ K) where
  equiv : ∀ X H, ((A).obj X ⟶ T.obj H) ≃ (A'.obj X ⟶ T'.obj H)
  post : ∀ X H H' (f : (A).obj X ⟶ T.obj H) (h : H ⟶ H'),
    equiv X H' (f ≫ T.map h) = equiv X H f ≫ T'.map h
  pre : ∀ X X' H (g : X ⟶ X') (f : (A).obj X' ⟶ T.obj H),
    equiv X H (A.map g ≫ f) = A'.map g ≫ equiv X' H f

@[irreducible] private noncomputable def HomData.trans
    {V : Type*} [Category* V] {A : D ⥤ B} {T : E ⥤ B}
    {A' : D ⥤ K} {T' : E ⥤ K} {A'' : D ⥤ V} {T'' : E ⥤ V}
    (a : HomData A T A' T') (b : HomData A' T' A'' T'') : HomData A T A'' T'' where
  equiv X H := (a.equiv X H).trans (b.equiv X H)
  post X H H' f h := by
    change b.equiv _ _ (a.equiv _ _ _) = _
    rw [a.post, b.post]
    rfl
  pre X X' H g f := by
    change b.equiv _ _ (a.equiv _ _ _) = _
    rw [a.pre, b.pre]
    rfl

@[irreducible] private noncomputable def HomData.symm
    {A : D ⥤ B} {T : E ⥤ B} {A' : D ⥤ K} {T' : E ⥤ K}
    (a : HomData A T A' T') : HomData A' T' A T where
  equiv X H := (a.equiv X H).symm
  post X H H' f h := by
    apply (a.equiv X H').injective
    rw [a.post, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  pre X X' H g f := by
    apply (a.equiv X H).injective
    rw [a.pre, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[irreducible] private noncomputable def HomData.adj (L : B ⥤ K) (Q : K ⥤ B) (adj : L ⊣ Q)
    (A : D ⥤ B) (T : E ⥤ K) : HomData (A ⋙ L) T A (T ⋙ Q) where
  equiv X H := adj.homEquiv ((A).obj X) (T.obj H)
  post _ _ _ f h := adj.homEquiv_naturality_right f (T.map h)
  pre _ _ _ g f := adj.homEquiv_naturality_left (A.map g) f

@[irreducible] private noncomputable def HomData.iso {A A' : D ⥤ B} (a : A ≅ A') (T : E ⥤ B) :
    HomData A T A' T where
  equiv X H := (a.app X).homCongr (Iso.refl _)
  post X H H' f h := by simp [Iso.homCongr, Category.assoc]
  pre X X' H g f := by
    change a.inv.app X ≫ (A.map g ≫ f) ≫ 𝟙 _ =
      A'.map g ≫ a.inv.app X' ≫ f ≫ 𝟙 _
    simp only [Category.comp_id]
    exact a.inv.naturality_assoc g f |>.symm

end HomData

section
variable {R : Type (max u v)} [CommRing R] {ι : Type v} [DecidableEq ι]
  {M : ι → Type (max u v)} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {N P : Type (max u v)} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
-- Keep the direct-sum/tensor construction behind its generator formula.
end


-- The explicit adjunction from LocalizedModuleAdjunctionExact, with independent
-- object and coefficient universes. No exactness or precoverage hypotheses are needed.
section RawTensor

open Opposite MonoidalCategory

variable {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  (R : Sheaf J CommRingCat.{max u v}) (U : C)

set_option backward.isDefEq.respectTransparency false

set_option hygiene false in
local notation "A" => (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R

variable (F : SheafOfModules.{max u v} ((A).over U)) (G H : SheafOfModules.{max u v} A)

end RawTensor

section SheafifyTensor

open Opposite MonoidalCategory

variable {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v}) (U : C)

set_option backward.isDefEq.respectTransparency false

set_option hygiene false in
local notation "A" => (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R

variable [Presheaf.IsLocallyInjective J (𝟙 (A).obj)]
  [Presheaf.IsLocallySurjective J (𝟙 (A).obj)]

end SheafifyTensor

end RingedSliceTensor

end SheafOfModules
