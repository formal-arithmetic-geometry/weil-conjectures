/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections

/-!
# The global sections of the condensed ring `ℚ̲̄_ℓ`

The global sections `Γ ℚ̲̄_ℓ = (𝟙 ⟶ ℚ̲̄_ℓ)` of the condensed ring `ℚ̲̄_ℓ` are the constant ones: the
ring homomorphism `ℚ̄_ℓ →+* Γ ℚ̲̄_ℓ` (`Profinite.PadicAlgCl.constRingHom`) is surjective
(`Profinite.PadicAlgCl.constRingHom_surjective`). Indeed a global section of a condensed abelian
group `G` is determined by its value at the point `*` (`Profinite.hom_ext_of_ε_comp_app_one`):
the monoidal unit of condensed abelian groups is the sheafification of the constant presheaf
`ℤ`, and `*` is terminal among profinite sets. The value at `*` of a global section of `ℚ̲̄_ℓ`
is an element of `ℚ̲̄_ℓ(*) = ℚ̄_ℓ`. In particular the nonzero global sections of `ℚ̲̄_ℓ` are
units (`Profinite.PadicAlgCl.isUnit_of_ne_zero`).
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Opposite

namespace CategoryTheory.Sheaf

attribute [local instance] Sheaf.monoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})]
  (S : Sheaf J RingCat.{w}) {R : Type*} [Ring R]

/-- On underlying presheaves, after the unit `ε : 𝟙 ⟶ (𝟙 : Sheaf J Ab).val`, the global section
`ringHomΓSheafCompose J S φ hφ r` of the sheaf of rings `S` is the global section
`n ↦ n • φ X r` of the underlying presheaf of rings. -/
lemma ε_comp_ringHomΓSheafCompose_hom (φ : ∀ X, R →+* S.obj.obj X)
    (hφ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R), S.obj.map f (φ X r) = φ Y r) (r : R) :
    ε (sheafToPresheaf J Ab.{w}) ≫
        (sheafToPresheaf J Ab.{w}).map (ringHomΓSheafCompose J S φ hφ r).hom =
      (S.obj.ringHomΓCompForget₂ φ hφ r).hom := by
  have e (G : Sheaf J Ab.{w}) (c : 𝟙_ (Sheaf J Ab.{w}) ⟶ G) :
      ((sheafificationAdjunction J Ab.{w}).homEquiv _ _).symm
        (ε (sheafToPresheaf J Ab.{w}) ≫ (sheafToPresheaf J Ab.{w}).map c) =
        Functor.OplaxMonoidal.η (presheafToSheaf J Ab.{w}) ≫ c := by
    rw [Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact Equiv.symm_apply_apply _ _
  apply ((sheafificationAdjunction J Ab.{w}).homEquiv _ _).symm.injective
  rw [e, Adjunction.homEquiv_counit]
  simp [ringHomΓSheafCompose, sheafifyRingPresheafIso, Functor.Monoidal.η_ε_assoc]

end CategoryTheory.Sheaf

namespace Profinite

open Functor.LaxMonoidal

/-- A morphism of abelian presheaves on profinite sets out of the monoidal unit (the constant
presheaf `ℤ`) is determined by the image of `1` at the point. -/
lemma natTrans_ext_of_app_one {P : Profinite.{u}ᵒᵖ ⥤ Ab.{w}}
    {t s : 𝟙_ (Profinite.{u}ᵒᵖ ⥤ Ab.{w}) ⟶ P}
    (h : t.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1) =
      s.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) : t = s := by
  have key (t : 𝟙_ (Profinite.{u}ᵒᵖ ⥤ Ab.{w}) ⟶ P) (X : Profinite.{u}ᵒᵖ) (n : ULift.{w} ℤ) :
      t.app X n = n.down • P.map (isTerminalPUnit.from X.unop).op
        (t.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) := by
    have hn : n = n.down • (ULift.up 1 : ULift.{w} ℤ) := by
      ext
      simp
    conv_lhs => rw [hn, map_zsmul]
    rw [← NatTrans.naturality_apply]
    rfl
  ext X n
  rw [key t, key s, h]

end Profinite
