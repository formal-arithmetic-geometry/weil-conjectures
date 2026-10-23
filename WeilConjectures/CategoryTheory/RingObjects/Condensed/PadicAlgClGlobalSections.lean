/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndSurjective
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections

/-!
# The global sections of the condensed ring `ℚ̲̄_ℓ`

The global sections `𝟙 ⟶ ℚ̲̄_ℓ` of the condensed ring `ℚ̲̄_ℓ` are the constants: the ring
homomorphism `ℚ̄_ℓ →+* Γ ℚ̲̄_ℓ` is surjective (`Profinite.PadicAlgCl.constRingHom_surjective`).
Indeed, a morphism `𝟙 ⟶ ℚ̲̄_ℓ` from the sheafified constant sheaf `ℤ` transposes to a morphism of
presheaves `ℤ ⟶ ℚ̲̄_ℓ`, which is determined by the image of `1` over the point, the point being
terminal among profinite sets.

Consequently the endomorphisms of the regular module `ℚ̲̄_ℓ` form a quotient of the field `ℚ̄_ℓ`,
and it is nonzero: every nonzero endomorphism of the regular module is invertible
(`Profinite.PadicAlgCl.isIso_of_ne_zero_end_regular`), and `𝟙 ≠ 0`
(`Profinite.PadicAlgCl.one_ne_zero_end_regular`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace Profinite.PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Every global section of the condensed ring `ℚ̲̄_ℓ` is constant. -/
theorem constRingHom_surjective : Function.Surjective (constRingHom.{u} ℓ) := by
  intro x
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  let x' := adj.homEquiv _ _
    (inv (Functor.LaxMonoidal.ε (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
      ≫ x.hom)
  let b := x'.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)
  refine ⟨b.down.1 PUnit.unit, ?_⟩
  have hx : x' = (Functor.ringHomΓCompForget₂ (padicAlgClCondensedRing ℓ).obj
      (constSectionRingHom ℓ) (fun _ _ ↦ rfl) (b.down.1 PUnit.unit)).hom := by
    ext S n
    obtain ⟨m⟩ := n
    have key : x'.app S (ULift.up 1) = (padicAlgClRingObj ℓ).obj.map
        (isTerminalPUnit.from S.unop).op b :=
      NatTrans.naturality_apply x' (isTerminalPUnit.from S.unop).op (ULift.up 1)
    have hm : (ULift.up m : ULift.{u + 1} ℤ) = m • ULift.up 1 := by
      ext
      simp
    refine (congrArg (x'.app S) hm).trans ?_
    rw [map_zsmul, key]
    exact (zsmul_eq_mul (α := (padicAlgClRingPresheaf ℓ).obj S) _ m).trans rfl
  ext1
  rw [constRingHom, Sheaf.ringHomΓSheafCompose, RingHom.comp_apply, RingHom.comp_apply,
    Γ.map_hom, Γ.mapFunctor_hom, ← hx, Category.assoc, Sheaf.sheafifyRingPresheafIso, asIso_hom,
    ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc]

/-- The identity of the regular module `ℚ̲̄_ℓ` is not zero: the sections of `ℚ̲̄_ℓ` over the point
form the nonzero ring `ℚ̄_ℓ`. -/
theorem one_ne_zero_end_regular :
    (1 : End (Mod.regular (padicAlgClRingObj.{u} ℓ))) ≠ 0 := by
  intro h
  have h1 : 𝟙 (padicAlgClRingObj.{u} ℓ) = 0 := congrArg Mod.Hom.hom h
  exact one_ne_zero (α := ULift.{u + 1}
    (_root_.PadicAlgCl.finiteIntermediateFieldValued ℓ (Profinite.of PUnit.{u + 1})))
    (congrArg (fun φ ↦ φ.hom.app (op (Profinite.of PUnit.{u + 1}))
      (1 : (padicAlgClRingPresheaf.{u} ℓ).obj (op (Profinite.of PUnit.{u + 1})))) h1)

/-- Every nonzero endomorphism of the regular module `ℚ̲̄_ℓ` is invertible: the endomorphisms are
the multiplications by the constants `ℚ̄_ℓ`, a field. -/
theorem isIso_of_ne_zero_end_regular (t : End (Mod.regular (padicAlgClRingObj.{u} ℓ)))
    (ht : t ≠ 0) : IsIso t :=
  isIso_of_ne_zero_of_surjective (Mod.regularEndRingHom.comp (constRingHom.{u} ℓ))
    (Mod.regularEndRingHom_surjective.comp (constRingHom_surjective ℓ)) t ht

end Profinite.PadicAlgCl
