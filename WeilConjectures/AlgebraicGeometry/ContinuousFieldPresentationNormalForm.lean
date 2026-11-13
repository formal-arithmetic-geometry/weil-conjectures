/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix

import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm

/-!
# Local freeness of cokernels of continuous matrices of locally constant rank

## References

* Hemo–Richarz–Scholbach, Example 3.1
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A continuous finite presentation of locally constant rank is locally an identity
block and a zero block, up to isomorphisms of its source and target (Hemo–Richarz–Scholbach,
Example 3.1). -/
theorem exists_cover_continuousField_presentation_normalForm
    (E : Type u) [NormedField E] (V : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (hr : IsLocallyConstant (fun v : V ↦
      ((continuousFieldPresentationMatrix E V e f).map (fun a ↦ a v)).rank)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage V, ∀ i : C.I₀,
      ∃ (r s t : ℕ)
        (a : ((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R).obj
            (Mod.finiteFree R m) ≅
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R) r ⊞
            Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R) s)
        (b : ((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R).obj
            (Mod.finiteFree R n) ≅
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R) r ⊞
            Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R) t),
        ((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R).map f =
          a.hom ≫ biprod.map (𝟙 _) 0 ≫ b.inv := by
  classical
  let M := continuousFieldPresentationMatrix E V e f
  have hm (x : V) := continuousField_exists_isOpen_eq_mul_of_locallyConstant M hr x
  choose r U ρ γ hρ hγ hU hx hmat using hm
  let O (x : V) : V.Opens := ⟨U x, hU x⟩
  have hcover : Presieve.ofArrows (fun x ↦ (O x).toScheme) (fun x ↦ (O x).ι) ∈
      Scheme.proetalePrecoverage V :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2
        ⟨fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩, fun _ ↦ inferInstance⟩)
  let C : Scheme.Cover.{u} Scheme.proetalePrecoverage V :=
    { I₀ := V, X := fun x ↦ (O x).toScheme, f := fun x ↦ (O x).ι, mem₀ := hcover }
  refine ⟨C, fun x ↦ ?_⟩
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := hmat x
    (⟨(O x).ι.base.hom, (O x).ι.continuous⟩ : C((O x).toScheme, V))
    (by rintro _ ⟨z, rfl⟩; exact z.2)
  obtain ⟨s, t, a, b, hab⟩ := continuousField_matrix_sheaf_normalForm E R e f
    (O x).ι (r x) (ρ x) (γ x) (hρ x) (hγ x) P Q hP hQ hPQ
  exact ⟨r x, s, t, a, b, hab⟩

end AlgebraicGeometry.ProEtale
