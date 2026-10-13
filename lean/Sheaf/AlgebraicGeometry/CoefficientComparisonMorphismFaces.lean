/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientComparisonConstruction

/-! # Coefficient comparison by the composed adjunction

Source: Stacks Project, Tags 02KE, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The concrete coefficient mates commute with every Cech face restriction.
Source: Stacks Project, Tags 02KE and 0097, naturality of the termwise map.
(blueprint: lem-pc-coefficient-comparison-morphism-faces).
Proof: Restriction of sections from an intersection with a deleted index to the
full intersection commutes with restrictAppIso and with the pullback unit.
Thus the explicitly defined section maps commute with the source restriction
and the support restriction on the target. Take mates under the composed
adjunction. Naturality of the hom equivalence on both sides gives equality of
module morphisms after the coefficient restriction. Evaluate on B and use
naturality of the support identifications. Their equality morphisms and the
inclusions of supports compose to the single inclusion displayed here, by
proof irrelevance in the poset of opens. For empty opens the same identities
hold; for an empty tuple family there is no face to check. -/
theorem coefficientComparisonMorphism_faces {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι))
    (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t =
        g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ alternatingCechIntersection V t)) :
    let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
    let H := ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
      tilde.functor Γ(U.toScheme, ⊤) ⋙
      Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
    let M := (Modules.pullback g').obj F
    let W := fun (p : ℕ) (t : Fin (p + 1) ↪o Fin r) ↦
      alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t
    ∀ (p : ℕ) (t : Fin (p + 2) ↪o Fin r) (j : Fin (p + 2)) (B : T'.Opens)
        (s : Γ(H.obj (G.obj (op (alternatingCechIntersection V
          ((Fin.succAboveOrderEmb j).trans t)))), B)),
        (M.presheaf.map (eqToHom (show
          (W (p + 1) t) ⊓ f' ⁻¹ᵁ B = (W (p + 1) t).ι ''ᵁ (((W (p + 1) t).ι ≫ f') ⁻¹ᵁ B) by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι])).op)
          ((coefficientComparisonMorphism f F U (alternatingCechIntersection V t)
              g g' f' w (W (p + 1) t)
              (hW (p + 1) t)).app B
            ((H.map (G.map (homOfLE
              (alternatingCechIntersection_face_le V p t j)).op)).app B s)) =
        M.presheaf.map (homOfLE (inf_le_inf
          (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
            ((M.presheaf.map (eqToHom (show
          (W p ((Fin.succAboveOrderEmb j).trans t)) ⊓ f' ⁻¹ᵁ B =
            (W p ((Fin.succAboveOrderEmb j).trans t)).ι ''ᵁ
              (((W p ((Fin.succAboveOrderEmb j).trans t)).ι ≫ f') ⁻¹ᵁ B) by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι])).op)
              ((coefficientComparisonMorphism f F U
                  (alternatingCechIntersection V ((Fin.succAboveOrderEmb j).trans t))
                  g g' f' w (W p ((Fin.succAboveOrderEmb j).trans t))
                  (hW p
                    ((Fin.succAboveOrderEmb j).trans t))).app B s)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
