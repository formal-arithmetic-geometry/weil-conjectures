/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare

/-! # Restricted composition through nested overlap inclusions -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restricted composition through the nested overlap inclusions.
Source: Stacks Project, Tag 08DW. Compose the nested restricted square with the
restricted map to the larger open, then use restricted composition.
(blueprint: lem-pc-perfect-overlap-tail-restricted-composite). -/
theorem perfectOverlapTailRestrictedComposite
    {X Y K : Scheme.{u}} (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y)
    (hgf : gk ≫ f = g) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    let hT : g ⁻¹ᵁ (U ⊓ V) ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ (U ⊓ V)) :=
      le_of_eq (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ (U ⊓ V)) hgf.symm)
    let iX : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
    let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
    gk.resLE (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) hT ≫
        (K.homOfLE (leOfHom iK) ≫ (f ∣_ L)) =
      X.homOfLE (leOfHom iX) ≫ (g ∣_ L) := by
  intro hT iX iK
  let hP : g ⁻¹ᵁ L ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ L) :=
    le_of_eq (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ L) hgf.symm)
  have hj : gk.resLE (f ⁻¹ᵁ L) (g ⁻¹ᵁ L) hP ≫ (f ∣_ L) = g ∣_ L := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
  rw [← Category.assoc,
    perfectOverlapNestedRestrictedMaps gk iK iX hP hT, Category.assoc,
    hj]

end AlgebraicGeometry
