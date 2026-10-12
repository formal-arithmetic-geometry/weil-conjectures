/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Identification of the glued twist with the Serre twist

Source: Stacks Project, Constructions, Section 01MM and Lemma 01MS;
Sheaves, Section 00AK and Lemma 00AL
(blueprint: lem-weil-pbc-projective-space-twist-glued-identification).

`P = Proj ℤ[T_k : k ∈ n]` is the integral model `Proj (homogeneousSubmodule n (ULift ℤ))`.
The glued module `𝒪_P(1)` of def-pc-projective-space-twist (A = ℤ, d = 1) is its recorded
declaration `ProjectiveSpace.twist n (Spec ℤ) 1` on `ℙ(n; Spec ℤ)`, carried to `P` along the
projection `ProjectiveSpace.toProjInt` (an isomorphism, the base being `Spec ℤ`) by
`Scheme.Modules.pushforward`. Its chart bases are `e_i = T^gl_i|_{U_i}` and its global
coordinate sections are `T^gl_k = ProjectiveSpace.twistOneSection n (Spec ℤ) k`, which satisfy
the transition rule `e_i = (T_i/T_j) e_j` and `T^gl_k|_{U_i} = (T_k/T_i) e_i`
(`ProjectiveSpace.pullbackSection_twistOneSection_map_eq_smul`).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Morphisms agree if they agree on global sections whose restrictions form local frames.
On each intersection with a frame chart, express a section as a scalar multiple of the
restricted frame, use linearity and naturality, and apply sheaf separation. -/
private theorem hom_ext_of_global_frames {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type u} (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (t : ι → Γ(M, ⊤))
    (ht : ∀ i, Scheme.Modules.IsFreeGenerator
      (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (t i)))
    (g₁ g₂ : M ⟶ N) (hagree : ∀ i, g₁.app ⊤ (t i) = g₂.app ⊤ (t i)) : g₁ = g₂ := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ U i) V (fun _ ↦ homOfLE inf_le_left) (fun x hx ↦ ?_) _ _
    (fun i ↦ ?_)
  · have hx' : x ∈ ⨆ i, U i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · obtain ⟨a, ha⟩ := ((ht i).map (inf_le_right : V ⊓ U i ≤ U i)).exists_smul_eq
      (M.presheaf.map (homOfLE inf_le_left).op s)
    rw [← Scheme.Modules.Hom.app_presheaf_map g₁,
      ← Scheme.Modules.Hom.app_presheaf_map g₂, ← ha,
      Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
      Scheme.Modules.Hom.app_presheaf_map g₁, Scheme.Modules.Hom.app_presheaf_map g₂,
      Scheme.Modules.Hom.app_presheaf_map g₁, Scheme.Modules.Hom.app_presheaf_map g₂,
      hagree]

/-- The glued O(1) has a unique isomorphism to the Serre twist preserving its chart bases;
the isomorphism carries the glued coordinate sections to the polynomial coordinate sections.
Source: Stacks Project, Constructions 01MS and Sheaves 00AL
(blueprint: lem-weil-pbc-projective-space-twist-glued-identification).

Proof: Over `Spec (ULift ℤ)`, the projection `toProjInt` is an isomorphism. The glued
module is defined as the pullback of the Serre twist, so the pullback-pushforward
adjunction unit is an isomorphism; its inverse is the required comparison. By definition,
each glued coordinate section is the image under this unit of the polynomial section.
The inverse identity therefore proves global compatibility. Naturality and the pointwise
fraction formulas prove chart compatibility. For uniqueness, precompose with the unit.
The resulting morphisms agree on the polynomial coordinate sections. Their restrictions
are free generators on the standard chart cover, so linearity, naturality and sheaf
separation prove equality on every open. Cancel the unit to conclude uniqueness. -/
theorem existsUnique_polynomial_twist_glued_identification
    (n : Type u) [Finite n] [Nonempty n] :
    ∃! θ : (Scheme.Modules.pushforward
          (ProjectiveSpace.toProjInt n (Spec (CommRingCat.of (ULift.{u} ℤ))))).obj
          (ProjectiveSpace.twist n (Spec (CommRingCat.of (ULift.{u} ℤ))) 1) ≅
        Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1,
      (∀ i : n,
        θ.hom.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
            (MvPolynomial.X i))
          ((ProjectiveSpace.twist n (Spec (CommRingCat.of (ULift.{u} ℤ))) 1).presheaf.map
            (homOfLE (le_top :
              ProjectiveSpace.toProjInt n (Spec (CommRingCat.of (ULift.{u} ℤ))) ⁻¹ᵁ
                Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
                  (MvPolynomial.X i) ≤ ⊤)).op
            (ProjectiveSpace.twistOneSection n (Spec (CommRingCat.of (ULift.{u} ℤ))) i)) =
          Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)) ∧
      (∀ k : n,
        θ.hom.app ⊤
            (ProjectiveSpace.twistOneSection n (Spec (CommRingCat.of (ULift.{u} ℤ))) k) =
          (Proj.unitToTwist (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)).app ⊤
            (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)), ⊤))) := by
  classical
  let S := Spec (CommRingCat.of (ULift.{u} ℤ))
  let A := MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)
  let f := ProjectiveSpace.toProjInt n S
  let M := Proj.twist A 1
  have : IsIso (CategoryTheory.Limits.terminal.from S) := by
    exact ⟨⟨specULiftZIsTerminal.from _, specULiftZIsTerminal.hom_ext _ _,
      CategoryTheory.Limits.terminal.hom_ext _ _⟩⟩
  have : IsIso f := by
    dsimp [f, ProjectiveSpace.toProjInt]
    infer_instance
  have := (Scheme.Modules.pullbackPushforwardAdjunction f).isIso_unit_of_iso
    (Functor.isoWhiskerRight (Scheme.Modules.pullbackIsoPushforwardInv f)
      (Scheme.Modules.pushforward f) ≪≫
      Scheme.Modules.pushforwardComp _ _ ≪≫
      Scheme.Modules.pushforwardCongr (by simp) ≪≫ Scheme.Modules.pushforwardId _)
  let η : M ⟶ (Scheme.Modules.pushforward f).obj (ProjectiveSpace.twist n S 1) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  let θ : (Scheme.Modules.pushforward f).obj (ProjectiveSpace.twist n S 1) ≅ M :=
    (asIso η).symm
  have hglobal (k : n) : θ.hom.app ⊤ (ProjectiveSpace.twistOneSection n S k) =
      (Proj.unitToTwist (𝒜 := A) (d := 1) (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)).app ⊤
        (1 : Γ(Proj A, ⊤)) := by
    change (inv η).app ⊤ (η.app ⊤ _) = _
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      IsIso.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have hchart (i : n) : θ.hom.app (Proj.basicOpen A (MvPolynomial.X i))
      ((ProjectiveSpace.twist n S 1).presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ Proj.basicOpen A (MvPolynomial.X i) ≤ ⊤)).op
        (ProjectiveSpace.twistOneSection n S i)) =
      Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) := by
    change θ.hom.app (Proj.basicOpen A (MvPolynomial.X i))
      (((Scheme.Modules.pushforward f).obj (ProjectiveSpace.twist n S 1)).presheaf.map
        (homOfLE le_top).op (ProjectiveSpace.twistOneSection n S i)) = _
    rw [Scheme.Modules.Hom.app_presheaf_map θ.hom, hglobal]
    apply Subtype.ext
    funext x
    apply Subtype.ext
    change (((Proj.unitToTwist (𝒜 := A) (d := 1)
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)).app ⊤
      (1 : Γ(Proj A, ⊤))).1 ⟨x.1, trivial⟩ :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
    rw [Proj.val_unitToTwist_app_top, Proj.val_twistPowSection_apply]
    simp
    rfl
  refine ⟨θ, ⟨hchart, hglobal⟩, ?_⟩
  intro θ' hθ'
  apply Iso.ext
  apply (cancel_epi η).mp
  let g₁ : M ⟶ M := η ≫ θ'.hom
  let g₂ : M ⟶ M := η ≫ θ.hom
  let t (k : n) : Γ(M, ⊤) :=
    (Proj.unitToTwist (𝒜 := A) (d := 1) (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)).app ⊤
      (1 : Γ(Proj A, ⊤))
  have hagree (k : n) : Scheme.Modules.Hom.app (X := Proj A) g₁ ⊤ (t k) =
      Scheme.Modules.Hom.app (X := Proj A) g₂ ⊤ (t k) := by
    exact (hθ'.2 k).trans (hglobal k).symm
  let U (i : n) := Proj.basicOpen A (MvPolynomial.X i)
  have hcover : (⨆ i, U i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' A (MvPolynomial.X : n → MvPolynomial n (ULift.{u} ℤ))
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i⟩)
      (MvPolynomial.adjoin_range_X_eq_top n (ULift.{u} ℤ))
  apply hom_ext_of_global_frames (X := Proj A) U hcover t ?_ g₁ g₂ hagree
  intro i
  have hpoly : M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (t i) =
      Proj.twistPowSection (𝒜 := A) 1
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    change (((Proj.unitToTwist (𝒜 := A) (d := 1)
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)).app ⊤
        (1 : Γ(Proj A, ⊤))).1 ⟨x.1, trivial⟩ :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
    rw [Proj.val_unitToTwist_app_top, Proj.val_twistPowSection_apply]
    simp
    rfl
  rw [hpoly]
  exact Proj.isFreeGenerator_twistPowSection (𝒜 := A) 1 _

end AlgebraicGeometry.Proj
