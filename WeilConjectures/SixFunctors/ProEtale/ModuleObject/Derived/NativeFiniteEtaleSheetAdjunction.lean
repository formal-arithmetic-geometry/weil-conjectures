/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleSheetTrace

/-! # The adjunction determined by a nondegenerate native sheet trace -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private def adjunction_of_bijective_counit
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (τ : G ⋙ F ⟶ 𝟭 D)
    (h : ∀ (M : C) (P : D),
      Function.Bijective (fun f : M ⟶ G.obj P ↦ F.map f ≫ τ.app P)) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv M P := (Equiv.ofBijective _ (h M P)).symm
      homEquiv_naturality_left_symm := by
        intro M' M P f g
        change F.map (f ≫ g) ≫ τ.app P = F.map f ≫ (F.map g ≫ τ.app P)
        rw [F.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro M P P' f g
        have he (Q : D) (v : F.obj M ⟶ Q) :
            F.map ((Equiv.ofBijective _ (h M Q)).symm v) ≫ τ.app Q = v :=
          (Equiv.ofBijective _ (h M Q)).apply_symm_apply v
        apply (h M P').injective
        change F.map ((Equiv.ofBijective _ (h M P')).symm (f ≫ g)) ≫ τ.app P' =
          F.map ((Equiv.ofBijective _ (h M P)).symm f ≫ G.map g) ≫ τ.app P'
        rw [he, F.map_comp, Category.assoc]
        have hn := τ.naturality g
        dsimp only [Functor.comp_map, Functor.id_map] at hn
        rw [hn, ← Category.assoc, he] }

private theorem adjunction_of_bijective_counit_eq
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (τ : G ⋙ F ⟶ 𝟭 D)
    (h : ∀ (M : C) (P : D),
      Function.Bijective (fun f : M ⟶ G.obj P ↦ F.map f ≫ τ.app P)) :
    (adjunction_of_bijective_counit F G τ h).counit = τ := by
  ext P
  change F.map (𝟙 (G.obj P)) ≫ τ.app P = τ.app P
  rw [F.map_id, Category.id_comp]

/-- A nondegenerate sheet trace gives the required adjunction with its exact
counit, rather than merely an unnormalized existence assertion.
Source: the natural Hom bijection determined by a counit.
(blueprint: new-det-sp-native-finite-etale-sheet-adjunction).
Proof. Use the inverse of the specified trace pairing as the Hom equivalence.
Functoriality and trace naturality give its two naturality identities. Evaluation
at the identity gives precisely the descended trace as counit. -/
theorem nativeFiniteEtaleSheetAdjunction_of_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (h : ∀
      (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
      (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      Function.Bijective (fun f : M ⟶ (upperStar Λ p).obj P ↦
        (lowerStar Λ p).map f ≫ nativeFiniteEtaleSheetTrace Λ p P)) :
    ∃ b : lowerStar Λ p ⊣ upperStar Λ p,
      b.counit = nativeFiniteEtaleSheetTraceNat Λ p := by
  exact ⟨adjunction_of_bijective_counit _ _ (nativeFiniteEtaleSheetTraceNat Λ p) h,
    adjunction_of_bijective_counit_eq _ _ (nativeFiniteEtaleSheetTraceNat Λ p) h⟩

end AlgebraicGeometry.ProEtale.CondensedRing
