/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom

/-! # Naturality of the specified exceptional Hom chain

Source: blueprint det-def-sf-operations (vi), thm-sf-ambient-adjoint-class (2).
(blueprint: lem-sf-specified-exceptional-hom-naturality).

The naturality equations compare arbitrary retained etale origins, so their identity
specialization proves independence of the witness. No ambient pro-etale adjunction
is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem transpose_left
    {E₀ E₁ C₀ C₁ : Type*} [Category* E₀] [Category* E₁]
    [Category* C₀] [Category* C₁]
    (A : E₀ ⥤ C₀) (B : E₁ ⥤ C₁) (U : C₁ ⥤ E₁)
    (F : E₀ ⥤ E₁) (R : E₁ ⥤ E₀) (I : C₀ ⥤ C₁)
    (ad : F ⊣ R) (bd : B ⊣ U)
    {L L' : E₀} {M M' : C₀} {N : C₁}
    (a : A.obj L ≅ M) (a' : A.obj L' ≅ M')
    (v : B.obj (F.obj L) ⟶ I.obj (A.obj L))
    (v' : B.obj (F.obj L') ⟶ I.obj (A.obj L'))
    (s : M ⟶ M') (b : I.obj M' ⟶ N) (t : L ⟶ L')
    (ht : A.map t = a.hom ≫ s ≫ a'.inv)
    (hv : B.map (F.map t) ≫ v' = v ≫ I.map (A.map t)) :
    a.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v ≫ I.map a.hom ≫ I.map s ≫ b))) =
    s ≫ a'.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v' ≫ I.map a'.hom ≫ b))) := by
  have hm : A.map t ≫ a'.hom = a.hom ≫ s := by
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have heq : v ≫ I.map a.hom ≫ I.map s ≫ b =
      B.map (F.map t) ≫ v' ≫ I.map a'.hom ≫ b := by
    rw [reassoc_of% hv, ← I.map_comp_assoc, ← I.map_comp_assoc, hm, I.map_comp,
      Category.assoc]
  rw [heq, bd.homEquiv_naturality_left, ad.homEquiv_naturality_left, A.map_comp]
  simp only [← Category.assoc]
  congr 1
  rw [ht]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem specified_value
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ L.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L a = W.iso.inv ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
        ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c)).homEquiv _ _
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _
            ((ProEtale.fixedCompactSupportComparisonIso Λ c).inv.app W.complex ≫
              (ProEtale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} Λ) c).map W.iso.hom ≫ a))) := by
  rfl

private theorem specified_left
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M M' : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M) (W' : FixedEtaleOriginWitness X Λ M')
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (s : M.obj ⟶ M'.obj)
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M'.obj ⟶ L.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L
      ((ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} Λ) c).map s ≫ a) =
      s ≫ ProEtale.specifiedExceptionalHomEquiv Λ c M' W' L a := by
  obtain ⟨t, ht⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    W.complex.obj W'.complex.obj W'.complex.property).surjective
      (W.iso.hom ≫ s ≫ W'.iso.inv)
  have hv := (ProEtale.fixedCompactSupportComparisonIso Λ c).inv.naturality
    (ObjectProperty.homMk t : W.complex ⟶ W'.complex)
  rw [specified_value, specified_value]
  exact transpose_left _ _ _ _ _ _
    (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c))
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
    W.iso W'.iso _ _ s a t ht hv

private theorem specified_right
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M)
    (L L' : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ L.obj) (b : L.obj ⟶ L'.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L' (a ≫ b) =
      ProEtale.specifiedExceptionalHomEquiv Λ c M W L a ≫
        (ProEtale.sfFiniteExceptionalAt Λ c).map b := by
  rw [specified_value, specified_value]
  simp only [← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Functor.map_comp]
  simp only [Category.assoc]
  rfl

/-- The specified finite-coefficient Hom equivalence is natural in both ambient
arguments, including maps between objects with different retained etale origins.
In particular it is independent of the etale-origin witness.

Source: blueprint det-def-sf-operations (vi), thm-sf-ambient-adjoint-class (2).
(blueprint: lem-sf-specified-exceptional-hom-naturality).

Proof: lift alpha;s;alpha' inverse uniquely across the fully faithful derived
etale/pro-etale comparison. Naturality of the proper/open compact-support comparison
and of the two adjunction Hom maps then gives source naturality, after cancelling
alpha and alpha'. Target naturality follows from the target naturality of the same
adjunction Hom maps. Apply source naturality to the identity map with two arbitrary
origin witnesses, and cancel the support functor's image of the identity, to prove
witness independence. No separatedness of the source or target structure maps is used;
the empty scheme and zero coefficient ring use exactly the same equations. -/
theorem specifiedExceptionalHomEquiv_naturality
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint] :
    (∀ (M M' : DerivedCategory.Plus
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (W : FixedEtaleOriginWitness X Λ M) (W' : FixedEtaleOriginWitness X Λ M')
      (N : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      (s : M.obj ⟶ M'.obj)
      (a : (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} Λ) c).obj M'.obj ⟶ N.obj),
      specifiedExceptionalHomEquiv Λ c M W N
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c).map s ≫ a) =
        s ≫ specifiedExceptionalHomEquiv Λ c M' W' N a) ∧
    (∀ (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (W : FixedEtaleOriginWitness X Λ M)
      (N N' : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      (a : (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ N.obj) (b : N.obj ⟶ N'.obj),
      specifiedExceptionalHomEquiv Λ c M W N' (a ≫ b) =
        specifiedExceptionalHomEquiv Λ c M W N a ≫ (sfFiniteExceptionalAt Λ c).map b) ∧
    (∀ (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (W W' : FixedEtaleOriginWitness X Λ M)
      (N : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ))),
      specifiedExceptionalHomEquiv Λ c M W N =
        specifiedExceptionalHomEquiv Λ c M W' N) := by
  refine ⟨specified_left Λ c, specified_right Λ c, ?_⟩
  intro M W W' N
  ext a
  have h := specified_left Λ c M M W W' N (𝟙 M.obj) a
  rw [(rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} Λ) c).map_id, Category.id_comp, Category.id_comp] at h
  exact h

end AlgebraicGeometry.ProEtale
