/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit

/-!
# Injective étale sheaves of modules are acyclic as abelian sheaves

Let `Λ` be a ring. An injective presheaf of `Λ`-modules is a direct summand of the presheaf
`Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` (`CategoryTheory.Presheaf.cofreeModule`), whose underlying
presheaf of abelian groups is the cofree presheaf `CategoryTheory.Presheaf.cofree`. Hence the
Čech complexes of its underlying abelian presheaf are exact in positive degrees, and by the
Čech criterion the underlying abelian sheaf of an injective étale sheaf of `Λ`-modules on a
quasi-compact quasi-separated scheme has no higher cohomology. This compares the cohomology
of sheaves of `Λ`-modules with that of their underlying abelian sheaves.

## Main statements

- `CategoryTheory.Presheaf.exactAt_cechComplex_forget₂_of_injective`: the Čech complexes of
  the underlying abelian presheaf of an injective presheaf of modules are exact in positive
  degrees.
- `AlgebraicGeometry.Scheme.subsingleton_H_forget₂_of_injective`: on a quasi-compact
  quasi-separated scheme, the underlying abelian sheaf of an injective étale sheaf of
  `Λ`-modules has no higher cohomology.
-/

@[expose] public section

universe w v t u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] {ι : Type t}
  (U : ι → Over V)

/-- The Čech complexes of a retract of a presheaf whose Čech complex is exact in degree `q + 1`
are exact in degree `q + 1`. -/
lemma exactAt_cechComplex_of_retract {P P' : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} (i : P ⟶ P')
    (r : P' ⟶ P) (hir : i ≫ r = 𝟙 P) (q : ℕ) (h : ((cechComplex U).obj P').ExactAt (q + 1)) :
    ((cechComplex U).obj P).ExactAt (q + 1) := by
  set ι' := (cechComplex U).map i
  set ρ := (cechComplex U).map r
  have hιρ (k : ℕ) (c : ((cechComplex U).obj P).X k) : ρ.f k (ι'.f k c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hir,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1 h
    (ι'.f (q + 1) c) (by
      exact (ConcreteCategory.congr_hom (ι'.comm (q + 1) (q + 2)) c).trans
        ((congrArg (ι'.f (q + 2)) hc).trans (map_zero _)))
  exact ⟨ρ.f q b, (ConcreteCategory.congr_hom (ρ.comm q (q + 1)) b).trans
    ((congrArg (ρ.f (q + 1)) hb).trans (hιρ _ c))⟩

variable (R : Type (max w v)) [Ring R] (P : Cᵒᵖ ⥤ ModuleCat.{max w v} R)

/-- The presheaf of modules `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)`, the module version of
`CategoryTheory.Presheaf.cofree`. -/
@[simps]
noncomputable def cofreeModule : Cᵒᵖ ⥤ ModuleCat.{max w v} R where
  obj Y := ModuleCat.of R (∀ (Z : C) (_ : Z ⟶ Y.unop), P.obj (op Z))
  map {Y Y'} h := ModuleCat.ofHom
    { toFun c Z g := c Z (g ≫ h.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := by
    ext c
    simp
  map_comp _ _ := by
    ext c
    simp

/-- The embedding of a presheaf of modules into its cofree presheaf, `p ↦ (g ↦ P(g) p)`. -/
@[simps]
noncomputable def toCofreeModule : P ⟶ cofreeModule R P where
  app Y := ModuleCat.ofHom
    { toFun p Z g := P.map g.op p
      map_add' _ _ := funext fun _ ↦ funext fun _ ↦ map_add _ _ _
      map_smul' _ _ := funext fun _ ↦ funext fun _ ↦ map_smul _ _ _ }
  naturality Y Y' h := by
    ext p
    funext Z g
    change P.map g.op (P.map h p) = P.map (g ≫ h.unop).op p
    rw [op_comp, P.map_comp]
    rfl

instance : Mono (toCofreeModule R P) := by
  have (Y : Cᵒᵖ) : Mono ((toCofreeModule R P).app Y) :=
    (ModuleCat.mono_iff_injective _).2 fun p p' h ↦ by
      have := congrFun (congrFun h Y.unop) (𝟙 _)
      change P.map (𝟙 _).op p = P.map (𝟙 _).op p' at this
      simpa using this
  exact NatTrans.mono_of_mono_app _

/-- The Čech complexes of the underlying abelian presheaf of an injective presheaf of modules
are exact in positive degrees. -/
theorem exactAt_cechComplex_forget₂_of_injective [Injective P] (q : ℕ) :
    ((cechComplex U).obj (P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v})).ExactAt
      (q + 1) := by
  let r := Injective.factorThru (𝟙 P) (toCofreeModule R P)
  have hr : toCofreeModule R P ≫ r = 𝟙 P := Injective.comp_factorThru _ _
  let r' : cofree (P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v}) ⟶
      P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v} :=
    { app Y := AddCommGrpCat.ofHom
        { toFun c := (r.app Y).hom c
          map_zero' := map_zero (r.app Y).hom
          map_add' a b := map_add (r.app Y).hom a b }
      naturality Y Y' h := by
        ext c
        exact ConcreteCategory.congr_hom (r.naturality h) c }
  refine exactAt_cechComplex_of_retract U (toCofree _) r' ?_ q (exactAt_cechComplex_cofree U _ q)
  ext Y p
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hr Y) p

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Scheme

open Presheaf

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- On a quasi-compact quasi-separated scheme, the underlying abelian sheaf of an injective
étale sheaf of `Λ`-modules has no higher cohomology. -/
theorem subsingleton_H_forget₂_of_injective (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (q : ℕ) :
    Subsingleton (Sheaf.H ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J) (q + 1)) := by
  have : Injective J.obj := (sheafificationAdjunction _ _).map_injective J inferInstance
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let B : X.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : X.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  have hF (V : X.Etale) {n : ℕ} (U : Fin n → Over V) (q : ℕ) :
      ((cechComplex U).obj ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J).obj).ExactAt (q + 1) :=
    exactAt_cechComplex_forget₂_of_injective U _ J.obj q
  exact Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov _ (fun V _ _ U _ _ q ↦ hF V U q) q

end AlgebraicGeometry.Scheme
