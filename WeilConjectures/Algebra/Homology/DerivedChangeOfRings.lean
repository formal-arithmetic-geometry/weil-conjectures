/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso

/-!
# Derived change of rings on a ringed site

The main theorem asserts an additive functor `E` given by `SheafOfModules.changeOfRings φ` on
objects and `SheafOfModules.changeOfRingsHom φ` on morphisms (`- ⊗_O O'`), and uses
`E.mapHomologicalComplex` (termwise change of rings of complexes) and
`E.mapHomotopyCategory ⋙ DerivedCategory.Qh` (the functor `K(O) → D(O')`).

## References

* Stacks Project, Tags 06YT, 06YY and 06XN
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Derived change of rings along a morphism `φ : O ⟶ O'` of sheaves of commutative rings
on a site. There is an additive functor `E : Mod(O) ⥤ Mod(O')` given by the change of rings
`changeOfRings φ` / `changeOfRingsHom φ` (`- ⊗_O O'`), such that termwise change of rings sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms, and `K(O) → D(O')`,
`G ↦ Q(G ⊗_O O')`, has a pointwise left derived functor `Lφ^* : D(O) ⥤ D(O')` with counit `ε`,
which is triangulated and for which `ε` is an isomorphism at every K-flat complex. -/
theorem derivedChangeOfRings
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{u} (𝓡 O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (𝓡 O'))] :
    ∃ (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
      (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
      (_ : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
        E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
      (_ : E.Additive),
      (∀ {P Q : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ} (α : P ⟶ Q),
        P.IsKFlatTensor → Q.IsKFlatTensor → QuasiIso α →
          QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) ∧
      (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (𝓡 O)) (ComplexShape.up ℤ)) ∧
      ∃ (LF : DerivedCategory (SheafOfModules.{u} (𝓡 O)) ⥤
          DerivedCategory (SheafOfModules.{u} (𝓡 O')))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{u} (𝓡 O)) (ComplexShape.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
          ∀ P : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ, P.IsKFlatTensor →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  have hscalar (U : Cᵒᵖ) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O').obj)).left_adjoint_additive
  let E₀ : SheafOfModules.{u} (𝓡 O) ⥤ PresheafOfModules.{u} (𝓡 O').obj :=
    { obj := changeOfRingsPresheaf φ
      map := fun a ↦
        { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
          naturality := changeOfRingsHom_naturality φ _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro U
        simp
        rfl
      map_comp := by
        intro M N P a b
        apply PresheafOfModules.hom_ext
        intro U
        simp }
  let E := E₀ ⋙ PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)
  have hE₀ : E₀.Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro U
    simpa only [E₀, SheafOfModules.add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
        (f := a.val.app U) (g := b.val.app U)
  have hE : E.Additive := by infer_instance
  refine ⟨E, fun _ ↦ rfl, ?_, hE, ?_⟩
  · intro M N a
    simp [E, E₀, changeOfRingsHom]
  · have hinv : ∀ {P Q : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ} (α : P ⟶ Q),
        P.IsKFlatTensor → Q.IsKFlatTensor → QuasiIso α →
          QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α) :=
      changeOfRings_kFlat_quasiIso φ E (fun _ ↦ rfl)
        (by intro M N a; simp [E, E₀, changeOfRingsHom])
    refine ⟨hinv, ?_⟩
    let F := E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
    let S : Set (HomotopyCategory (SheafOfModules.{u} (𝓡 O)) (ComplexShape.up ℤ)) :=
      { X | ∃ P : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ,
          P.IsKFlatTensor ∧ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X }
    have hres : ∀ X : HomotopyCategory (SheafOfModules.{u} (𝓡 O)) (ComplexShape.up ℤ),
        ∃ (X' : HomotopyCategory (SheafOfModules.{u} (𝓡 O)) (ComplexShape.up ℤ))
          (s : X' ⟶ X), X' ∈ S ∧ HomotopyCategory.quasiIso _ _ s := by
      intro X
      obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution G
      refine ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨P, hP, rfl⟩, ?_⟩
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have hinvS : ∀ X Y : HomotopyCategory (SheafOfModules.{u} (𝓡 O))
        (ComplexShape.up ℤ), ∀ s : X ⟶ Y, X ∈ S → Y ∈ S →
          HomotopyCategory.quasiIso _ _ s → IsIso (F.map s) := by
      intro X Y s hX hY hs
      obtain ⟨P, hP, rfl⟩ := hX
      obtain ⟨Q, hQ, rfl⟩ := hY
      obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
      have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
      have hEa := hinv a hP hQ ha
      dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
      apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
    obtain ⟨hpoint, LF, ε, hLF, htri, hε⟩ :=
      Functor.leftDerived_from_resolvingClass _ _ F S hres hinvS
    exact ⟨hpoint, LF, ε, hLF, htri, fun P hP ↦ hε _ ⟨P, hP, rfl⟩⟩

end SheafOfModules
