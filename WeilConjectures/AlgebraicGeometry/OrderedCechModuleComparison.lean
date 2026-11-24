/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleRetraction
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleKernelNullHomotopic

/-! # Ordered versus usual Čech complexes of module sheaves

## References

* [Stacks, Tags 01FJ, 01FK and 01FM]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- A complex with the ordered section formulas is homotopy equivalent to the direct
image of any locally linear usual Čech presentation. No cover, affine, flatness or
quasi-coherence hypothesis is needed (Stacks, Tags 01FJ, 01FK and 01FM). -/
theorem orderedCech_module_comparison {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (K : CochainComplex T'.Modules ℤ) (hK : K.IsStrictlyGE 0)
    (a : ∀ (p : ℕ) (B : T'.Opens),
      Γ(K.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B)))
    (hn : ∀ (p : ℕ) {B C : T'.Opens} (i : B ⟶ C)
        (s : Γ(K.X (p : ℤ), C)) (t : Fin (p + 1) ↪o Fin r),
      a p B ((K.X (p : ℤ)).presheaf.map i.op s) t =
        M.presheaf.map (homOfLE (inf_le_inf le_rfl
          ((TopologicalSpace.Opens.map f'.base).map i).le)).op (a p C s t))
    (hl : ∀ (p : ℕ) (B : T'.Opens) (b : Γ(T', B))
        (s : Γ(K.X (p : ℤ), B)) (t : Fin (p + 1) ↪o Fin r),
      a p B (b • s) t =
        X'.presheaf.map (homOfLE (show
          alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B
            from inf_le_right)).op (f'.app B b) • a p B s t)
    (ha : ∀ (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
        (t : Fin (p + 2) ↪o Fin r),
      a (p + 1) B ((K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          M.presheaf.map (homOfLE (inf_le_inf
            (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
              (a p B s ((Fin.succAboveOrderEmb j).trans t)))
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s) :
    Nonempty (HomotopyEquiv K
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat)) := by
  obtain ⟨rmap, imap, hi, hr⟩ :=
    orderedCech_module_retraction f' M W₀ K hK a hn hl ha D e hd hlinear
  let L := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
    ComplexShape.embeddingUpNat
  let g : L ⟶ L := rmap ≫ imap - 𝟙 L
  have hgr : g ≫ rmap = 0 := by
    dsimp only [g]
    rw [Preadditive.sub_comp, Category.assoc, hi, Category.comp_id,
      Category.id_comp, sub_self]
  have hg : ∀ (p : ℕ) (B : T'.Opens) (s : Γ(L.X (p : ℤ), B))
      (t : Fin (p + 1) ↪o Fin r),
      orderedCechModuleCoordinate f' M W₀ D e p B t ((g.f (p : ℤ)).app B s) = 0 := by
    intro p B s t
    rw [← hr]
    have hz := congrArg (fun k : L ⟶ K ↦ (k.f (p : ℤ)).app B s) hgr
    have hzero : (rmap.f (p : ℤ)).app B ((g.f (p : ℤ)).app B s) = 0 := by
      simpa using hz
    rw [hzero, map_zero]
    rfl
  obtain ⟨h⟩ := orderedCech_module_kernel_nullHomotopic f' M W₀ D e hd hlinear g hg
  exact ⟨{
    hom := imap
    inv := rmap
    homotopyHomInvId := Homotopy.ofEq hi
    homotopyInvHomId := Homotopy.equivSubZero.symm h }⟩

end AlgebraicGeometry.Scheme.Modules
