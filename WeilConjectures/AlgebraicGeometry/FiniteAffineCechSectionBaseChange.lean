/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechBaseChangeCoordinates
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleComparison
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Termwise base change and the ordered Čech comparison

## References

* Stacks Project, Tags 02KE, 01FK and 01FM
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Compare the specified model with the direct-image complex of a Čech sheaf complex.
There is no cover assumption, no augmentation, no acyclicity hypothesis and no assertion
about derived direct images.
(Stacks, Tags 02KE, 01FK and 01FM.) -/
theorem finiteAffineCech_section_baseChange {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens) (hV : ∀ i, IsAffineOpen (V i))
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (D : CochainComplex X'.Modules ℕ)
    (W : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ i, W i = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ V i.down))
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              ((Scheme.Modules.pullback g').obj F).presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              ((Scheme.Modules.pullback g').obj F).presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ((Modules.pullback g').obj F, (∏ᶜ fun l ↦ W (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                ((Modules.pullback g').obj F).presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W (y l)) ⨯ B ⟶ B).op a • c s) :
    ∀ q : ℕ,
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj
          (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V)).homology q ≅
        (((Modules.pushforward f').mapHomologicalComplex _).obj D).homology q) := by
  obtain ⟨a, hn, hl, ha⟩ :=
    finiteAffineCech_baseChange_coordinates f F U hU V hV g g' f' sq W hW
  let K : CochainComplex T'.Modules ℤ := ((Modules.pullback g).mapHomologicalComplex _).obj
    (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V)
  have hK : K.IsStrictlyGE 0 := by
    have : (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V).IsStrictlyGE 0 :=
      finiteAffineCechModel_ge _ _ V
    dsimp only [K]
    infer_instance
  obtain ⟨E⟩ := orderedCech_module_comparison f' ((Modules.pullback g').obj F) W
    K hK a hn hl ha D e hd hlinear
  intro q
  exact ⟨E.toHomologyIso (q : ℤ) ≪≫
    (((Modules.pushforward f').mapHomologicalComplex _).obj D).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl⟩

end AlgebraicGeometry.Scheme.Modules
