/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafTerms
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafLocalContraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafAffineComparison

/-! # Augmented increasing-tuple complex of module sheaves

## References

* Stacks Project, Tags 01FM, 02KG, 02KH
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Construct the augmented increasing-tuple sheaf complex and its affine section model.
(Stacks, Tags 01FM, 02KG and 02KH). -/
theorem exists_affineAlternatingCech_augmented_construction
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    ∃ (C : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj G ⟶ C),
      Nonempty (((Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (C.extend ComplexShape.embeddingUpNat) ≅
          affineAlternatingCechModel f U G) ∧
      QuasiIso ε ∧
      QuasiIso (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap ε
          ComplexShape.embeddingUpNat)) ∧
      ∀ k : ℕ, ∃ (n : ℕ) (W : Fin n → X.Opens),
        (∀ j, IsAffineOpen (W j)) ∧
        Nonempty (C.X k ≅ ∏ᶜ fun j : Fin n ↦
          (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι)) := by
  classical
  have hsep : IsSeparated (terminal.from X) := by
    have h : IsSeparated (f ≫ terminal.from (Spec A)) := inferInstance
    simpa only [terminal.comp_from] using h
  let : X.IsSeparated := ⟨hsep⟩
  obtain ⟨hε, hpε⟩ := alternatingCechSheafAugmentation_quasiIso (pullback.fst f g) U hU G
  refine ⟨alternatingCechSheafComplex U G, alternatingCechSheafAugmentation U G,
    alternatingCechSheafComplex_affineComparison f U haffine G, hε, hpε, ?_⟩
  intro k
  let T := Fin (k + 1) ↪o Fin r
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let W : Fin (Fintype.card T) → X.Opens := fun j ↦ alternatingCechIntersection U (e.symm j)
  obtain ⟨q⟩ := alternatingCechSheafComplex_terms U G k
  refine ⟨Fintype.card T, W, ?_, ?_⟩
  · intro j
    exact IsAffineOpen.iInf fun l ↦ haffine (e.symm j l)
  · exact ⟨q ≪≫ (Pi.reindex e.symm (fun t : T ↦
      (Scheme.Modules.pushforward (alternatingCechIntersection U t).ι).obj
        (G.restrict (alternatingCechIntersection U t).ι))).symm⟩

end AlgebraicGeometry
