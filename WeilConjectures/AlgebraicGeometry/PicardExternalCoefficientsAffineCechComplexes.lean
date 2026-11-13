/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.PicardExternalCoefficientsAffineCechDifferential

/-! # The affine-right product-cover Cech calculation

## References

* Stacks Project, Varieties, Tag 0BED.
-/

@[expose] public section

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The termwise external tensor formula on the inverse image of an affine open.
There is no covering hypothesis and no assertion about cohomology or derived functors.
(Stacks, Tags 0BED, 01I9, 01CD) -/
theorem picardExternalCupCoefficients_affine_cech_complexes
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type w} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (V : Y.Opens) (hV : IsAffineOpen V) :
    let Z := Limits.pullback f g
    let W : Z.Opens := (pullback.snd f g) ⁻¹ᵁ V
    let E := (externalCupCoefficients f g F G).restrict W.ι
    let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
    let B := (cechComplexFunctor U').obj E.presheafModuleCat
    let R := ModuleCat.restrictScalars (scalarMap f ⊤)
    let C := (R.mapHomologicalComplex (.up ℕ)).obj
      ((cechComplexFunctor U).obj F.presheafModuleCat)
    let T := tensorRight (scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤))
    Nonempty
        (((forget₂ (ModuleCat.{w} Γ(W.toScheme, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
            (.up ℕ)).obj B ≅
          ((forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}).mapHomologicalComplex
            (.up ℕ)).obj ((T.mapHomologicalComplex (.up ℕ)).obj C)) := by
  obtain ⟨e, he⟩ := picardAffineCech_normalized_terms f g F G U V hU hV
  exact ⟨(HomologicalComplex.Hom.isoOfComponents e
    (picardAffineCech_normalized_differential k X Y f g F G U V e he)).symm⟩

end AlgebraicGeometry.Scheme.Modules
