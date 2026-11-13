/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorAffine
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCoverLeft
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # External sections with an affine second factor

Source: Stacks Project, Tag 0BED, lemma-kunneth, the displayed comparison on X times V.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- The external section comparison when the second factor is affine.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the comparison on X times V. -/
theorem externalGlobalSectionsTensor_bijective_of_isAffine_right
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)] [IsAffine Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by
  classical
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hU (i : C.I₀) : IsAffineOpen (U i) := by
    have : IsAffine (C.X i) := by
      dsimp only [C]
      rw [Scheme.OpenCover.finiteSubcover_X]
      infer_instance
    exact isAffineOpen_opensRange (C.f i)
  have hUU (i j : C.I₀) : IsAffineOpen (U i ⊓ U j) :=
    (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
      (U i) (by simp) (U j) (by simp) (hU i) (hU j)
  have hlocal (V : X.Opens) (hV : IsAffineOpen V) :
      Function.Bijective (externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G) := by
    have : IsAffine V.toScheme := hV
    exact externalGlobalSectionsTensor_bijective_of_isAffine
      k V.toScheme Y (V.ι ≫ f) g (F.restrict V.ι) G
  exact externalGlobalSectionsTensor_bijective_of_finite_cover_left k X Y f g F G
    U C.iSup_opensRange (fun i ↦ hlocal (U i) (hU i))
    (fun i j ↦ hlocal (U i ⊓ U j) (hUU i j))

end AlgebraicGeometry.Scheme.Modules
