/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientArrowTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientRootEndpoint

/-! # Coefficient maps preserve the normalized finite-root arrow
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] comparisonUpperStar comparisonAdjunction forgetComparisonIso

private theorem finiteRoots_unique {X : Scheme.{u}} {N : ℕ}
    (r s : FiniteRoots X N) : r.iso = s.iso := by
  have : Mono (Scheme.proEtaleRootsOfUnityInclusion X N) := by
    dsimp [Scheme.proEtaleRootsOfUnityInclusion]
    infer_instance
  apply Iso.ext
  apply (cancel_mono (Scheme.proEtaleRootsOfUnityInclusion X N)).mp
  exact r.inclusion.trans s.inclusion.symm

/-- A scalar map normalized on pure root tensors preserves the root arrow. -/
theorem finiteRoots_toLine_scalar
    {R A : Type (u + 1)} [CommRing R] [CommRing A] {φ : R →+* A}
    {N : ℕ} {hR : (N : R) = 0} {hA : (N : A) = 0} {Y : Scheme.{u}}
    (maps : CartierScalarMaps φ N hR hA Y)
    (r s : FiniteRoots (diagonalSurface Y) N) :
    r.toLine R hR ≫
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
        (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).map maps.line = s.toLine A hA := by
  have hrs := finiteRoots_unique r s
  unfold FiniteRoots.toLine
  rw [hrs]
  simp only [Category.assoc]
  congr 1
  apply ((comparisonAdjunction Ab.{u + 1} (diagonalSurface Y)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  have hb (B : Type (u + 1)) [CommRing B] (hB : (N : B) = 0) :
      (comparisonAdjunction Ab.{u + 1} (diagonalSurface Y)).homEquiv _ _
        ((forgetComparisonIso B (diagonalSurface Y)).hom.app
          (Scheme.finiteEtaleTateLine (diagonalSurface Y) N B hB)) =
      (sheafCompose (diagonalSurface Y).smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).map
          ((comparisonAdjunction (ModuleCat.{u + 1} B) (diagonalSurface Y)).unit.app
            (Scheme.finiteEtaleTateLine (diagonalSurface Y) N B hB)) := by
    calc
      _ = (comparisonAdjunction Ab.{u + 1} (diagonalSurface Y)).homEquiv _ _
          (((comparisonAdjunction Ab.{u + 1} (diagonalSurface Y)).homEquiv _ _).symm
            ((Etale.RawModuleScalarComparison.forget B (diagonalSurface Y)).map
              ((comparisonAdjunction (ModuleCat.{u + 1} B) (diagonalSurface Y)).unit.app
                (Scheme.finiteEtaleTateLine (diagonalSurface Y) N B hB)))) :=
        congrArg _ (forgetComparisonIso_hom B (diagonalSurface Y) _)
      _ = _ := by
        exact (Equiv.apply_symm_apply _ _).trans (by rfl)
  erw [hb R hR, hb A hA]
  apply Sheaf.hom_ext
  ext V z
  have h := maps.line_normalization V 1 z
  rw [map_one] at h
  change _ = _ at h
  exact h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
