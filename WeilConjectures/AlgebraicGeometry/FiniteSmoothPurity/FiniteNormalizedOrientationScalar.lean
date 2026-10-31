/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothDiagonalScalar
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedScalar

/-! # Coefficient compatibility of normalized finite smooth orientations

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation.
(blueprint: lem-sp-finite-normalized-orientation-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Normalized orientations commute with a coefficient map and the specified root power.
Source: coefficient compatibility (3), Orientation
(blueprint: lem-sp-finite-normalized-orientation-scalar).
Proof: cancel the invertible normal-section and integration factors in each supplied
normalization equation. This writes each orientation as diagonalFactor followed by
integratedSpecialization. The ring map supplies the common target annihilator N.
Paste finiteSmoothDiagonalScalar with integratedSpecialization_scalar, and cancel
the two orientation isomorphisms. All coefficient and Tate maps remain the supplied
canonical maps; no coefficient-flatness hypothesis is used. -/
theorem normalizedOrientation_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : M ∣ N)
    (hA : (N : A) = 0) (hB : (M : B) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (f : X ⟶ Y)
    [HasCompactification f] [IsSeparated f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (geometry : FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (M : Γ(X, ⊤)))
    (alphaN : dualizingComplex A f ≅ line A N hA X d)
    (alphaM : dualizingComplex B f ≅ line B M hB X d)
    (_hn : OrientationNormalized A N hN hA f d geometry hX alphaN)
    (_hm : OrientationNormalized B M hM hB f d geometry hX' alphaM)
    (t : CoefficientLineComparison φ N M hA hB X) :
    (ordinaryScalar φ X).map alphaN.inv ≫ ExceptionalCoefficients.dualizingScalarMap φ f =
      (t.tensorPower d).hom ≫ alphaM.inv := by
  let := geometry
  obtain ⟨κ, hκ, sq, heq⟩ := _hn
  obtain ⟨κ', hκ', sq', heq'⟩ := _hm
  let ψ := integratedSpecialization A d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) sq N
    hN hA hX κ
  let ψ' := integratedSpecialization B d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) sq' M
    hM hB hX' κ'
  have factorN : alphaN.hom = finiteSmoothDiagonalFactor A f ≫ ψ := by
    let := normalSectionMap_isIso A d (pullback.fst f f)
      (pullback.diagonal f) (pullback.diagonal_fst f) sq N
      hN hA hX
    let := (FiniteRingSectionDeformation.bundleAdjoint_isIso N
      hN A hA X hX d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
    apply (cancel_mono (FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA X hX d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
      normalSectionMap A d (pullback.fst f f)
        (pullback.diagonal f) (pullback.diagonal_fst f) sq)).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq.symm
  have factorM : alphaM.hom = finiteSmoothDiagonalFactor B f ≫ ψ' := by
    let := normalSectionMap_isIso B d (pullback.fst f f)
      (pullback.diagonal f) (pullback.diagonal_fst f) sq' M
      hM hB hX'
    let := (FiniteRingSectionDeformation.bundleAdjoint_isIso M
      hM B hB X hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
    apply (cancel_mono (FiniteRingSectionDeformation.bundleSectionAdjoint
      M hM B hB X hX' d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
      normalSectionMap B d (pullback.fst f f)
        (pullback.diagonal f) (pullback.diagonal_fst f) sq')).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq'.symm
  have hψ := integratedSpecialization_scalar φ
    N M hN
    hM hMN
    hA hB d (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
    sq sq' hX hX' κ κ' hκ hκ' t
  have hBN : (N : B) = 0 := by
    rw [← map_natCast φ, hA, map_zero]
  have hdiag := finiteSmoothDiagonalScalar φ
    N hN hA hBN
    hY f d
  have forward : ExceptionalCoefficients.dualizingScalarMap φ f ≫ alphaM.hom =
      (ordinaryScalar φ X).map alphaN.hom ≫
        (t.tensorPower d).hom := by
    rw [factorN, factorM, Functor.map_comp, ← Category.assoc, ← hdiag, Category.assoc]
    simpa only [Category.assoc] using congrArg (fun z ↦
      (ordinaryScalar φ X).map
        (finiteSmoothDiagonalFactor A f) ≫ z) hψ.symm
  apply (cancel_mono alphaM.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [forward, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
