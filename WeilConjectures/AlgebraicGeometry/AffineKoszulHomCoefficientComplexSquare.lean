/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.HomComplexToSingleCoefficientSquare
import WeilConjectures.AlgebraicGeometry.AffineKoszulSignedDualCoefficientSquare

/-! # Finite free Koszul Hom coordinates before taking homology

Source: Stacks Project, Tag 0BQZ, displayed map of Hom complexes. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private theorem exists_iso_square_trans {C : Type*} [Category* C]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} {f : X₁ ⟶ X₂} {g : Y₁ ⟶ Y₂} {h : Z₁ ⟶ Z₂}
    (hf : ∃ (a : X₁ ≅ Y₁) (b : X₂ ≅ Y₂), f ≫ b.hom = a.hom ≫ g)
    (hg : ∃ (a : Y₁ ≅ Z₁) (b : Y₂ ≅ Z₂), g ≫ b.hom = a.hom ≫ h) :
    ∃ (a : X₁ ≅ Z₁) (b : X₂ ≅ Z₂), f ≫ b.hom = a.hom ≫ h := by
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨c, d, hcd⟩ := hg
  exact ⟨a ≪≫ c, b ≪≫ d, (CommSq.vert_comp ⟨hab⟩ ⟨hcd⟩).w⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Applying internal Hom to the sheafified coefficient quotient gives the
sheafification of the explicit coefficient reduction between dual complexes
(Stacks, Tags 0BQZ and 01HV). -/
theorem affine_koszul_hom_coefficient_complex_square
    {Y : Scheme.{u}} (U : Y.affineOpens) (I : Ideal (Γ(Y, U.1)))
    (n : ℕ) (f : Fin n → Γ(Y, U.1))
    (H : CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ ⥤
      CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ)
    (hH : H =
      let A := (Γ(Y, U.1) : Type u)
      let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
      let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
      (homComplexFunctor (R := U.1.toScheme.toRingedSpace.sheaf)).obj (op E)) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
    let S := CochainComplex.singleFunctor U.1.toScheme.Modules 0
    ∃ (cO : H.obj (S.obj (T.obj (ModuleCat.of A A))) ≅
        TC.obj ((ExteriorAlgebra.koszulDualComplex A n f).extend
          ComplexShape.embeddingUpNat))
      (cQ : H.obj (S.obj (T.obj (ModuleCat.of A (A ⧸ I)))) ≅
        TC.obj ((ExteriorAlgebra.koszulQuotientDualComplex A I n f).extend
          ComplexShape.embeddingUpNat)),
      H.map (S.map (T.map (ModuleCat.ofHom I.mkQ))) ≫ cQ.hom =
        cO.hom ≫ TC.map (HomologicalComplex.extendMap
          (ExteriorAlgebra.koszulCoefficientReduction A I n f)
          ComplexShape.embeddingUpNat) := by
  subst H
  let A := (Γ(Y, U.1) : Type u)
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let E := TC.obj
    ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
  exact exists_iso_square_trans
    (homComplex_to_single_coefficient_square
      (R := U.1.toScheme.toRingedSpace.sheaf) E
      (T.obj (ModuleCat.of A A)) (T.obj (ModuleCat.of A (A ⧸ I)))
      (T.map (ModuleCat.ofHom I.mkQ)))
    (affine_koszul_signed_dual_coefficient_square U I n f)

end AlgebraicGeometry
