/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechAmitsurComparison

/-! # Čech vanishing for lifted tensor-section sheaves

## References

* Stacks Project, Tags 03P2 and 03OZ
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The lifted tensor-section sheaf has zero positive Čech cohomology on finite affine covers
(Stacks, Tags 03P2 and 03OZ). -/
theorem isZero_etaleTensorSectionsSheaf_ulift_cech
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (hf : finiteAffineEtaleCechCover X U I V f) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)).homology p) := by
  obtain ⟨B, a, hflat, ⟨e⟩⟩ :=
    exists_etaleTensorSectionsSheaf_ulift_cech_amitsur_iso X F U I V f hf
  let A := Γ(U.left, ⊤)
  let M := Γ((Modules.tensorPullback U.hom).obj F, ⊤)
  let : Algebra A B := a.toAlgebra
  let : Module.FaithfullyFlat A B := hflat
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have h := (Module.FaithfullyFlat.exact_amitsurComplex A B M).2.2 q
  have hm := h.map ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u})
  have he : ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
        (Algebra.TensorProduct.amitsurComplex A B M)).ExactAt (q + 1) := by
    exact hm
  exact (he.of_iso e.symm).isZero_homology

end AlgebraicGeometry.Scheme
