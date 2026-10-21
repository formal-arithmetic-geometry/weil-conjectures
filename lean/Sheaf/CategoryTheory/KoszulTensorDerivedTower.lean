/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import all Sheaf.CategoryTheory.RingedCechKoszulDualKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! Ordinary Koszul tensor towers represent the published derived tensor towers.
Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable (O : Sheaf J CommRingCat.{u})
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

set_option linter.unusedSectionVars false in
private theorem dualKoszul_flatOnSite (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) (i : ℤ) :
    SheafOfModules.IsFlatOnSite (J := J) (R := O)
      (((ringedKoszulDualTower O r b).obj (op n)).X i) :=
  (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso O _).symm
    (koszulDual_flat O r b n i)

/-- Ordinary tensor with the finite dual Koszul tower computes derived tensor,
including every transition map.

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU, and More on
Algebra, Tag 0913 (blueprint: lem-sbc-koszul-tensor-derived-tower).

Proof: Choose a flat-term K-flat resolution P→M. Each dual Koszul term is K-flat
and has flat terms, so its tensor with P→M is a quasi-isomorphism. These maps are
natural in the Koszul term and hence give an isomorphism between the localized
ordinary tensor towers. Apply the fixed-left-factor comparison for P; its naturality
in the second factor identifies the tower transitions. Finally apply the published
derived tensor bifunctor to the isomorphism Q(P)→Q(M) in the first factor. The
composite is the required tower isomorphism. The argument includes the empty
Koszul sequence and zero complexes. -/
theorem koszulTensorDerivedTower (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    Nonempty (((ringedKoszulTensorTower O r b).obj M ⋙ DerivedCategory.Q) ≅
      (ringedKoszulDualTower O r b ⋙ DerivedCategory.Q ⋙
        (SheafOfModules.KFlatFixedTensor.derivedTensor O).obj
          (DerivedCategory.Q.obj M))) := by
  obtain ⟨P, p, hP, hfP, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients M
  have hfP' (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := O) (P.X i) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso O _).symm
      (hfP i)
  obtain ⟨_, ht⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated O
  let a := Functor.whiskerRight ((ringedKoszulTensorTower O r b).map p) DerivedCategory.Q
  have (n : ℕᵒᵖ) : IsIso (a.app n) := by
    have hk := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
      (ringed_cech_koszul_dual_tower_isKFlat O r b n.unop)
    have : QuasiIso (((ringedKoszulTensorTower O r b).map p).app n) :=
      ((ht _ hk (dualKoszul_flatOnSite O r b n.unop)).1 P M p hp).2
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      (((ringedKoszulTensorTower O r b).map p).app n)))
  have := NatIso.isIso_of_isIso_app a
  let e₁ := asIso a
  obtain ⟨c, _, _⟩ := (ht P hP hfP').2.2.2.1
  have : QuasiIso p := hp
  let e₂ := (SheafOfModules.KFlatFixedTensor.derivedTensor O).mapIso
    (asIso (DerivedCategory.Q.map p))
  exact ⟨e₁.symm ≪≫ Functor.isoWhiskerLeft (ringedKoszulDualTower O r b) c ≪≫
    Functor.isoWhiskerLeft (ringedKoszulDualTower O r b ⋙ DerivedCategory.Q) e₂⟩

end CategoryTheory
