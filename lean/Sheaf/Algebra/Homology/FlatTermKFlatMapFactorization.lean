/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Sheaf.Paper.KFlatMapFactorization
import all Sheaf.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModelOfClass

/-! # Flat-term K-flat factorization in a closed Grothendieck category -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

/-- A map from a flat-term K-flat complex has a flat-term K-flat target lift.
Source: Stacks Project, Cohomology on Sites, Tag 0G7D
(blueprint: lem-pur-flat-term-kflat-map-factorization-native).

Proof: resolve the cone of t by a flat-term K-flat complex M. Compose its
augmentation with the connecting map to D[1], and take the cone shifted by -1.
The cone-square completion produces v and c and the required homotopy; its
third-isomorphism argument makes c a quasi-isomorphism. Shifts and cones preserve
K-flatness. The new complex has terms M^i plus D^i, hence has flat terms.
This proof also applies to zero sources and unbounded complexes. -/
theorem exists_flat_term_kFlat_map_factorization {D I : CochainComplex C ℤ}
    (t : D ⟶ I) (hD : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat D)
    (hflatD : ∀ n, ObjectProperty.flat (D.X n)) :
    ∃ (N : CochainComplex C ℤ) (v : D ⟶ N) (c : N ⟶ I),
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat N ∧
      (∀ n, ObjectProperty.flat (N.X n)) ∧ QuasiIso c ∧
      Nonempty (Homotopy (v ≫ c) t) := by
  classical
  obtain ⟨M, m, hm, hflatM, hM⟩ := exists_quasiIso_flat_kFlat (mappingCone t)
  let := hm
  let g := m ≫ (mappingCone.triangle t).mor₃
  let N := (mappingCone g)⟦(-1 : ℤ)⟧
  obtain ⟨v, c, hc, ⟨hhom⟩⟩ := cone_factorization t m
  have hshift (P : CochainComplex C ℤ)
      (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) (n : ℤ) :
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat (P⟦n⟧) :=
    (ObjectProperty.prop_shift_iff_of_isStableUnderShift
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P n).2 hP
  have hN : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat N :=
    hshift _ (CategoryTheory.Functor.kFlat_cone g hM (hshift D hD 1)) (-1)
  refine ⟨N, v, c, hN, ?_, hc, ⟨hhom.symm⟩⟩
  intro i
  let e : N.X i ≅ M.X i ⊞ D.X i :=
    (mappingCone g).shiftFunctorObjXIso (-1) i (i - 1) (by omega) ≪≫
      HomologicalComplex.homotopyCofiber.XIsoBiprod g (i - 1) i
        (by change i - 1 + 1 = i; omega) ≪≫
      biprod.mapIso (Iso.refl _) (D.shiftFunctorObjXIso 1 (i - 1) i (by omega))
  exact ObjectProperty.prop_of_iso _ e.symm
    (ObjectProperty.flat_biprod (hflatM i) (hflatD i))

end CochainComplex
