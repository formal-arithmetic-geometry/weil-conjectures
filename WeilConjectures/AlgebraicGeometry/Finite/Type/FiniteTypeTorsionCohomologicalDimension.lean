/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Affine.AffineToGlobalTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Affine.AffineTorsionCohomologicalDimensionSupplement
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived

/-!
# Torsion cohomological dimension of a finite-type scheme
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem subsingleton_H_of_subsingleton_derivedCohomology
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))) : Subsingleton (Sheaf.H F q) := by
  have hz : Limits.IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr h
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ X.Etale))).Additive := { map_add := rfl }
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  obtain ⟨e⟩ := (show Nonempty _ from ⟨
    Functor.homologyRightDerivedFunctorObjSingleFunctorIso Γ F q⟩)
  obtain ⟨eS⟩ := (show Nonempty _ from ⟨
    (NatIso.rightDerived
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        Limits.terminalIsTerminal) q).app F⟩)
  let S : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} := Sheaf.sectionsFunctorAt X.smallEtaleTopology (⊤_ X.Etale)
  have hz' : Limits.IsZero ((S.rightDerived q).obj F) := by
    exact hz.of_iso (e ≪≫ eS).symm
  exact (Sheaf.subsingleton_H_iff_isZero_rightDerived X.smallEtaleTopology
    Limits.terminalIsTerminal q F).2 hz'

/-- A finite-type scheme of dimension `d` over a field of torsion étale cohomological
 dimension at most `c` has torsion étale cohomological dimension at most `2 * d + c`. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_finiteType
    (K : Type u) [Field K] (c d : ℕ)
    (hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c)
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (hX : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    HasTorsionEtaleCohomologicalDimensionLE X (2 * d + c) := by
  intro F hF q hq
  have hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞) := le_of_eq hX
  have hAffine : ∀ {Y : Scheme.{u}} (b : Y ⟶ Spec (.of K))
      [LocallyOfFiniteType b] [QuasiCompact b] [IsAffine Y]
      (hY : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
      (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion)
      (n : ℕ), d + c < n → Subsingleton (Sheaf.H G n) := by
    intro Y b _ _ _ hY G hG n hn
    apply subsingleton_H_of_two_mul_add_lt_of_isAffine c d
      (fun H hH m hm ↦ subsingleton_H_of_subsingleton_derivedCohomology H m
        (hK H hH m hm)) b hY G hG n hn
  have hH : Subsingleton (Sheaf.H F q) :=
    subsingleton_H_of_two_mul_add_lt_of_affine_bound c d (X ↘ Spec (.of K)) hdim
      hAffine F hF q hq
  let S : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} := Sheaf.sectionsFunctorAt X.smallEtaleTopology (⊤_ X.Etale)
  have hz : Limits.IsZero ((S.rightDerived q).obj F) :=
    (Sheaf.subsingleton_H_iff_isZero_rightDerived X.smallEtaleTopology
    Limits.terminalIsTerminal q F).1 hH
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ X.Etale))).Additive := { map_add := rfl }
  obtain ⟨e⟩ := (show Nonempty _ from ⟨
    Functor.homologyRightDerivedFunctorObjSingleFunctorIso Γ F q⟩)
  obtain ⟨eS⟩ := (show Nonempty _ from ⟨
    (NatIso.rightDerived
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        Limits.terminalIsTerminal) q).app F⟩)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hz.of_iso (e ≪≫ eS))

end AlgebraicGeometry.Scheme

end
