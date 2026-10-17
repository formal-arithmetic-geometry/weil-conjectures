/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.TorsionColimit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-!
# The comparison of étale and pro-étale sheaves detects torsion

An étale sheaf of `Λ`-modules `F` is torsion (`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`)
as soon as its pullback `ν^* F` to the pro-étale site has torsion underlying abelian sheaf
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf.of_isTorsion_comparisonUpperStar`).

Both notions are detected by the rationalization `F ⊗ ℚ`, the colimit of the sequence
`F --1--> F --2--> F --3--> ⋯` (`CategoryTheory.Preadditive.rationalizationDiagram`): it vanishes
for torsion sheaves on any site, it is preserved by the left adjoint `ν^*`, whose faithfulness
reflects its vanishing, and its vanishing on the étale site implies torsion stalks.
-/

@[expose] public section

universe u

open CategoryTheory Limits Preadditive

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- An étale sheaf of `Λ`-modules with vanishing rationalization is torsion: the fibre functor
at a geometric point commutes with the colimit, and an element of the fibre which becomes zero
in the colimit of `M --1--> M --2--> M --3--> ⋯` is killed by a positive integer. -/
lemma Scheme.IsTorsionModuleSheaf.of_isZero_colimit_rationalizationDiagram
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsZero (colimit (rationalizationDiagram F))) : IsTorsionModuleSheaf F where
  isTorsion_sheafFiber Ω _ _ s := by
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
    have :=
      ((pointSmallEtale s).skyscraperSheafAdjunction (A := ModuleCat.{u + 1} Λ)).isLeftAdjoint
    have hZ : IsZero (colimit (rationalizationDiagram
        ((pointSmallEtale s).sheafFiber.obj F))) :=
      IsZero.of_iso ((pointSmallEtale s).sheafFiber.map_isZero hF)
        ((HasColimit.isoOfNatIso
          ((pointSmallEtale s).sheafFiber.mapRationalizationDiagramIso F)).symm ≪≫
          (preservesColimitIso (pointSmallEtale s).sheafFiber _).symm)
    intro x
    have : PreservesFilteredColimitsOfSize.{0, 0} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{0, u + 1, 0, u + 1} _
    obtain ⟨n, i, hn⟩ := Concrete.colimit_rep_eq_zero Λ
      (rationalizationDiagram ((pointSmallEtale s).sheafFiber.obj F)) 0 x
      (by rw [hZ.eq_of_tgt (colimit.ι _ 0) 0]; rfl)
    rw [rationalizationDiagram_map] at hn
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨_, Nat.ascFactorial_pos 0 (n - 0), ?_⟩
    rw [ModuleCat.hom_nsmul, LinearMap.smul_apply] at hn
    exact hn

/-- An étale sheaf of `Λ`-modules is torsion if its pullback `ν^* F` to the pro-étale site has
torsion underlying abelian sheaf. -/
lemma Scheme.IsTorsionModuleSheaf.of_isTorsion_comparisonUpperStar
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ((sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F)).IsTorsion) :
    IsTorsionModuleSheaf F := by
  refine .of_isZero_colimit_rationalizationDiagram F ?_
  have h : IsZero ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj
      (colimit (rationalizationDiagram F))) :=
    IsZero.of_iso hF.isZero_colimit_rationalizationDiagram
      (preservesColimitIso (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X) _ ≪≫
        HasColimit.isoOfNatIso
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapRationalizationDiagramIso F))
  rw [IsZero.iff_id_eq_zero]
  refine (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map_injective ?_
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact h.eq_of_src _ _

end AlgebraicGeometry
