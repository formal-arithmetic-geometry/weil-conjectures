/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentEtaleExactComparisonData
import all Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison
import Sheaf.AlgebraicGeometry.UnitStructureCoefficientIso

/-! # Exact-functor presentations of normalized coherent comparisons

Source: Stacks Project, Tags 03P2 and 03FD. The data below concern sheaves and
sections; their induced maps in every cohomological degree are constructed by Ext.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

namespace CoherentEtale

attribute [local irreducible] tensorPullback tensorPullbackObj
  tensorSectionsUnit coherentEtaleMap sourceZero
  CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.comp
  CategoryTheory.Abelian.Ext.mapExactFunctor CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Sheaf.H.equiv₀

local instance (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

namespace ExactComparison

/-- The sheaf and section conditions imply all the delta-functor normalization conditions.
Source: Stacks Project, Tag 03FD; naturality of Ext composition and extension classes.
(blueprint: lem-pbc-exact-comparison-normalized). -/
theorem isNormalized {X : Scheme.{u}} (D : ExactComparison X) :
    IsNormalized X (fun F G _ _ φ ↦ coherentEtaleMap F G φ) (D.map) := by
  change IsNormalized X (fun F G _ _ φ ↦ coherentEtaleMap F G φ)
    (fun F _ q ↦ QcoherentNormalizedProof.comparison D.P
      (Abelian.Ext.mk₀ D.integer) (D.coefficient F) q)
  refine ⟨?_, ?_, ?_⟩
  · intro F G _ _ φ q x
    exact QcoherentNormalizedProof.comparison_naturality D.P (Abelian.Ext.mk₀ D.integer)
      (D.coefficient F) (D.coefficient G) ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)
      (coherentEtaleMap F G φ) (D.naturality F G φ) q x
  · intro F _ x
    exact (QcoherentNormalizedProof.comparison_zero D.P (Abelian.Ext.mk₀ D.integer)
      (D.coefficient F) terminalIsTerminal x).trans (by
        have hz := D.zero
        unfold SectionNormalization at hz
        exact hz F x)
  · intro S h₁ h₂ h₃ hS hz ha he q x
    let R := ShortComplex.mk (coherentEtaleMap S.X₁ S.X₂ S.f)
      (coherentEtaleMap S.X₂ S.X₃ S.g) hz
    let f : (S.map (SheafOfModules.toSheaf X.ringCatSheaf)).map D.P ⟶ R :=
      { τ₁ := D.coefficient S.X₁
        τ₂ := D.coefficient S.X₂
        τ₃ := D.coefficient S.X₃
        comm₁₂ := (D.naturality _ _ S.f).symm
        comm₂₃ := (D.naturality _ _ S.g).symm }
    exact QcoherentNormalizedProof.comparison_boundary D.P (Abelian.Ext.mk₀ D.integer)
      (S.map (SheafOfModules.toSheaf X.ringCatSheaf)) R ha he f q x

/-- Every normalized comparison agrees with this explicit Ext construction.
Source: Stacks Project, Tags 03P2 and 03FD; quasi-coherent effacement and uniqueness.
(blueprint: lem-pbc-exact-comparison-normalized). -/
theorem eq_normalized {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (D : ExactComparison X)
    (a : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ), Source X F q ≃+ Target X F q)
    (ha : IsNormalizedCoherentEtaleComparison X a)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (x : Source X F q) :
    a F q x = D.map F q x := by
  let m : Maps X := fun F G _ _ φ ↦ coherentEtaleMap F G φ
  have hm (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale) :
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          (((tensorPullback U.hom).map φ).app ⊤) := by
    exact coherentEtaleMap_app F G φ U
  have h := normalized_unique X m (QcoherentNormalizedProof.effaces X m hm)
    (fun F _ q ↦ (a F q).toAddMonoidHom) D.map ha D.isNormalized
  exact congrArg (fun c : Family X ↦ c F q x) h

end ExactComparison
end CoherentEtale
end
end AlgebraicGeometry.Scheme.Modules
