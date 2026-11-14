/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicIsomorphismSections
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLisseTowerSectionCover

/-! # Compatible algebraic stalk trivialization of finite perfect quotient diagrams

Source: Stacks Project, Tag 09C6, with the finite-stalk tower argument of Tag 09BV.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Uniform finite perfect local models admit compatible algebraic stalk trivializations.

Source: Stacks Project, Tag 09C6, the choice of the algebraic stalk system and of
compatible local markings, using Tags 09B1 and 09BV. -/
theorem finitePerfectAdicTower_extraction
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        Nonempty (FinitePerfectAdicLocalTower X d U ((completedAdicReduction X d).obj M)) := by
  classical
  obtain ⟨𝒱, h𝒱⟩ := finitePerfectAdic_stalk_models X d φ hφ hcompat M hmodels
  choose T hperfect hmark using h𝒱
  choose I r ev hI hne hred using fun i ↦ finitePerfectAdic_isomorphism_sections
    X d φ hφ hcompat M (𝒱.etalePrecoverageToEtale i) (T i) (hperfect i) (hmark i)
  choose J U hcov ha hw s hs using fun i ↦
    finite_lisse_tower_section_cover (𝒱.etalePrecoverageToEtale i).left
      (I i) (r i) (hI i) (hne i)
  let C : Cover.{t} proetalePrecoverage X :=
    ⟨𝒱.toPreZeroHypercover, etalePrecoverage_le_proetalePrecoverage _ 𝒱.mem₀⟩
  let D (i : 𝒱.I₀) : Cover.{t} proetalePrecoverage (𝒱.X i) :=
    ⟨⟨J i, fun j ↦ (U i j).left, fun j ↦ (U i j).hom⟩, hcov i⟩
  let Y (ij : Σ i, J i) : X.ProEt :=
    finitePerfectAdicChartObject (𝒱.etalePrecoverageToEtale ij.1) (U ij.1 ij.2)
  have ht : IsTerminal (ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  let τ : ProEt.mk (𝟙 X) ≅ ⊤_ X.ProEt := ht.uniqueUpToIso terminalIsTerminal
  let f (ij : Σ i, J i) : Y ij ⟶ ⊤_ X.ProEt :=
    MorphismProperty.Over.homMk (B := ProEt.mk (𝟙 X)) (Y ij).hom
      (Category.comp_id _) ≫ τ.hom
  refine ⟨Sieve.ofArrows Y f, ?_, ?_⟩
  · apply ProEt.mem_topology_iff.mpr
    refine ⟨Presieve.ofArrows Y f, ?_, Sieve.le_generate _⟩
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    have : IsIso τ.hom.left := (ProEt.forget X ⋙ Over.forget X).map_isIso τ.hom
    change (Presieve.ofArrows (fun ij ↦ (C.bind D).X ij)
      (fun ij ↦ (C.bind D).f ij ≫ τ.hom.left)) ∈ _
    exact ((C.bind D).pushforward τ.hom.left
      (Precoverage.mem_coverings_of_isIso _)).mem₀
  · intro W g hg
    obtain ⟨⟨i, j⟩, a, _⟩ := (Sieve.mem_ofArrows_iff Y f g).mp hg
    let e (n : ℕ) := ev i (U i j) (ha i j) (hw i j) W a n (s i j n)
    let α : finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M) ⟶
        finitePerfectAdicModelDiagram X d W (T i) :=
      NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
        intro n
        have h := hred i (U i j) (ha i j) (hw i j) W a n (s i j (n + 1))
        rw [hs i j n] at h
        exact h)
    have (n : ℕᵒᵖ) : IsIso (α.app n) := (e n.unop).isIso_hom
    have : IsIso α := NatIso.isIso_of_isIso_app α
    exact ⟨{ toFinitePerfectAdicAlgebraTower := T i, comparison := ⟨asIso α⟩ }⟩

end AlgebraicGeometry.Scheme
