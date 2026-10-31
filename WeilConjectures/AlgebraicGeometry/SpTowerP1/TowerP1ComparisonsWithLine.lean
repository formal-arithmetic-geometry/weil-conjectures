/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1EtaleOriginComparisons

/-! # The shifted Tate line in the projective-line comparison domain

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Construction and Levels (blueprint: lem-sp-tower-p1-etale-origin-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- The same canonical comparisons, exposing their specialization to the shifted Tate line.
Source: Construction, the invertible-twist comparison; Levels, the root-site comparison
(blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
structure EtaleOriginComparisonsWithLine (p : Presentation l E S hS) (d : Maps l E p) :
    Prop extends EtaleOriginComparisons l E p d where
  line_domain : domain l E p.classes.base (ProjectiveLine S)
    ((SpTowerClasses.line l E p.classes.chernP)⟦(2 : ℤ)⟧)

/-- Canonical comparisons including the Tate-line specialization implicit in their words.
Source: Construction and Levels (blueprint: lem-sp-tower-p1-etale-origin-comparisons).

Proof plan: use towerP1EtaleOriginComparisons for all its canonical comparisons, boundedness,
exact diagonal image, naturality, and finite-level equations. The root-tower line is a degree-zero
module; shifting it by two gives lower bound -2. At each positive level its root-site comparison
is the pullback of the ordinary etale rank-one Tate module, shifted by two. The retained etale
object and that comparison give the required origin witness, independently at every level.
This is precisely Steps 3--5 of the comparison node; it adds no Tor or constructibility condition.
-/
theorem towerP1EtaleOriginComparisonsWithLine (S : Scheme.{u})
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∀ p : Presentation l E S hS, ∃ d : Maps l E p,
      EtaleOriginComparisonsWithLine l E p d := by
  intro p
  obtain ⟨d, h⟩ := towerP1EtaleOriginComparisons l E S hS p
  refine ⟨d, { toEtaleOriginComparisons := h, line_domain := ?_ }⟩
  constructor
  · refine ⟨-2, ?_⟩
    change DerivedCategory.IsGE
      (((DerivedCategory.singleFunctor _ 0).obj
        (SpTowerClasses.lineModule l E p.classes.chernP))⟦(2 : ℤ)⟧) (-2)
    exact DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)
  · intro n
    let : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
    obtain ⟨c, _⟩ := h.levels n
    let L : DerivedCategory.Plus
        (Sheaf (ProjectiveLine S).smallEtaleTopology
          (ModuleCat.{u + 1} (levelRing l E n))) :=
      ⟨(c.lineP l E n).etale, ⟨-2, by
        change DerivedCategory.IsGE
          (((DerivedCategory.singleFunctor _ 0).obj _)⟦(2 : ℤ)⟧) (-2)
        exact DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩⟩
    refine ⟨{
      level := (comparisonUpperStar
        (ModuleCat.{u + 1} (levelRing l E n))
          (ProjectiveLine S)).mapDerivedCategoryPlus.obj L
      realization := ?_
      witness := ⟨L, Iso.refl _⟩ }⟩
    have : IsIso (c.lineP l E n).comparison := by
      dsimp only [ProjectiveCoordinates.lineP, lineWord]
      infer_instance
    exact asIso (c.lineP l E n).comparison

end AlgebraicGeometry.ProEtale.SpTowerP1
