/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpaceAmbientTower
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization

/-! # Compact supports and the explicit affine-space tower

Source: blueprint cor-amb-affine-space-adjunction, proof steps 1, 3, 5 and 6.
(blueprint: lem-amb-affine-space-tower-left-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Identify the concrete tower of open extension and proper direct image with compact supports.
Source: blueprint cor-amb-affine-space-adjunction, proof steps 1, 3, 5 and 6.
(blueprint: lem-amb-affine-space-tower-left-comparison).

Proof: In dimension zero the projection is an isomorphism. The normalized comparison
identifies its exact sum extension with compact supports. At the successor step the chart
`ambientSuccessorChart` and projective-line projection form a compactification of their
composite. Compactification independence identifies its open/proper functor with compact
supports of that composite. Whisker this comparison and the induction comparison, then use
unbounded composition. The coordinate identity `ambientSuccessorChart_over` identifies the
composite morphism with the affine-space projection. All comparisons are natural functor
isomorphisms on the entire unbounded categories. -/
theorem nonempty_ambientTowerLeftComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    Nonempty (ambientTowerLeft A S d ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (ambientAffine S d ↘ S)) := by
  induction d with
  | zero =>
    obtain ⟨norm⟩ := nonempty_etaleCompactSupportNormalization A
    exact ⟨(norm.comparison (ambientAffine S 0 ↘ S)
      (HasCompactification.compactification (ambientAffine S 0 ↘ S))).symm⟩
  | succ d ih =>
    obtain ⟨e⟩ := ih
    let j := ambientSuccessorChart S d
    let q := (ProjectiveLine (ambientAffine S d) ↘ ambientAffine S d)
    let p := (ambientAffine S d ↘ S)
    let c : Compactification (j ≫ q) := {
      Z := ProjectiveLine (ambientAffine S d)
      i := j
      g := q
      comm := rfl
      isProper := inferInstance
      isOpenImmersion := inferInstance }
    have : HasCompactification (j ≫ q) := c.hasCompactification
    have heq : (j ≫ q) ≫ p = (ambientAffine S (d + 1) ↘ S) := by
      simpa only [Category.assoc] using ambientSuccessorChart_over S d
    have : HasCompactification ((j ≫ q) ≫ p) :=
      HasCompactification.of_eq heq.symm
    refine ⟨?_⟩
    exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ e) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedLowerShriekIso A c) _ ≪≫
      unboundedEtaleLowerShriekCompIso A (j ≫ q) p ≪≫
      unboundedEtaleLowerShriekCongr A heq

end AlgebraicGeometry.Etale
