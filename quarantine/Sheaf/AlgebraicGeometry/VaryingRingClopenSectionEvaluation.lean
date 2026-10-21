/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors

/-!
# Coefficient realization of the clopen section factor

Source: the clopen construction in Stacks 0F7B and Zheng, Construction 4.1.
The comparison concerns the clopen projector and its outgoing composition identifications.
(blueprint: lem-sp-varying-ring-clopen-section-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- Coefficient evaluation preserves the clopen section projection and its
outgoing composition identifications.
Source: Stacks 0F7B, open case, and 09AE; Zheng, Construction 4.1
(blueprint: lem-sp-varying-ring-clopen-section-evaluation).
Proof: put q = pullback.snd p i, b = pullback.fst p i and s = squareLift k r p i h.
The lift s is open and closed. In the ordinary module category the normalized
map pi_s restricts to the open-adjunction unit on its image and to zero on the
complement. The clopen sheaf product decomposition therefore determines it.
Module evaluation preserves these two restrictions and the unit. Consequently
it gives the single-coefficient clopen projection, and strict-tower evaluation
gives the same map termwise. Compose with b_!, then use the specified
identifications b_! s_! = k_! and s^* q^* = r^*. Coefficient evaluation preserves
the pullback compositor by the unit-normalized pull/direct mate calculation;
it preserves the open compositor by taking open-adjunction mates. Equality
transport is proof-irrelevant. These equations identify both evaluated section
factors with the single-coefficient one. Carry out the varying-system argument
on complexes and apply Q, since sectionArrow is the exact localization of the
ordinary section factor. For strict towers, the derived units and the inverse
open-to-direct comparison localize the same ordinary clopen projection. The
localization factor isomorphisms and essential surjectivity extend the equations
to arbitrary derived inputs. No cartesian open base-change comparison enters
this factor, and no equality of arbitrary derived maps is detected by evaluation. -/
theorem clopenSectionEvaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (n : ℕ) :
    ∃ a : (StrictTower.modulePullback (R n) (pullback.snd p i)).mapDerivedCategory ⋙
          (StrictTower.moduleJ (R n) (pullback.fst p i)).mapDerivedCategory ⟶
        (StrictTower.modulePullback (R n) r).mapDerivedCategory ⋙
          (StrictTower.moduleJ (R n) k).mapDerivedCategory,
      (∀ N : Derived R φ S,
        (ev R φ W n).map ((sectionArrow R φ k r p i h).app N) ≫
            (evalJ R φ k n).hom.app ((G R φ r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((evalG R φ r n).hom.app N) =
          (evalJ R φ (pullback.fst p i) n).hom.app
              ((G R φ (pullback.snd p i)).obj N) ≫
            (StrictTower.moduleJ (R n) (pullback.fst p i)).mapDerivedCategory.map
              ((evalG R φ (pullback.snd p i) n).hom.app N) ≫ a.app ((ev R φ S n).obj N)) ∧
      (∀ N : StrictTower.Derived (R n) S,
        (StrictTower.ev (R n) W 0).map ((strictSectionArrow (R n) k r p i h).app N) ≫
            (StrictTower.evalJ (R n) k 0).hom.app ((StrictTower.G (R n) r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((StrictTower.evalG (R n) r 0).hom.app N) =
          (StrictTower.evalJ (R n) (pullback.fst p i) 0).hom.app
              ((StrictTower.G (R n) (pullback.snd p i)).obj N) ≫
            (StrictTower.moduleJ (R n) (pullback.fst p i)).mapDerivedCategory.map
              ((StrictTower.evalG (R n) (pullback.snd p i) 0).hom.app N) ≫
            a.app ((StrictTower.ev (R n) S 0).obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
