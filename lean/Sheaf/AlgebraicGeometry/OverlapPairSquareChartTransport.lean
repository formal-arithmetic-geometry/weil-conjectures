/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons

/-! # Transport of pair squares through chart refinements

Source: Stacks Project, Tag 01ZR, first proof; Mathlib pullHom composition.
(blueprint: lem-pc-overlap-pair-square-chart-transport). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

/-- Transport a pair square along a diagram of cover charts, using specified chart isomorphisms.
Source: Stacks Project, Tag 01ZR, first proof, successive restriction; Mathlib
Sites/Descent/IsPrestack.lean, pullHom_pullHom.
(blueprint: lem-pc-overlap-pair-square-chart-transport).

Proof: Write K for the map from the later stage overlap to the earlier stage overlap,
constructed by pullback.lift from fst followed by ρ a and snd followed by ρ b. Write L
for the analogous map between the limit overlaps, using δ a and δ b. Their lift
conditions follow from hr and hδf. Apply the module pullback functor along L to hs and
conjugate its ends by the pullback composition comparisons for the overlap projections.
Naturality of mapComp moves the pulled ε components through these comparisons.
DescentData.pullHom_hom for the restriction datum of M identifies its pulled transition
with the later limit transition, using hδf.

The two composites from the later limit overlap to the earlier stage overlap, through L
and the old limit-to-stage overlap map or through the new limit-to-stage overlap map and K,
are equal: their fst and snd projections agree by hδv, so pullback.hom_ext applies.
The identity pullHom_pullHom therefore identifies the middle map with the pullback of
the base-changed stage map. Apply the mapComp pentagon to the three successive projections,
and naturality to the chart isomorphisms c. Cancel each adjacent composition comparison
with its inverse. This puts the pullbacks of c a.inv and c b.hom at the two ends of the
stage map, giving exactly the explicit map in the conclusion. The remaining component
comparisons are the five displayed factors in hε; replace them with ε' using hε. The
resulting equality is the later overlapPairSquare. These are universal pullback maps and
functorial identities, so empty charts, empty overlaps and arbitrary index maps α cause
no exceptions. No identity or cocycle equation for φ is used. -/
theorem overlap_pair_square_chart_transport
    {Y Y' Z : Scheme.{u}} (V : Y.OpenCover.{u}) (V' : Y'.OpenCover.{u})
    (α : V'.I₀ → V.I₀) (r : Y' ⟶ Y) (ρ : ∀ d, V'.X d ⟶ V.X (α d))
    (hr : ∀ d, ρ d ≫ V.f (α d) = V'.f d ≫ r)
    (p : Z ⟶ Y) (p' : Z ⟶ Y') (hp : p' ≫ r = p)
    (A : (d : V.I₀) → (V.X d).Modules)
    (A' : (d : V'.I₀) → (V'.X d).Modules) (M : Z.Modules)
    (c : ∀ d, (Scheme.Modules.pullback (ρ d)).obj (A (α d)) ≅ A' d)
    (δ : ∀ d, (V'.pullback₁ p').X d ⟶ (V.pullback₁ p).X (α d))
    (hδf : ∀ d, δ d ≫ (V.pullback₁ p).f (α d) = (V'.pullback₁ p').f d)
    (hδv : ∀ d, δ d ≫ V.pullbackHom p (α d) = V'.pullbackHom p' d ≫ ρ d)
    (ε : ∀ d, (Scheme.Modules.pullback (V.pullbackHom p d)).obj (A d) ≅
      (Scheme.Modules.pullback ((V.pullback₁ p).f d)).obj M)
    (ε' : ∀ d, (Scheme.Modules.pullback (V'.pullbackHom p' d)).obj (A' d) ≅
      (Scheme.Modules.pullback ((V'.pullback₁ p').f d)).obj M)
    (hε : ε' =
    (fun d ↦ (Scheme.Modules.pullback (V'.pullbackHom p' d)).mapIso (c d).symm ≪≫
      pullbackCompOfEq (V'.pullbackHom p' d) (ρ d)
        (δ d ≫ V.pullbackHom p (α d)) (hδv d).symm (A (α d)) ≪≫
      (pullbackCompOfEq (δ d) (V.pullbackHom p (α d))
        (δ d ≫ V.pullbackHom p (α d)) rfl (A (α d))).symm ≪≫
      (Scheme.Modules.pullback (δ d)).mapIso (ε (α d)) ≪≫
      pullbackCompOfEq (δ d) ((V.pullback₁ p).f (α d))
        ((V'.pullback₁ p').f d) (hδf d) M))
    (a b : V'.I₀)
    (φ : (Scheme.Modules.pullback (pullback.fst (V.f (α a)) (V.f (α b)))).obj
        (A (α a)) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f (α a)) (V.f (α b)))).obj
        (A (α b)))
    (hs : overlapPairSquare V A p
      ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M) ε (α a) (α b) φ) :
    overlapPairSquare V' A' p'
      ((modulesPseudofunctor.toDescentData (V'.pullback₁ p').f).obj M)
      ε' a b
      ((Scheme.Modules.pullback (pullback.fst (V'.f a) (V'.f b))).map (c a).inv ≫
        modulesPseudofunctor.overlapPairBaseChangeHom
          (V.f (α a)) (V.f (α b)) r (ρ a) (ρ b) (V'.f a) (V'.f b)
          (hr a) (hr b) (A (α a)) (A (α b)) φ ≫
        (Scheme.Modules.pullback (pullback.snd (V'.f a) (V'.f b))).map (c b).hom) := by
  sorry

end AlgebraicGeometry
