/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.SixFunctors.DetSfCompBaseChangeDefs

/-!
# Pasting compact-support exchange with dense refinements

Source: blueprint det-sf-comp-composition-base-change, proof steps 4--7.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The local refinement-pasting equation for the specified exchange composite.
This statement involves one refinement and one dense refinement after pullback; it
neither chooses compactification comparisons nor asserts that exchange is invertible.

Source: blueprint det-sf-comp-composition-base-change, proof (3), the equation obtained
by applying proper pushforward to the identity-on-open comparison.
(blueprint: lem-sfb-compact-support-refinement-base-change).

Proof: the two composite refinements from the dense source `w` to `c.baseChange v`
agree, since they agree on the distinguished open and the target is separated over
Y'. Transport the proper compositors to the canonical derived adjunction compositors
using the K-injective normalization. On the open square, the unit, square comparison
and counit defining `detSfOpenBaseChangeMap` restrict to identity. The same holds for
the normalized localizing refinement maps. The precise proper base-change mate for
`h` restricts to identity on the open, by baseChangeIdentityOpenRestriction. Transpose
the two maps from the base-changed open extension to the proper image from `w`
under its open adjunction. Their adjuncts are equal by these identity restrictions,
so injectivity of the adjunction Hom equivalence equates the original maps. Apply
the proper pushforward for c and precompose with its proper base-change mate.
Naturality moves the refinement arrow across that mate. Horizontal mate pasting
replaces the two proper mates by the mate for d. The normalized compositor cancels
with the inverse compositor in compactificationRefinementComponent. The resulting
component equation is precisely the displayed formula. No base-changed open is
assumed dense: density is required only for the chosen further source w. The proof
uses no invertibility of a proper mate or of a refinement map and applies to every
unbounded K, including zero objects and empty distinguished opens. -/
theorem compactSupportRefinement_baseChange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (o : ∀ c : Compactification f,
      D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
        detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧))
    (ho : ∀ c, (o c).inv = detSfOpenBaseChangeMap Λ f v c)
    (c : Compactification f) (d : Compactification.DenseBoundaryCompactification f)
    (h : d.obj ⟶ detSfBoundaryCompactification c)
    (w : Compactification.DenseBoundaryCompactification (pullback.snd f v))
    (hd : w.obj ⟶ detSfBoundaryCompactification (d.obj.obj.obj.baseChange v))
    (hc : w.obj ⟶ detSfBoundaryCompactification (c.baseChange v))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (detSfDerivedPullback Λ v).map (compactificationRefinementComponent Λ h K) ≫
        (detSfCompactSupportBaseChangeComposite Λ f v d.obj.obj.obj
          (o d.obj.obj.obj)).app K ≫
        compactificationRefinementComponent Λ hd
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) =
      (detSfCompactSupportBaseChangeComposite Λ f v c (o c)).app K ≫
        compactificationRefinementComponent Λ hc
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
