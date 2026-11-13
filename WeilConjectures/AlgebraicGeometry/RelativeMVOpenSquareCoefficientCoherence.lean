/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.CanonicalRelativeMVOpenSquareCoefficientCoherence

/-! # Coefficient coherence for one nested open square

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The coefficient comparisons commute with the inclusion W ⊆ U, before any
counit or base-change mate is applied. -/
theorem relativeMV_open_square_coefficient_coherence
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (W U : X.Opens) (i : W ≤ U)
    (c : derivedPullback U.ι ⋙ derivedPullback (X.homOfLE i) ≅ derivedPullback W.ι)
    (c' : derivedPullback (pullback.fst g' U.ι) ⋙
      derivedPullback (relativeMVOpenLift g' i) ≅ derivedPullback (pullback.fst g' W.ι))
    (s : ∀ N : schemeDerivedCategory X,
      (derivedPullback (pullback.snd g' U.ι)).obj ((derivedPullback U.ι).obj N) ⟶
        (derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj N))
    (t : ∀ N : schemeDerivedCategory X,
      (derivedPullback (pullback.snd g' W.ι)).obj ((derivedPullback W.ι).obj N) ⟶
        (derivedPullback (pullback.fst g' W.ι)).obj ((derivedPullback g').obj N))
    (d : derivedPullback (X.homOfLE i) ⋙ derivedPullback (pullback.snd g' W.ι) ≅
      derivedPullback (pullback.snd g' U.ι) ⋙ derivedPullback (relativeMVOpenLift g' i))
    (hc : c = relativeMVComp (X.homOfLE i) U.ι ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.homOfLE_ι X i)))
    (hc' : c' = relativeMVComp (relativeMVOpenLift g' i) (pullback.fst g' U.ι) ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (pullback.lift_fst _ _ _)))
    (hs : ∀ N, s N = (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app N ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' U.ι) g').inv.app N)
    (ht : ∀ N, t N = (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app N ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app N)
    (hd : d = relativeMVComp (pullback.snd g' W.ι) (X.homOfLE i) ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k)
        (pullback.lift_snd _ _ _).symm) ≪≫
      (relativeMVComp (relativeMVOpenLift g' i) (pullback.snd g' U.ι)).symm) :
    ∀ N : schemeDerivedCategory X,
    (derivedPullback (pullback.snd g' W.ι)).map (c.hom.app N) ≫ t N =
      d.hom.app ((derivedPullback U.ι).obj N) ≫
        (derivedPullback (relativeMVOpenLift g' i)).map (s N) ≫
        c'.hom.app ((derivedPullback g').obj N)  := by
  intro N
  rw [hc, hc', hs N, ht N, hd]
  exact canonical_relativeMV_open_square_coefficient_coherence g' W U i N


end AlgebraicGeometry
