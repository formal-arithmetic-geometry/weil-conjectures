/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps

/-! # Restricting the counit in a single open base-change square

Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 0D5S.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The single open-square counit calculation. There is no structure morphism `f`
or second base-change morphism `g`, and no relative direct image to a base.
Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 0D5S.
(blueprint: new-relative-mv-open-square-counit).
Proof: Transpose the base-change map for U → X using its defining 08HY formula.
The target restriction counit is the transpose after the comparison for W' → U' → X'.
Naturality moves the base-change morphism through the inverse comparison. The
triangle identity cancels the U'-adjunction unit, leaving the pullback of the
U-adjunction counit and the U coefficient comparison. Associativity of the
canonical pullback comparisons on W → U → X and W' → U' → X', together with
both projection identities of relativeMVOpenLift, identifies these factors with
the W coefficient comparison, the pulled-back inverse W → U → X comparison,
the pulled-back U-counit, and the W coefficient comparison at K. Scheme.homOfLE_ι
identifies the open composite, and proof irrelevance identifies all equality
transports. The inverse W coefficient comparison is then canceled. This argument
uses neither strictness nor nonemptiness of the opens and works also for K = 0. -/
theorem relativeMV_open_square_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (W U : X.Opens) (i : W ≤ U) :
    let C := (schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)
    let c := relativeMVComp (X.homOfLE i) U.ι ≪≫
      eqToIso (congrArg (fun t : W.toScheme ⟶ X ↦ derivedPullback t)
        (Scheme.homOfLE_ι X i))
    let c' := relativeMVComp (relativeMVOpenLift g' i) (pullback.fst g' U.ι) ≪≫
      eqToIso (congrArg (fun t : pullback g' W.ι ⟶ X' ↦ derivedPullback t)
        (pullback.lift_fst _ _ _))
    let γ (N : schemeDerivedCategory X) :=
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app N ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app N
    let θ := (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' U.ι) g').inv.app K
    γ C ≫ (derivedPullback (pullback.fst g' W.ι)).map
        (schemeDerivedBaseChangeMap U.ι (pullback.fst g' U.ι) g'
            (pullback.snd g' U.ι) (pullback.condition (f := g') (g := U.ι)).symm
            ((derivedPullback U.ι).obj K) ≫
          (schemeDerivedDirectImage (pullback.fst g' U.ι)).map θ) ≫
      c'.inv.app ((schemeDerivedDirectImage (pullback.fst g' U.ι)).obj
        ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      (derivedPullback (relativeMVOpenLift g' i)).map
        ((relativeMVAdj (pullback.fst g' U.ι)).counit.app
          ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      c'.hom.app ((derivedPullback g').obj K) =
      (derivedPullback (pullback.snd g' W.ι)).map
        (c.inv.app C ≫ (derivedPullback (X.homOfLE i)).map
          ((relativeMVAdj U.ι).counit.app ((derivedPullback U.ι).obj K)) ≫ c.hom.app K) ≫
      γ K := by sorry

end AlgebraicGeometry
