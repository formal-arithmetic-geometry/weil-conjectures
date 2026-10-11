/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal
import Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Universal first order thickenings under flat base change

Source: Stacks Project, More on Morphisms, Lemmas 04F8 and 04F9; Morphisms,
Lemmas 01R4 and 0473 (blueprint: lem-weil-pbc-universal-thickening-flat-base-change).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flat base change preserves universal first order thickenings and identifies their
conormal sheaves. The two projection equations specify `iZ = id_X × iW` uniquely.
The map in the final clause is exactly the canonical map of
`Scheme.Modules.closedImmersion_conormal_functorial`, not an arbitrary module isomorphism.
The proof witnesses `hu` and `HZ` allow the conormal definition to use this thickening.

Source: Stacks Project, More on Morphisms, Lemmas 04F8 and 04F9, with Morphisms,
Lemmas 01R4 and 0473 (blueprint: lem-weil-pbc-universal-thickening-flat-base-change).
Proof:
1. The first projection is formally unramified by base change of `hW`
   (lem-weil-pbc-formally-unramified-base-change).
2. The square of `iZ`, `iW` and the second projections is cartesian by
   lem-weil-pbc-cartesian-square-pasting. Thus iZ is a first order thickening by
   lem-weil-pbc-first-order-thickening-base-change.
3. Given a test thickening over X mapping into Z, compose its maps with g and the
   second projection. The universal property of HW gives a unique map into W'.
   Pair it with the test scheme's map to X to obtain its unique map into Z'.
   This is def-weil-pbc-universal-first-order-thickening and the fibre product property.
4. The second projection from Z' is flat by base change of g
   (lem-weil-pbc-flat-morphism-base-change).
5. By def-weil-pbc-conormal-sheaf-formally-unramified, compute the conormal sheaves
   using HW and HZ; uniqueness of universal thickenings justifies these choices
   (lem-weil-pbc-universal-first-order-thickening-exists). Their canonical map is the
   map of lem-weil-pbc-closed-immersion-conormal-functorial, induced by the ambient
   second projection on ideals and def-pc-module-pullback. The cartesian square and
   its flat ambient map make it an isomorphism by
   lem-weil-pbc-closed-immersion-conormal-flat-base-change. -/
theorem universalFirstOrderThickening_flat_base_change
    {W W' X Y : Scheme.{u}} (hW : W ⟶ Y) [FormallyUnramified hW]
    (g : X ⟶ Y) [Flat g] (iW : W ⟶ W') (s : W' ⟶ Y)
    (HW : IsUniversalFirstOrderThickening hW iW s)
    (iZ : pullback g hW ⟶ pullback g s)
    (_hfst : iZ ≫ pullback.fst g s = pullback.fst g hW)
    (hsnd : iZ ≫ pullback.snd g s = pullback.snd g hW ≫ iW) :
    ∃ hu : FormallyUnramified (pullback.fst g hW),
      ∃ HZ : IsUniversalFirstOrderThickening (pullback.fst g hW) iZ (pullback.fst g s),
        Flat (pullback.snd g s) ∧
          ∀ c : (Scheme.Modules.tensorPullback (pullback.snd g hW)).obj
              (formallyUnramifiedConormal hW iW s HW) ⟶
            @formallyUnramifiedConormal _ _ _ (pullback.fst g hW) hu
              iZ (pullback.fst g s) HZ,
            c = Classical.choose ((Classical.choose_spec
              (@Scheme.Modules.closedImmersion_conormal_functorial
                (pullback g s) (pullback g hW) W' W iZ iW HZ.1.1 HW.1.1
                (pullback.snd g s) (pullback.snd g hW) hsnd).2).2) → IsIso c := by
  sorry

end AlgebraicGeometry
