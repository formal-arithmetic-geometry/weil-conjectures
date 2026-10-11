/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.AffineConormalSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Functoriality of conormal sheaves of closed immersions

Source: Stacks Project, Morphisms, Lemma 01R4, Definition 01R2 and Lemma 01R3
(blueprint: lem-weil-pbc-closed-immersion-conormal-functorial).
-/

@[expose] public section

universe uc

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The extended ideal is contained in the ideal of the source closed subscheme.
The map `γ` is fixed by its values on pullbacks of ideal sections. The unique map `c`
is the pullback of `γ`, expressed by the equality of its adjoint with the composite
of the units and `γ`; pushforward comparison maps implement the commutative square.
The affine clause uses ideal sections before their conormal classes: by
`affine_conormal_sections`, the units on these sections are precisely `a mod I²`.
The final affine equation explicitly sends that class to the class of `g.appLE` applied
to its ideal representative. The existential section `s` also records ideal containment
on these affine opens, without choosing coordinates or a second conormal definition.

Source: Stacks Project, Morphisms, Lemma 01R4 (closed immersion case), with 01R2 and 01R3
(blueprint: lem-weil-pbc-closed-immersion-conormal-functorial).
Proof:
1. A section of `i'.ker` vanishes on `Z'`. Commutativity shows its image under `g`
vanishes on `Z`, hence belongs to `i.ker` (def-sbc-closed-immersion-ideal-sheaf).
This gives the containment of def-nagata-extended-ideal and the corestriction `γ`.
2. Apply tensor pullback along `i` and the composition comparison of
   def-pc-module-pullback. Under adjunction this is precisely the displayed equality.
3. On affine opens, the restriction of `g` gives `g.appLE`; the preceding containment
sends `I'` into `I`, hence also `I'²` into `I²`, inducing the map of quotients.
4. The identifications of lem-weil-pbc-affine-conormal-sections send an ideal section
   to its pullback unit. Unwinding the construction gives the affine equation. These
   affine opens cover `Z`, and the classes of ideal sections generate each pulled-back
   conormal module (lem-weil-pbc-module-pullback-affine-sections); consequently the
   affine equation determines `c` uniquely. -/
theorem closedImmersion_conormal_functorial
    {X Z X' Z' : Scheme.{uc}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i') :
    i'.ker.comap g ≤ i.ker ∧
      ∃ γ : (tensorPullback g).obj i'.ker.toModules ⟶ i.ker.toModules,
        (∀ (U' : X'.Opens) (s' : Γ(i'.ker.toModules, U')),
          i.ker.toModulesι.app (g ⁻¹ᵁ U')
              (γ.app (g ⁻¹ᵁ U')
                (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
                  i'.ker.toModules).app U' s')) =
            g.app U' (i'.ker.toModulesι.app U' s')) ∧
        ∃! c : (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules) ⟶
            (tensorPullback i).obj i.ker.toModules,
          (((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
              i'.ker.toModules) ≫
            (pushforward i').map
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
                ((tensorPullback i').obj i'.ker.toModules)) ≫ (pushforward f).map c) ≫
            (pushforwardComp f i').hom.app ((tensorPullback i).obj i.ker.toModules) ≫
            (pushforwardCongr h.symm).hom.app ((tensorPullback i).obj i.ker.toModules) =
          ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
              i'.ker.toModules) ≫
            (pushforward g).map
              (γ ≫ ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules)) ≫
            (pushforwardComp i g).hom.app ((tensorPullback i).obj i.ker.toModules)) ∧
          ∀ (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1)
            (s' : Γ(i'.ker.toModules, U'.1)),
            ∃ s : Γ(i.ker.toModules, U.1),
              i.ker.toModulesι.app U.1 s = g.appLE U'.1 U.1 H
                (i'.ker.toModulesι.app U'.1 s') ∧
              ((tensorPullback i).obj i.ker.toModules).val.map
                (homOfLE (i.preimage_mono H)).op
                ((((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
                    i'.ker.toModules) ≫
                  (pushforward i').map
                    (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
                      ((tensorPullback i').obj i'.ker.toModules)) ≫
                        (pushforward f).map c) ≫
                  (pushforwardComp f i').hom.app ((tensorPullback i).obj i.ker.toModules) ≫
                  (pushforwardCongr h.symm).hom.app
                    ((tensorPullback i).obj i.ker.toModules)).app U'.1 s') =
                ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                  i.ker.toModules).app U.1 s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
