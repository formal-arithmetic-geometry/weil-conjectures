/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import Sheaf.AlgebraicGeometry.PullbackSectionsComparison
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Constant-module section comparisons on a cartesian square

Source: Stacks Project, Tags 03S2 and 09Z1, degree zero.
(blueprint: lem-weil-pbc-constant-module-pullback-section-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Constant-module direct-image sections identify with abelian global sections
on the etale pullback, compatibly with a cartesian morphism of total spaces.
There is no inverse system, limit cone, stalk, or finiteness hypothesis here.

Source: Stacks Project, Tag 03S2, restriction along an etale morphism;
Tag 09Z1, canonical degree-zero transition maps; Tags 03DB and 03CO, coefficients.
(blueprint: lem-weil-pbc-constant-module-pullback-section-comparison).

Proof: Forget module coefficients to abelian groups. This functor is left adjoint
(restriction of scalars along integers followed by the integer-module equivalence),
and its sheaf functor preserves colimits and sheafification. constantCommuteCompose
therefore identifies the underlying constant module sheaf on any scheme with the
constant abelian sheaf with value M's underlying group, naturally and preserving
constant-presheaf generators. Direct image commutes with forgetting by definition.
For f:Z -> X, the source sections are sections of this constant sheaf over
U times_X Z. Restriction along the etale second projection identifies them with
global sections of its inverse image. The constant pullback comparison identifies
that inverse image with the inverse image along fst of the constant abelian sheaf
G on U; these maps define the additive equivalence e. For a cartesian map m, apply
pullbackSections_comparison to the constant abelian sheaf on X. Its canonical
constant pullback comparisons identify the sheaves there with the constant sheaves
here. Naturality of the adjunction unit moves those comparisons through the units;
uniqueness of the constant-sheaf left-adjoint comparison and inverse-image
composition coherence identify the two composites. The two equations for m ensure
the fiber-product pasting is the same canonical map. Thus the resulting equality
is the displayed compatibility with constantModulePushforwardMap. No equality of
limit representatives is asserted. Empty pullbacks and zero coefficients are
covered by the same natural isomorphisms. -/
theorem exists_constantModule_pullback_section_comparison
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} (U : X.Etale) :
    let A := AddCommGrpCat.{u + 1}
    let G := (constantSheaf U.left.smallEtaleTopology A).obj
      ((forget₂ (ModuleCat.{u + 1} Λ) A).obj M)
    ∃ e : ∀ (Z : Scheme.{u}) (f : Z ⟶ X),
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
          (op U) ≃+
      (Sheaf.Γ (pullback U.hom f).smallEtaleTopology A).obj
        ((upperStar A (pullback.fst U.hom f)).obj G),
      ∀ {Z W : Scheme.{u}} (g : W ⟶ Z) (f : Z ⟶ X) (h : W ⟶ X)
        (w : g ≫ f = h) (m : pullback U.hom h ⟶ pullback U.hom f)
        (hm : m ≫ pullback.fst U.hom f = pullback.fst U.hom h)
        (_hm' : m ≫ pullback.snd U.hom f = pullback.snd U.hom h ≫ g)
        (z : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
            (op U)),
        e W h ((constantModulePushforwardMap Λ M f h g w).hom.app (op U) z) =
          (globalSectionsUpperStarMap A m
              ((upperStar A (pullback.fst U.hom f)).obj G) ≫
            (Sheaf.Γ (pullback U.hom h).smallEtaleTopology A).map
              ((upperStarComp A m (pullback.fst U.hom f) (pullback.fst U.hom h)
                hm.symm).inv.app G)) (e Z f z) := by
  sorry

end AlgebraicGeometry.Etale
