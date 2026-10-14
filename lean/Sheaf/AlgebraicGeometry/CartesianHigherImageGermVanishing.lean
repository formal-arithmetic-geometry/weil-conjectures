/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Eventual vanishing of germs of relative higher direct images

Source: Stacks Project, Tag 0EYM, second proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- A stage higher-image germ dying at the limit dies after a stage transition.
This is the kernel criterion for relative higher-image continuity, independently
of invertibility of any exchange map.
Source: Stacks Project, Tag 0EYM, second proof, part (2).
(blueprint: lem-sc-cartesian-higher-image-germ-vanishing)

Proof: represent the stage germ on an affine etale stage neighbourhood. Pullback
of sheaves and geometric stalks identify this representative with a germ on the
limit base. Locally lift the stage higher-image section to the cohomology
presheaf (Tag 03Q8). Its zero limit germ means that, after a further etale
refinement, its cohomology class is zero: both local lifting and local vanishing
are properties of sheafification. Descend these finitely presented affine etale
neighbourhoods and refinements to a common later stage (Tag 0EYL). Apply
cohomology continuity (Tag 09YQ) to the cartesian pullbacks of the neighbourhoods;
a stage class zero at the limit becomes zero at a later stage. The associated
higher-image section, and hence its germ, are zero at that stage. Pasting of
exchange and naturality of the presheaf comparison identify this restriction
with cartesianHigherImageTransition. Cofilteredness supplies a common stage and
handles parallel-arrow equalities; reindex by a directed set if necessary.
No torsion or smoothness is used, and q=0 and zero sheaves are included. -/
theorem exists_cartesianHigherImage_germ_eq_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (s : c.pt.left)
    (i : I) (x : ((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
      (cartesianHigherImageStage D c f F q i))
    (hx : (((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map
      (cartesianHigherImageLeg D c f F q i)) x = 0) :
    ∃ (j : I) (a : j ⟶ i),
      (((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map
        (cartesianHigherImageTransition D c f F q a)) x = 0 := by
  sorry

end AlgebraicGeometry.Etale
