/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.Cohomology.AffineCechInverseImage
import Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural
import Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural

/-! # Canonical additive comparison and its inverse-image square

Source: Stacks Project, Tags 03P2 and 01FD.
(blueprint: lem-pbc-canonical-additive-cohomology-square)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Multiplication by a global function on the lifted additive structure sheaf.
This is a sectionwise construction, with naturality from structural pullback.
Source: Stacks Project, Tag 03P2, the associated abelian sheaf of the unit module.
(blueprint: lem-pbc-canonical-additive-cohomology-square) -/
noncomputable def etaleAdditiveSmul (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf := by
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro U
    exact AddCommGrpCat.ofHom
      { toFun := fun x ↦ ULift.up
          ((show Γ(U.unop.left, ⊤) from x.down) * (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r))
        map_zero' := by
          change ULift.up (0 * (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r)) = ULift.up 0
          rw [zero_mul]
        map_add' := fun x y ↦ by
          apply ULift.ext
          exact add_mul (show Γ(U.unop.left, ⊤) from x.down) y.down _ }
  · intro U V g
    ext x
    apply ULift.ext
    symm
    change g.unop.left.appTop ((show Γ(U.unop.left, ⊤) from x.down) *
        (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r)) =
      (show Γ(V.unop.left, ⊤) from g.unop.left.appTop x.down) *
        (show Γ(V.unop.left, ⊤) from V.unop.hom.appTop r)
    rw [map_mul]
    congr 1
    have hw := congrArg Scheme.Hom.appTop g.unop.w
    rw [Scheme.Hom.comp_appTop] at hw
    exact ConcreteCategory.congr_hom hw r

/-- The coefficient map adjoint to structural pullback on additive sections.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial.
(blueprint: lem-pbc-canonical-additive-cohomology-square) -/
noncomputable def etaleAdditivePullback {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj X.etaleAdditiveSheaf ⟶
      Y.etaleAdditiveSheaf :=
  ((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
    (Scheme.etaleAdditiveSheafToLowerStar g)

/-- The fixed additive structure sheaves admit comparisons compatible with global
multiplication and the canonical inverse-image coefficient map.
Source: Stacks Project, Tag 03P2, theorem
etale-cohomology-theorem-zariski-fpqc-quasi-coherent; Tag 01FD, inverse-image
naturality of the Cech comparison.
(blueprint: lem-pbc-canonical-additive-cohomology-square)

Proof: Choose finite affine open covers of X and Y, refining the target cover so
that each member lies over a source member. Separatedness makes their tuple
intersections affine. For the unit quasi-coherent modules, affine etale
acyclicity in each coefficient universe identifies etale cohomology with the
ordered Cech complex of structural functions. Lowering the finitely many lifted
coordinates identifies that complex with the ordinary unit-module Cech complex.
The natural etale/Zariski and ordinary-H comparisons give e and e'. Multiplication
by a global function acts componentwise on these complexes, so the comparison
intertwines etaleAdditiveSmul with H.map of smulHom. Structural pullback on each
intersection is both the adjoint section map of etaleAdditivePullback and the
underlying coefficient map of unitToPushforwardObjUnit. The inverse-image Cech
comparison identifies the induced cycle-class map with the Ext map using invImage
and constIso. Every class is represented by a cycle, which proves the square.
Refinement naturality makes the chosen comparisons compatible with both maps.
Degree zero is the section map. The empty scheme gives zero complexes and groups.
There is no affine, flat, proper, or invertibility hypothesis on g. -/
theorem exists_canonical_additive_cohomology_square
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    [CompactSpace X] [CompactSpace Y] [X.IsSeparated] [Y.IsSeparated] (n : ℕ) :
    ∃ e : Sheaf.H X.etaleAdditiveSheaf n ≃+
        H (SheafOfModules.unit X.ringCatSheaf) n,
    ∃ e' : Sheaf.H Y.etaleAdditiveSheaf n ≃+
        H (SheafOfModules.unit Y.ringCatSheaf) n,
      (∀ (r : Γ(X, ⊤)) x,
        e (Sheaf.H.map (etaleAdditiveSmul X r) n x) =
          H.map (smulHom (SheafOfModules.unit X.ringCatSheaf) r) n (e x)) ∧
      (∀ (r : Γ(Y, ⊤)) x,
        e' (Sheaf.H.map (etaleAdditiveSmul Y r) n x) =
          H.map (smulHom (SheafOfModules.unit Y.ringCatSheaf) r) n (e' x)) ∧
      ∀ x, e' (Sheaf.H.map (etaleAdditivePullback g) n
          (Etale.cohomologyMap g X.etaleAdditiveSheaf n x)) =
        Sheaf.H.map (coeff g (SheafOfModules.unitToPushforwardObjUnit
          g.toRingCatSheafHom)) n
          (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj
              (SheafOfModules.unit X.ringCatSheaf)) n (e x)) := by sorry

end AlgebraicGeometry.Scheme.Modules
