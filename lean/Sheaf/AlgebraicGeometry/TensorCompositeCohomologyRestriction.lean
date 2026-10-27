/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # Cohomology restriction with tensor-composition coefficients -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] RingedSpace.moduleCohomology tensorPullback tensorPullbackObj
  tensorSectionsComp moduleCohomologyFMap

/-- Transport of a tensor-pullback coefficient along an equality of scheme maps.
Source: equality substitution; Stacks Project, Descent, Tag 03DR.
(blueprint: def-tensor-composite-cohomology-restriction).
Proof: apply the tensor-pullback object function to the given equality. Naming this
proof keeps its type stable when the construction is specialized to a unit sheaf. -/
theorem tensorCompositeCoefficient_eq {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (G : C.Modules) :
    (tensorPullback (a ≫ b)).obj G = (tensorPullback c).obj G :=
  congrArg (fun k ↦ (tensorPullback k).obj G) w

/-- The cohomology map of the adjunct of the canonical tensor-composition coefficient map.
Source: Stacks Project, Cohomology, Tags 01F8 and 01FB; Descent, Tag 03DR.
(blueprint: def-tensor-composite-cohomology-restriction).
The arrow equality transports the final coefficient object; no new adjunction is chosen. -/
def tensorCompositeCohomologyRestriction {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c)
    (G : C.Modules) (q : ℕ) :
    AddCommGrpCat.of ((RingedSpace.moduleCohomology B.toRingedSpace q).obj
      ((tensorPullback b).obj G)) ⟶
    AddCommGrpCat.of ((RingedSpace.moduleCohomology A.toRingedSpace q).obj
      ((tensorPullback c).obj G)) :=
  moduleCohomologyFMap a
    (((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _).toFun
      ((tensorSectionsComp a b).hom.app G ≫
        eqToHom (tensorCompositeCoefficient_eq a b c w G))) q

/-- The restriction is the existing canonical adjoint coefficient map on cohomology.
Source: Stacks Project, Cohomology, Tags 01F8 and 01FB; Descent, Tag 03DR.
(blueprint: def-tensor-composite-cohomology-restriction).
Proof: unfold the constructed map. The coefficient module remains arbitrary, so this
identity does not unfold a structural-unit sheaf or a concrete fibre-product scheme. -/
private theorem tensorCompositeCohomologyRestriction_eq_named {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c)
    (G : C.Modules) (q : ℕ) :
    tensorCompositeCohomologyRestriction a b c w G q =
      moduleCohomologyFMap a
        (((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _).toFun
          ((tensorSectionsComp a b).hom.app G ≫
            eqToHom (tensorCompositeCoefficient_eq a b c w G))) q := by
  rfl

/-- The canonical restriction expressed with direct transport along the arrow equality.
Source: Stacks Project, Cohomology, Tags 01F8 and 01FB; Descent, Tag 03DR.
(blueprint: def-tensor-composite-cohomology-restriction).
Proof: use the constructed restriction formula and proof irrelevance for its
coefficient-object equality, applying congruence before specializing any module. -/
theorem tensorCompositeCohomologyRestriction_eq {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c)
    (G : C.Modules) (q : ℕ) :
    tensorCompositeCohomologyRestriction a b c w G q =
      moduleCohomologyFMap a
        (((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _).toFun
          ((tensorSectionsComp a b).hom.app G ≫
            eqToHom (congrArg (fun k ↦ (tensorPullback k).obj G) w))) q := by
  exact (tensorCompositeCohomologyRestriction_eq_named a b c w G q).trans
    (congrArg (fun p : (tensorPullback (a ≫ b)).obj G = (tensorPullback c).obj G ↦
      moduleCohomologyFMap a
        (((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _).toFun
          ((tensorSectionsComp a b).hom.app G ≫ eqToHom p)) q)
      (Subsingleton.elim _ _))

attribute [irreducible] tensorCompositeCohomologyRestriction
end
end AlgebraicGeometry.Scheme.Modules
