/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Geometric stalks on the small pro-etale site

The bounded site has objects in `Type (u + 1)` and morphisms in `Type u`.
Neighbourhoods and colimits are formed in the larger universe `u + 1`.
The generic stalk specializes to sets and to modules over any fixed commutative ring.

## Implementation details

For varying coefficients we use `PresheafOfModules.colimitFunctor`: its scalar action
is induced by sectionwise scalar multiplication after common refinement, rather than
regarding semilinear restriction maps as linear over a fixed section ring.

## References

* Stacks Project, Tag 0F6B and the preceding definition of pro-etale neighbourhood.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- Pointed weakly etale neighbourhoods of `y`. Objects are weakly etale `U → Y`
with a lift `Spec Ω → U` over `Y`; arrows are `Y`-morphisms preserving the lift. -/
abbrev ProEtaleGeometricNeighbourhood [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :=
  StructuredArrow (Over.mk y) (ProEt.forget Y)

/-- Forget the lift in a pointed neighbourhood, retaining its object of the pro-etale site. -/
noncomputable def proEtaleGeometricNeighbourhoodForget [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ProEtaleGeometricNeighbourhood y ⥤ Y.ProEt :=
  StructuredArrow.proj (Over.mk y) (ProEt.forget Y)

/-- The neighbourhood category is cofiltered, equivalently its opposite is filtered
(Stacks, Tag 0F6B). -/
theorem proEtaleGeometricNeighbourhood_isCofiltered [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    IsCofiltered (ProEtaleGeometricNeighbourhood y) := by
  infer_instance

attribute [instance] proEtaleGeometricNeighbourhood_isCofiltered

/-- The bounded neighbourhood category is small in the larger universe. -/
noncomputable instance proEtaleGeometricNeighbourhood_initiallySmall [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) : InitiallySmall.{u + 1} (ProEtaleGeometricNeighbourhood y) :=
  initiallySmall_of_essentiallySmall _

/-- Colimits over pointed neighbourhoods exist in categories with colimits in the larger
universe. -/
noncomputable instance proEtaleGeometricNeighbourhood_hasColimitsOfShape [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (C : Type v) [Category.{w} C]
    [HasColimitsOfSize.{u + 1, u + 1} C] :
    HasColimitsOfShape (ProEtaleGeometricNeighbourhood y)ᵒᵖ C :=
  hasColimitsOfShape_of_finallySmall _ _

/-- The diagram `D_F`: evaluate `F` on neighbourhoods and use its restriction maps. -/
noncomputable def proEtaleGeometricStalkDiagram [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {C : Type v} [Category.{w} C] (F : Sheaf (ProEt.topology Y) C) :
    (ProEtaleGeometricNeighbourhood y)ᵒᵖ ⥤ C :=
  (proEtaleGeometricNeighbourhoodForget y).op ⋙ F.obj

/-- The geometric stalk, the colimit of sections over pointed weakly etale neighbourhoods.
Take `C = Type (u + 1)` for sets, or `C = ModuleCat A` for fixed coefficients.
(Stacks, Tags 040R, 03PN, 0F6B.) -/
noncomputable def proEtaleGeometricStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {C : Type v} [Category.{w} C] [HasColimitsOfSize.{u + 1, u + 1} C]
    (F : Sheaf (ProEt.topology Y) C) : C :=
  colimit (proEtaleGeometricStalkDiagram y F)

/-- The set-valued geometric stalk in the chosen larger universe. -/
noncomputable abbrev proEtaleGeometricSetStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (Type (u + 1))) : Type (u + 1) :=
  proEtaleGeometricStalk y F

/-- The stalk with fixed commutative coefficients, using the same diagram in `A`-modules. -/
noncomputable abbrev proEtaleGeometricFixedModuleStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) : ModuleCat.{u + 1} A :=
  proEtaleGeometricStalk y F

/-- The diagram of rings underlying a commutative ring sheaf on pointed neighbourhoods. -/
noncomputable def proEtaleGeometricStalkRingDiagram [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (ProEtaleGeometricNeighbourhood y)ᵒᵖ ⥤ RingCat.{u + 1} :=
  (proEtaleGeometricNeighbourhoodForget y).op ⋙ O.obj ⋙
    forget₂ CommRingCat.{u + 1} RingCat.{u + 1}

/-- The stalk ring, with operations induced from sections at common pointed refinements.
Its underlying set is the filtered colimit of the underlying sets; forgetting commutativity
here allows use of the general `PresheafOfModules` construction. -/
noncomputable def proEtaleGeometricStalkRing [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) : RingCat.{u + 1} :=
  colimit (proEtaleGeometricStalkRingDiagram y O)

/-- The stalk of an `O`-module sheaf as a module over the stalk ring. Its action respects
the semilinear restriction maps; no single section ring is used as a fixed coefficient
ring. (Stacks, Tags 0F6B and 002F.) -/
noncomputable def proEtaleGeometricModuleStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (F : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    ModuleCat.{u + 1} (proEtaleGeometricStalkRing y O) :=
  (PresheafOfModules.colimitFunctor
    (colimit.isColimit (proEtaleGeometricStalkRingDiagram y O))).obj
      ((PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
        (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj F.val)

end AlgebraicGeometry.Scheme
