/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # The fppf sheaf of isomorphism classes

Source: Stacks Project, Tag 06QD (blueprint: def-sfb-moduli-isomorphism-class-sheaf).

The presheaf is identified with the actual isomorphism classes in every fibre.
Sheafification is specified by its universal property, which determines the sheaf
and its unit uniquely up to unique isomorphism, without a universe-restricting choice.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace CategoryTheory

/-- A presentation of the presheaf of fibrewise isomorphism classes.
The functor over the base supplies restriction compatibility; bijectivity on skeletons
says exactly that its fibres are the quotient by isomorphism, retaining all test schemes.
Source: Stacks Project, Tag 06QD (blueprint: def-sfb-moduli-isomorphism-class-sheaf). -/
structure ModuliIsoClassPresheaf {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) where
  /-- The presheaf of sets of classes. -/
  presheaf : (Over S)ᵒᵖ ⥤ Type u
  /-- The quotient functor, compatible with all arrows over the base. -/
  classMap : BasedFunctor F (discreteModuli presheaf)
  /-- Precisely the isomorphism classes, in every fibre. -/
  class_bijective : ∀ T : Over S,
    Function.Bijective ((moduliFiberMap classMap T).mapSkeleton.obj)

/-- The fppf sheafification of the presheaf of isomorphism classes, including its unit.
The last field is the full sheafification universal property. It determines the unit,
not merely the existence of an unrelated map to a sheaf.
Source: Stacks Project, Tag 06QD; Sites, sheafification adjunction
(blueprint: def-sfb-moduli-isomorphism-class-sheaf). -/
structure ModuliIsoClassSheaf {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) extends ModuliIsoClassPresheaf F where
  /-- The sheafification on the big fppf site. -/
  sheaf : Sheaf (AlgebraicGeometry.Scheme.fppfTopology.over S) (Type u)
  /-- The unit on the prescribed isomorphism-class presheaf. -/
  unit : presheaf ⟶ sheaf.obj
  /-- Universal factorization through the unit into every fppf sheaf. -/
  universal : ∀ Z : Sheaf (AlgebraicGeometry.Scheme.fppfTopology.over S) (Type u),
    Function.Bijective (fun f : sheaf ⟶ Z ↦ unit ≫ f.hom)

/-- The natural map to the fppf sheaf of isomorphism classes: quotient, then unit.
Source: Stacks Project, Tag 06QD (blueprint: def-sfb-moduli-isomorphism-class-sheaf). -/
def ModuliIsoClassSheaf.projection {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Q : ModuliIsoClassSheaf F) :
    BasedFunctor F (discreteModuli Q.sheaf.obj) :=
  Q.classMap.comp (discreteModuliMap Q.unit)

end CategoryTheory

namespace CategoryTheory

/-- Mathlib's sheafification and its canonical adjunction unit give this presentation.
Source: Stacks Project, Tag 06QD; the sheafification-inclusion adjunction
(blueprint: def-sfb-moduli-isomorphism-class-sheaf). -/
noncomputable def ModuliIsoClassPresheaf.sheafification
    {S : AlgebraicGeometry.Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (P : ModuliIsoClassPresheaf F)
    [HasWeakSheafify (AlgebraicGeometry.Scheme.fppfTopology.over S) (Type u)] :
    ModuliIsoClassSheaf F where
  toModuliIsoClassPresheaf := P
  sheaf := (presheafToSheaf (AlgebraicGeometry.Scheme.fppfTopology.over S) (Type u)).obj
    P.presheaf
  unit := toSheafify (AlgebraicGeometry.Scheme.fppfTopology.over S) P.presheaf
  universal Z :=
    (sheafificationAdjunction (AlgebraicGeometry.Scheme.fppfTopology.over S) (Type u)).homEquiv
      P.presheaf Z |>.bijective

end CategoryTheory
