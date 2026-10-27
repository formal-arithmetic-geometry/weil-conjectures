/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal

/-! # Separated representable maps of fibred groupoids

Source: Stacks Project, Morphisms of Stacks, Tag 0CL0(1), and Morphisms of Spaces,
Tag 03HL (blueprint: def-sfb-separated-representable-moduli-map).

Every scheme base change retains its actual algebraic-space projection. Separatedness
of that projection uses the existing closed-immersion test on its presheaf diagonal.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

namespace CategoryTheory

/-- A representable morphism is separated when every scheme base change has separated
algebraic-space projection. The comparison is over the test scheme, and separatedness
uses all scheme tests of the actual presheaf diagonal, including nonreduced tests.
Source: Stacks Project, Morphisms of Stacks, Tag 0CL0(1), and Morphisms of Spaces,
Tag 03HL (blueprint: def-sfb-separated-representable-moduli-map). -/
def IsSeparatedRepresentableModuliMap {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (Z : AlgebraicGeometry.AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t Z p ∧ AlgebraicGeometry.AlgebraicSpace.IsSeparatedPresheafMap p

end CategoryTheory
