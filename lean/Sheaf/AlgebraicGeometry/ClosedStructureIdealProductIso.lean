/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # A normalized closed structure ideal-product comparison

Source: Stacks Project, Tag 01QY, affine quotient calculation.
(blueprint: lem-pc-closed-structure-ideal-product-iso)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Identify the pushforward of the extended ideal with its ambient ideal product,
including the compatibility with the inclusions into the closed structure module.
Source: Stacks Project, Tag 01QY (lemma-closed-immersion-pushforward).
(blueprint: lem-pc-closed-structure-ideal-product-iso)

Proof: On an affine open V = Spec A in X, its inverse image under the closed
immersion is Spec B, where B = A/K and the structure map pi : A -> B is surjective.
If L = I(V), the ideal of I.comap i on this inverse image is Ideal.map pi L.
Surjectivity makes pi(L) an ideal: a scalar b lifts to a in A, and b*pi(l) = pi(a*l).
Thus this extended ideal equals the B-submodule L B. The ambient product I H,
where H = i_* O_W, is the image of multiplication L tensor_A B -> B, and has
exactly the same sections L B. Both inclusions are injective: the upstairs ideal
inclusion is injective on sections, closed pushforward preserves this, and the
product inclusion is an image inclusion. On the affine basis their ranges agree.
The two subobjects of H consequently agree: a local lift through either inclusion
is unique, so the lifts agree on overlaps and glue by the sheaf axiom. The equal
subobjects give an isomorphism between their domains commuting with their monic
arrows into H. This is the displayed equation. The argument uses neither
Noetherianity nor integrality. It applies to the zero ideal, the unit ideal, and
the empty closed subscheme; all comparisons preserve the given inclusions. -/
theorem closed_structure_ideal_product_iso
    {X W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) :
    ∃ e : (pushforward i).obj (I.comap i).toModules ≅
        idealModuleProduct I.toModulesι
          ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)),
      e.hom ≫ idealModuleProductι I.toModulesι
          ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) =
        (pushforward i).map (I.comap i).toModulesι := by sorry

end AlgebraicGeometry.Scheme.Modules
