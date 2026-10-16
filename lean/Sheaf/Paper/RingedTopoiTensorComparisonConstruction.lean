/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses

/-! # Existence of the normalized ringed-topos tensor comparison -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))


open scoped ChangeOfRings

/-- The normalized ordinary tensor comparison exists.
Source: Stacks Project, Modules on Sites, Tag 03EL, together with the inverse-image
adjunction for a morphism of topoi and extension of scalars
(blueprint: lem-weil-pbc-canonical-ringed-tensor-comparison-construction).

Proof: First apply the inverse-image adjunction to the universal property of module
bilinear maps. Finite-product preservation transports addition and scalar multiplication;
the compatibility axioms of I identify these transported operations with those on
I.modules. Thus inverse image takes the universal R-balanced pairing to the universal
RI-balanced pairing. Its representing isomorphism sends the inverse image of m tensor n
to the tensor of the inverse images of m and n, naturally in both modules.
Next extend scalars. The balanced maps
s tensor (m tensor n) mapped to (s tensor m) tensor (1 tensor n), and
(s tensor m) tensor (t tensor n) mapped to st tensor (m tensor n), are inverse.
They commute with restrictions and so descend through module sheafification; checking
on pure tensors proves inverse identities and naturality. Compose these two comparisons
and transport along hobj. The map q is the sheafification insertion m mapped to 1 tensor m,
followed by eqToHom (hobj M).symm. The displayed scalar-extension formulas give q_one.
The same formulas, applied to a generalized pair of sections over any sheaf Z, give pure.
Naturality of both representing isomorphisms and hmap gives naturality. This supplies
all five fields of CanonicalRingedTensorComparison. -/
theorem canonicalRingedTensorComparison_nonempty
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := by sorry

end SheafOfModules
