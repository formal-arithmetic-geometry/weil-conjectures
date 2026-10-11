/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Abelian.Images

/-!
# Restriction of the ideal of the complementary components

Source: Stacks Project, Varieties, Remark 33.38.9 (Tag 09NW), applied to the reduced
component cover (blueprint: lem-sc-conductor-ideal-restriction).
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The ideal of the union of the other reduced components pulls back isomorphically
onto its image on the distinguished component. The intersection of the two defining
ideals equals their product.

Source: Stacks Project, Varieties, Remark 33.38.9 (Tag 09NW)
(blueprint: lem-sc-conductor-ideal-restriction).

Here `i` lists the distinct components `Z₁, …, Z_r` (`hdistinct`), `a` labels the first
component, `j` is the immersion of the reduced union of all other components, and
`I = j.ker`. The map `φ` is adjoint to the inclusion of `I` followed
by the structure-sheaf map of `i a`; it is the induced map `i₁^* I → O_Z₁`.
Its image is `I₁`, and `Abelian.factorThruImage φ` is the natural corestriction.
The product of ideal-sheaf data is sectionwise ideal multiplication on affine opens,
hence the image of the sheaf tensor multiplication map.

Proof:
1. By lem-sc-conductor-ideal-zero-intersection, `I ∩ J₁ = 0`. Products lie in both
ideals, so `J₁ I = 0`. By lem-weil-pbc-closed-immersion-unit-quotient the pullback unit
on `I` is surjective with kernel `J₁ I`, hence an isomorphism. Naturality of the unit
identifies the pushforward of `φ` with the inclusion followed by the structure-sheaf
map, whose kernel is `I ∩ J₁ = 0` (def-sbc-closed-immersion-ideal-sheaf).
Since the component is a closed immersion, every open of the component is induced
from an open of `Y`. Thus `φ` is injective, and its corestriction to its image is an
isomorphism. The pullback and adjunction are those of def-pc-module-pullback.
2. The image of tensor multiplication (def-pur-sheaf-tensor-product) is contained in
`I ∩ J₁`, since both factors are ideals. The zero-intersection lemma therefore gives
`I ∩ J₁ = I J₁ = 0`, proving the second clause. -/
theorem conductorIdeal_restriction_isIso
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (C : ι → Scheme.{u}) (i : ∀ b : ι, C b ⟶ Y)
    [∀ b : ι, IsReduced (C b)] [∀ b : ι, IsClosedImmersion (i b)]
    (hcomponents : ∀ b : ι, Set.range (i b) ∈ irreducibleComponents Y)
    (hdistinct : Function.Injective fun b : ι => Set.range (i b))
    (hcover : (⋃ b : ι, Set.range (i b)) = Set.univ) (a : ι)
    {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hZ : Set.range j = ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i b)) :
    let I := j.ker
    let J₁ := (i a).ker
    let adj := Classical.choice (Modules.nonempty_tensorPullbackAdjunction (i a))
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit (C a).ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit (i a).toRingCatSheafHom)
    IsIso (Abelian.factorThruImage φ) ∧ I ⊓ J₁ = I * J₁ := by
  sorry

end AlgebraicGeometry.Scheme
