/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Wedging two exterior sheaves before quotient descent

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph,
exterior-power and tensor universal properties (blueprint: lem-sc-exterior-sheaf-wedge-map).
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Wedge the image of the first tuple with the second tuple, without choosing quotient lifts.
For each open, the concatenated wedge is alternating and multilinear separately in the two
blocks. Linearize each block through the exterior-power universal property and then through
the tensor-product universal property. These maps commute with restriction: on generating
wedges this follows from naturality of `f` and the exterior-power restrictions. First compose
with the target's sheafification unit. Extend to the sheafifications of both source factors
using local representatives; equality on overlaps follows from separatedness of the target.
The tensor sheaf universal property gives the asserted sheaf morphism. Its pure-wedge formula
follows from the defining sectionwise maps. This construction works for arbitrary `f`; it uses
neither exactness nor a rank bound. Empty blocks give multiplication by the degree-zero scalar.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph, universal properties
(blueprint: lem-sc-exterior-sheaf-wedge-map). -/
theorem exteriorSheaf_wedgeMap_exists {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s t : ℕ) (ht : t = r + s) :
    ∃ ψ : exteriorSheaf A r ⊗ exteriorSheaf B s ⟶ exteriorSheaf B t,
      ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
          exteriorSheafSection B t U
            (fun i ↦ Fin.append (fun j ↦ f.val.app (op U) (a j)) c (Fin.cast ht i)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
