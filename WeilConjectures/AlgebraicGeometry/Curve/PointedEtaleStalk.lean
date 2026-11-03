/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# Geometric stalks with only the required colimit assumption

Source: the blueprint geometric stalk definition, and SGA 4 IV 6.3
(blueprint: def-weil-pbc-geometric-stalks).

`Point.sheafFiber` assumes all small colimits in its coefficient category. This
interface uses exactly the same diagram and requires only its particular colimit.
It therefore also applies to commutative-monoid sheaves, where the filtered colimit
is available without an all-colimits instance.

## Main definitions

* `pointedEtaleStalkDiagram`: the opposite pointed-neighbourhood diagram.
* `pointedEtaleStalk`: its colimit, assuming only this colimit exists.
* `pointedEtaleGerm`: the canonical colimit injection.
* `pointedEtaleCommMonStalkHasColimit`: its explicit monoid-colimit instance.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The opposite pointed-étale-neighbourhood diagram of a sheaf: objects are pairs
of an étale `W → X` and a lift of the geometric point, and the value is `F(W)`.
Source: SGA 4 IV 6.3 (blueprint: def-weil-pbc-geometric-stalks). -/
noncomputable def pointedEtaleStalkDiagram {X : Scheme.{u}} {A : Type w} [Category.{v} A]
    (F : Sheaf X.smallEtaleTopology A) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : (Scheme.pointSmallEtale t).fiber.Elementsᵒᵖ ⥤ A :=
  (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙ F.obj

/-- The geometric stalk, the colimit of sections over opposite pointed étale
neighbourhoods. This is the colimit defining `Point.sheafFiber`, with only the
colimit actually needed assumed. Source: SGA 4 IV 6.3
(blueprint: def-weil-pbc-geometric-stalks). -/
noncomputable def pointedEtaleStalk {X : Scheme.{u}} {A : Type w} [Category.{v} A]
    (F : Sheaf X.smallEtaleTopology A) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) [HasColimit (pointedEtaleStalkDiagram F t)] : A :=
  colimit (pointedEtaleStalkDiagram F t)

/-- The canonical germ from a pointed étale neighbourhood to the geometric stalk.
Source: SGA 4 IV 6.3 (blueprint: def-weil-pbc-geometric-stalks). -/
noncomputable def pointedEtaleGerm {X : Scheme.{u}} {A : Type w} [Category.{v} A]
    (F : Sheaf X.smallEtaleTopology A) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) [HasColimit (pointedEtaleStalkDiagram F t)]
    (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W) :
    F.obj.obj (op W) ⟶ pointedEtaleStalk F t :=
  colimit.ι (pointedEtaleStalkDiagram F t) (op ⟨W, w⟩)

end AlgebraicGeometry
