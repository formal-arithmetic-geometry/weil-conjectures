/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.HomotopyPullbackSquareLocalization
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Localization of the canonical homotopy pullback square

Source: Stacks Project, Tags 0D5S and 0DVC.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

/-- The ordinary exchange is the mate of the canonical pullback square on homotopy
categories, expressed by its counit transpose.
Source: Stacks Project, Tag 08HY, the two descriptions of the base-change map.
(blueprint: lem-pc-homotopy-base-change-counit).

Proof: On modules, let k be the f' adjoint of the pullback square at f_*D
followed by p* of the f counit. Apply the g Hom equivalence to k: its expression
starts with the unit of the composite adjunction (g,f'), followed by the image
of the pullback square and the image of p* of the f counit. The conjugate unit
identity for the square replaces the first two factors by the unit of the
composite adjunction (f,p), followed by the right-adjoint square comparison.
Naturality of that comparison moves p* of the f counit to its left. Naturality
of the p unit then moves the f counit across that unit. The right triangle
identity for f cancels its unit followed by f_* of its counit. The remaining
map is f_* of the p unit followed by pushforwardComp(p,f), the equality transport
of the square and the inverse pushforwardComp(f',g): precisely the g adjoint
used to define moduleBaseChangeMap. Injectivity of the g Hom equivalence identifies
k with that map; transposing under f' gives the desired ordinary counit formula.
Apply this equality degreewise to complexes. The mapped composition
identifications and adjunction counits descend through the homotopy quotient;
every homotopy object is the quotient of a complex. This gives the displayed
identity. The proof uses only adjunction identities, so no cartesian, flatness,
acyclicity, or nonempty-scheme hypothesis is necessary. -/
theorem moduleHomotopyBaseChange_counit
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (D : HomotopyCategory X.Modules (.up ℤ)) :
    let af := (Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory (.up ℤ)
    let af' := (Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction f')).mapHomotopyCategory (.up ℤ)
    let b :=
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g))
        (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory
        { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
          naturality := fun _ _ a ↦
            Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h a }
        (ComplexShape.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pushforward f'))
        (ComplexShape.up ℤ)).inv
    (moduleHomotopyPullbackSquare f f' g p h).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (.up ℤ)).obj D) ≫
      ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map
        (af.counit.app D) = (af'.homEquiv _ _).symm (b.app D) := by sorry

end
end AlgebraicGeometry
