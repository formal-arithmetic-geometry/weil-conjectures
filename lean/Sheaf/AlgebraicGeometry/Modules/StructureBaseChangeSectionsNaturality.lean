module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.Modules.PullbackSectionFactorization

/-! # Naturality on sections of the canonical structure-sheaf comparison

Source: Stacks Project, Tag 02KG, the canonical tensor comparison.
(blueprint: new-sbc-structure-base-change-sections-naturality)
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical structure-sheaf comparisons commute with a map of base-change squares.

Source: Stacks Project, Tag 02KG, canonical tensor comparison, and Tag 01CA.
(blueprint: new-sbc-structure-base-change-sections-naturality)

Proof: Unfold the constructed section transport. Substitute the defining equalities
hb and hb'. Apply the
pullback-pushforward adjunction to the proposed sheaf identity.
The adjunction units and the pullback composition comparison identify the adjoints
with the two restrictions from O_X to O_Z. Restrictions compose along w then k;
the equality wk identifies their composite with l. The equality wq identifies the
two pushforward factorizations. The canonical pushforward composition comparisons
are coherent, so the two adjoints agree. Injectivity of the adjunction homEquiv gives
the sheaf identity; evaluate it at the top open and on x. The structure-sheaf unit
on sections is w.appTop, and the pullback unit is pullbackΓ, yielding the displayed
equality after replacing b(x) by a using hx. No isomorphism or inverse is used.
In particular this identity is valid
for non-cartesian commuting squares, and for empty schemes. -/
theorem structure_baseChange_sections_naturality
    {X Y A B C D : Scheme.{u}}
    (p : X ⟶ Y) (q : A ⟶ B) (t : C ⟶ D)
    (g : B ⟶ Y) (h : D ⟶ Y) (k : A ⟶ X) (l : C ⟶ X)
    (sq : k ≫ p = q ≫ g) (sq' : l ≫ p = t ≫ h)
    (v : D ⟶ B) (w : C ⟶ A)
    (vg : v ≫ g = h) (wk : w ≫ k = l) (wq : w ≫ q = t ≫ v)
    (b : (pullback g).obj ((pushforward p).obj (unit X)) ⟶
      (pushforward q).obj (unit A))
    (b' : (pullback h).obj ((pushforward p).obj (unit X)) ⟶
      (pushforward t).obj (unit C))
    (hb : b = ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
      ((pushforward p).map (unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
        (pushforwardComp k p).hom.app (unit A) ≫
        (pushforwardCongr sq).hom.app (unit A) ≫
        (pushforwardComp q g).inv.app (unit A)))
    (hb' : b' = ((pullbackPushforwardAdjunction h).homEquiv _ _).symm
      ((pushforward p).map (unitToPushforwardObjUnit l.toRingCatSheafHom) ≫
        (pushforwardComp l p).hom.app (unit C) ≫
        (pushforwardCongr sq').hom.app (unit C) ≫
        (pushforwardComp t h).inv.app (unit C)))
    (x : Γ((pullback g).obj ((pushforward p).obj (unit X)), ⊤))
    (a : Γ(A, ⊤)) (hx : Hom.app b ⊤ x = a) :
    Hom.app b' ⊤ (pullbackSectionFactorization g h v vg ((pushforward p).obj (unit X)) x) =
      w.appTop a := by
  sorry

end AlgebraicGeometry.Scheme.Modules
