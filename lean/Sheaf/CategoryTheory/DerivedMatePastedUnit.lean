/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Pasted-unit normalization for derived mates

The normalization is separate from right-derived extensionality and the particular
composition comparison. Source: Mathlib's derived adjunction factorization equations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u₁ u₂ u₃ u₄ w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v} C] [Category.{v} D] [Category.{v} C'] [Category.{v} D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [HasDerivedCategory.{w} C'] [HasDerivedCategory.{w} D']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  [HasKInjectiveResolutions C'] [HasKInjectiveResolutions D']
  (F : C ⥤ D) (K : C' ⥤ D') (G : D ⥤ D') (H : C ⥤ C')
  (P : C' ⥤ C) (Q : D' ⥤ D)
  [F.Additive] [K.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (ah : H ⊣ P) (ag : G ⊣ Q)
  (m : F ⋙ G ⟶ H ⋙ K)
  (β : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
    H.mapDerivedCategory ⋙ K.rightDerivedFunctor)
  (hβ : rightDerivedFunctorCompUnit F G ≫
      whiskerLeft DerivedCategory.Qh
        (isoWhiskerLeft F.rightDerivedFunctor
          G.rightDerivedFunctorIsoMapDerivedCategory).hom ≫
      whiskerLeft DerivedCategory.Qh β =
    whiskerRight (NatTrans.mapHomotopyCategory m (.up ℤ)) DerivedCategory.Qh ≫
      rightDerivedFunctorCompUnit H K ≫
      whiskerLeft DerivedCategory.Qh
        (isoWhiskerRight H.rightDerivedFunctorIsoMapDerivedCategory
          K.rightDerivedFunctor).hom)

include hβ in
/-- An arbitrary normalized derived square has a mate whose pasted unit is the
localized ordinary mate. This calculation does not identify that mate with a specified
right-adjoint comparison; right-derived extensionality is a separate step.

Source: Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean,
`derivedη_fac_app` and `derivedε_fac_app`; Stacks Project, Tag 079W.
(blueprint: lem-pc-derived-mate-pasted-unit).

Proof: Evaluate at an object X of the homotopy category of C'. Expand the pasted
P,F unit and the forward mate into the G-unit, Q-image of β at RP(X), and H-counit.
Use naturality of the derived G-unit to move the F-unit across it, then
naturality of β to move the right-derived P-unit across it. Apply hβ at the image of X under
P on the homotopy category. The exact identifications RG ≅ D(G) and RH ≅ D(H)
replace their units by the inverses of the localization factor isomorphisms.
Use derivedη_fac_app for G and derivedε_fac_app for H to replace the derived
unit and counit. Naturality of the localization factor isomorphisms and the
P,F,K,Q units gives the composite localized G-unit, Q-image of m at P(X), and H-counit,
followed by the pasted K,Q unit. This is precisely the ordinary forward mate
by the defining formula of mateEquiv. Associators and unitors cancel componentwise.
More explicitly, write p,f,k,q for the four right-derived units, and γH,γG
for the inverses of the exact localization factor isomorphisms. Put N = P(X)
in the homotopy category, transporting composite functors by their canonical
composition isomorphisms. Naturality of the derived G-unit at RF(p_X),
naturality of β at p_X, and naturality of that unit at f_N rewrite the left side
as ηG at Qh(F(N)), followed by RQ of D(G)(f_N), β at Qh(N),
RK(D(H)(p_X)), and RK of the derived H-counit at Qh(X).
The G-unit factorization rewrites this ηG as the localized ordinary G-unit,
then q at G(F(N)), then RQ(γG at F(N)). The hypothesis hβ replaces
γG;D(G)(f_N);β by the localized ordinary square followed by k at H(N)
and RK(γH at N). The H-counit factorization gives
D(H)(p_X);εH = γH inverse at N followed by the localized ordinary H-counit.
Thus γH cancels with its inverse. Finally naturality of k at the ordinary
H-counit and of q at the ordinary square and its K-image of that counit
puts q and RQ(k) last. What precedes them is the localized ordinary
G-unit, Q-image of m at P(X), and Q-image of K applied to the H-counit,
which is the ordinary forward mate. Restoring the composite-functor
isomorphisms gives precisely the right side.
The argument only uses naturality and the factorization equations; it works for
zero categories, zero squares, and identity adjunctions without cancellation of
noninvertible derived units. -/
theorem derivedMate_pastedUnit :
    rightDerivedFunctorCompUnit P F ≫ whiskerLeft DerivedCategory.Qh
      (mateEquiv ah.mapDerivedCategoryRightDerivedAdjunction
        ag.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ β)).natTrans =
    whiskerRight (NatTrans.mapHomotopyCategory
      (mateEquiv ah ag (TwoSquare.mk _ _ _ _ m)).natTrans (.up ℤ))
        DerivedCategory.Qh ≫ rightDerivedFunctorCompUnit K Q := by sorry

end CategoryTheory.Functor
