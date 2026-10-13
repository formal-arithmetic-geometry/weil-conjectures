/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Normalization of the derived representable comparison on cocycles -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A represented additive functor has an Ext comparison normalized on every resolution.

Source: Stacks Project, Derived Categories, Tag 06XR, Lemma 13.27.2;
Tag 013P, comparison maps between injective resolutions.
(blueprint: lem-sc-ext-right-derived-cocycle-comparison)

Proof: For the chosen injective resolution of Y, identify Ext from A with cohomology
classes of Hom(single(A,0),I) using extAddEquivCohomologyClass. The from-single
additive equivalence identifies that Hom complex with Hom(A,I) degreewise, commuting
with differentials. Apply the given natural isomorphism e degreewise and take homology;
compose with the inverse of isoRightDerivedObj. This defines the inverse component
of x. For a coefficient map, lift it between injective resolutions. Postcomposition
commutes with the from-single equivalence and e; extMk_comp_mk₀ identifies the map
on Ext classes, and isoRightDerivedObj_naturality identifies the derived map.
Thus these components assemble into a natural isomorphism. For another resolution,
use a comparison lifting the identity: the same naturality calculation, together
with homotopy independence, identifies its computation with the chosen one.
The identity extEquivCohomologyClass_extMk says that the class of s is the class of
its from-single cocycle. Its image under the complex isomorphism has underlying
cycle e(s). Since iCycles is monic, it is precisely c when hc holds, and the homology
class is homologyπ(c). This proves the displayed normalization for every I.
The argument includes degree zero, the zero object, and arbitrary zero cocycles;
no projectivity of A or exactness of H is used. -/
theorem exists_ext_rightDerived_cocycle_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    [HasInjectiveResolutions C] (A : C) (H : C ⥤ AddCommGrpCat.{v}) [H.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ H) :
    ∃ x : ∀ n : ℕ, H.rightDerived n ≅ (Abelian.extFunctor n).obj (op A),
      ∀ (Y : C) (I : InjectiveResolution Y) (p : ℕ)
        (s : A ⟶ I.cocomplex.X p) (hs : s ≫ I.cocomplex.d p (p + 1) = 0)
        (c : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles p)
        (hc : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles p c =
          e.hom.app (I.cocomplex.X p) s),
        (I.isoRightDerivedObj H p).hom ((x p).inv.app Y (I.extMk s (p + 1) rfl hs)) =
          ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ p c := by sorry

end CategoryTheory
