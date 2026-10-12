/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic

/-! # Hom identifications for the open-cover triangle

Source: Stacks Project, Tags 08BU, 08BT and 08BW.
(blueprint: lem-sc-open-hom-triangle-realization).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

noncomputable section

namespace SheafOfModules

/-- Restrict derived Hom along an inclusion of opens, using the composition and
localization comparison isomorphisms.
Source: Stacks Project, Tag 08BW (blueprint: lem-sc-open-hom-triangle-realization). -/
def openHomRestriction {S : Type u} [TopologicalSpace S]
    (R : Sheaf (Opens.grothendieckTopology S) RingCat.{u})
    {W U : Opens S} (i : W ⟶ U)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R W).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R W)]
    [PreservesFiniteColimits (overFunctor.{u} R W)]
    [(overMap.{u} R i).Additive]
    [PreservesFiniteLimits (overMap.{u} R i)]
    [PreservesFiniteColimits (overMap.{u} R i)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over W))]
    {E F : DerivedCategory (SheafOfModules.{u} R)}
    (f : (overFunctor.{u} R U).mapDerivedCategory.obj E ⟶
      (overFunctor.{u} R U).mapDerivedCategory.obj F) :
    (overFunctor.{u} R W).mapDerivedCategory.obj E ⟶
      (overFunctor.{u} R W).mapDerivedCategory.obj F :=
  let A := overFunctor.{u} R U
  let B := overMap.{u} R i
  letI : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  letI : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  let e := (Functor.mapDerivedCategoryCompIso A B).symm ≪≫
    Functor.mapDerivedCategoryNatIso (overFunctorMap.{u} R i)
  e.inv.app E ≫ (overMap.{u} R i).mapDerivedCategory.map f ≫ e.hom.app F

/-- The open-cover triangle, together with its additive Hom identifications.
The equality hR records that R is exactly the underlying ring sheaf of X; keeping R
as an explicit parameter avoids repeatedly unfolding that large expression.
This statement supplies the geometric triangle and the map identifications, not exactness
of Hom. The latter follows separately from the pretriangulated-category axioms.

Source: Stacks Project, Tags 08BU (triangle), 08BT (adjunction), and 08BW (identifications).
(blueprint: lem-sc-open-hom-triangle-realization).

Proof: Represent E by a complex K. In each degree use the short exact sequence
0 → j_{U∩V,!} K|_{U∩V} → j_{U,!} K|_U ⊕ j_{V,!} K|_V → K → 0,
where the first map has components the canonical extension maps and minus the
canonical extension map, and the second is the pair of counits. Exactness follows
on stalks: on the intersection the sequence is M → M ⊕ M → M with maps
m ↦ (m,-m) and (m,n) ↦ m+n; on just one open it is 0 → M → M;
outside both opens there is nothing since U ∪ V is the whole space. Apply the
short-exact-complex triangle construction and transport along Q K ≅ E. Take A
to be derived extension by zero from the overlap, B the biproduct of the two
extensions, and b the pair of derived counits. The additive adjunction bijections
and the biproduct Hom bijection give eB and eA. For eN first use the shift
bijection Hom(A[1],F) ≃ Hom(A,F[-1]), then the overlap adjunction and restriction's
shift comparison. The adjunction triangle identity gives eB(b ≫ f) equal to the
pair of restrictions of f. Naturality of the adjunction for nested opens identifies
precomposition with each component of a with openHomRestriction: write η_W for the
unit and κ for the canonical extension map from W to U. The transpose of κ ≫ g_U
is η_W ≫ R_W(κ) ≫ R_W(g_U). The sectionwise extension-by-zero construction gives
η_W ≫ R_W(κ) = c_E.inv ≫ R_{W,U}(η_U) ≫ c_{L_U E_U}.hom,
where c is the nested restriction comparison. Naturality of c moves R_W(g_U)
past its last factor, leaving c_E.inv ≫ R_{W,U}(η_U ≫ R_U(g_U)) ≫ c_F.hom.
This is exactly restriction of the U transpose. The identity holds termwise on
complexes and passes through localization using the derived comparison isos.
Apply it on both opens, then use additivity and
the minus sign in the V component to obtain the asserted difference identity. For U or V
empty the extension term vanishes, and for U = V = top the stalk
sequence is the same split sequence, so both degenerate cases remain valid. -/
theorem open_hom_triangle_realization (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R V).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R V)]
    [PreservesFiniteColimits (overFunctor.{u} R V)]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R (U ⊓ V))]
    [PreservesFiniteColimits (overFunctor.{u} R (U ⊓ V))]
    [(overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [(overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over (U ⊓ V)))]
    (E F : DerivedCategory (SheafOfModules.{u} R)) :
    let RU := (overFunctor.{u} R U).mapDerivedCategory
    let RV := (overFunctor.{u} R V).mapDerivedCategory
    let RW := (overFunctor.{u} R (U ⊓ V)).mapDerivedCategory
    ∃ (A B : DerivedCategory (SheafOfModules.{u} R))
      (a : A ⟶ B) (b : B ⟶ E) (δ : E ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk a b δ ∈ distTriang _ ∧
      ∃ (eB : (B ⟶ F) ≃+ ((RU.obj E ⟶ RU.obj F) × (RV.obj E ⟶ RV.obj F)))
        (eA : (A ⟶ F) ≃+ (RW.obj E ⟶ RW.obj F))
        (eN : (A⟦(1 : ℤ)⟧ ⟶ F) ≃+ (RW.obj E ⟶ (RW.obj F)⟦(-1 : ℤ)⟧)),
        (∀ f : E ⟶ F, eB (b ≫ f) = (RU.map f, RV.map f)) ∧
        (∀ g : B ⟶ F, eA (a ≫ g) =
          openHomRestriction R (homOfLE inf_le_left) (eB g).1 -
            openHomRestriction R (homOfLE inf_le_right) (eB g).2) := by
  sorry

end SheafOfModules
