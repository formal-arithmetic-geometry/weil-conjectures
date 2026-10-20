/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import Sheaf.AlgebraicGeometry.DerivedHomologySectionsComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Local descent of raw relative derived classes
Source: Stacks Project, Tag 0EYM, second proof, left vertical map. -/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AbelianComparison.freeSheaf

attribute [local irreducible] upperStar rightDerivedLowerStarPlus
  relativeHigherDirectImageDerivedMap


/-- Raw derived sections locally factor through a stage derived image.
Source: Stacks Project, Tag 0EYM, second proof, left vertical map; Tags 0EYL and 09YQ.
(blueprint: lem-kun-relative-higher-image-raw-local-descent).

Proof: Choose an affine open at a stage whose inverse image contains the marked
point, and restrict both inverse systems to this open and its inverse images.
Pass to the cofinal tail. Affine permanence gives affine transition maps and
limit projections; quasi-compactness and quasi-separatedness of the vertical
maps make the restricted source schemes qcqs. Restrict the coefficient system
using inverse-image composition and preservation of colimits. Restrict the test
object to this open, then choose an affine etale neighbourhood of its marked
point. Descend this finitely presented neighbourhood to a later stage by 0EYL.
Its fibre products with the restricted source system form a qcqs inverse system
with affine transitions and the expected limit. Derived adjunction identifies
the restricted raw morphism with degree-q cohomology on this limit, with
coefficients the colimit of the restricted F_i. By 09YQ this class comes from a
finite stage. Apply derived adjunction back at that stage, pull the resulting
morphism to the limit base, and use the free-sheaf pullback and shift comparisons
to obtain t. The commutative exchange chart formula (and its coefficient
naturality) identifies its composite with the stated derived mate and the
restriction of z. Open-restriction exchange and cube pasting identify this with
the original systems' mate. The chosen neighbourhood supplies W, a, w, and the
point identity. This only claims factorization after shrinking at the point;
it assumes neither a globally qcqs base nor descent of an arbitrary test object.
Empty test objects have no marked point; q=0 and zero coefficients are included. -/
theorem relativeHigherDirectImage_raw_local_factorization
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DV.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DB.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)]
    [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cV : Cone DV) (hcV : IsLimit cV) (cB : Cone DB) (hcB : IsLimit cB)
    (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i : Iᵒᵖ, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DV.map a.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DV.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (DV.obj (op i))).hom.app (F i))
    (hφcomp : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) =
        (upperStarComp AddCommGrpCat.{u + 1} (DV.map b.op) (DV.map a.op)
          (DV.map (a ≫ b).op) (DV.map_comp b.op a.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (DV.map b.op)).map (φ a) ≫ φ b)
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i : I, A.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj (F i))
    (hA : ∀ (i j : I) (a : i ⟶ j), A.map a =
      (eA i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).map (φ a) ≫ (eA j).inv)
    (cA : Cocone A) (hcA : IsColimit cA) (q : ℕ)
    (s : cB.pt) (U : cB.pt.Etale)
    (u₀ : (cB.pt.uliftPointSmallEtale s).fiber.obj U)
    (z : ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj cA.pt))).obj (op U)) :
    ∃ (W : cB.pt.Etale) (a : W ⟶ U)
      (w : (cB.pt.uliftPointSmallEtale s).fiber.obj W),
      (cB.pt.uliftPointSmallEtale s).fiber.map a w = u₀ ∧
      ∃ (i : I)
        (t : ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).obj
          ((upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).mapDerivedCategoryPlus.obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i))))).obj (op W)),
        ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).map
          (relativeHigherDirectImageDerivedMap ⟨hu (op i)⟩ (F i) cA.pt
            ((eA i).inv ≫ cA.ι.app i))).app (op W) t =
          ((derivedHomologySectionsFunctor cB.pt (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj cA.pt))).map a.op z := by
  sorry

end AlgebraicGeometry.Etale
