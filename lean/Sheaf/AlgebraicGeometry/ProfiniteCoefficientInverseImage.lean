/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects

/-!
# Inverse image of profinite coefficient rings

Source: Stacks Project, Tags 098T (2), 097N, 04D3 and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Naturality of the constant-section adjunct. Source: Stacks, Tags 098T (2) and 04D3
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image).
Proof: the presheaf constant-section maps commute with every ring homomorphism.
Sheafification and the inverse-image adjunction preserve this equality by naturality.
This is the finite-level naturality used in the node's final proof step. -/
theorem proEtaleConstantInverseImageMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1} B =
    proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A ≫
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a := by
  sorry

/-- The canonical comparison on constant coefficient rings, as a natural transformation.
Source: Stacks, Tags 098T (2) and 04D3
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image). -/
noncomputable def proEtaleConstantComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (ProEt.topology Y) CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
      constantSheaf (ProEt.topology X) CommRingCat.{u + 1} where
  app A := proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A
  naturality _ _ a := proEtaleConstantInverseImageMap_naturality f a

/-- The constant ring-sheaf tower; index `op n` means the paper's level `n+1`.
Source: Stacks, Tags 098T (2), 097N and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image). -/
noncomputable abbrev proEtaleCoefficientTower (X : Scheme.{u})
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :=
  Q ⋙ constantSheaf (ProEt.topology X) CommRingCat.{u + 1}

/-- The specific infinite-limit comparison, without assuming preservation of limits.
Its data is the universal limit comparison followed by the map induced by the canonical
constant comparisons. Source: Stacks, Tags 098T (2), 097N, 04D3 and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image). -/
noncomputable def proEtaleProfiniteComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (limit (proEtaleCoefficientTower Y Q)) ⟶ limit (proEtaleCoefficientTower X Q) :=
  limit.post (proEtaleCoefficientTower Y Q)
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}) ≫
    limMap (Functor.whiskerLeft Q (proEtaleConstantComparison f))

/-- The identity comparison of inverse images, obtained as the mate of base change by
an identity. Source: Stacks, Tags 098T (2) and 04D3
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image). -/
noncomputable def proEtaleRingInverseImageId (X : Scheme.{u}) :
    proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1} ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (Functor.sheafPushforwardContinuousId'
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
          (ProEt.topology X)).symm

/-- The composite comparison of inverse images is the mate of pullback pasting.
Source: Stacks, Tags 098T (2) and 04D3
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image). -/
noncomputable def proEtaleRingInverseImageComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage f CommRingCat.{u + 1} :=
  ((conjugateIsoEquiv (proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1})
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction f CommRingCat.{u + 1}))).symm
        (Functor.sheafPushforwardContinuousComp'
          (eFG := (MorphismProperty.Over.pullbackComp
            (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
          (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

/-- Compatible canonical inverse image of a countable tower of finite commutative rings.
The value universe is `u+1`, as required by sheafification on the small site; finite rings
in universe `u` are included by their canonical `ULift`. No surjectivity of transitions is
required. Source: Stacks, Tags 098T (2), 097N, 04D3 and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image).

Proof plan, following the node's eight steps:
1. Use fpqc descent of morphisms to show the small pro-etale site is subcanonical.
2. Represent the finite constant sheaf by the finite disjoint union of copies of the base,
   labelled by ring elements; clopen partitions identify this with sheafified constants.
3. The finite transition maps are affine. Form their scheme limit; over Spec B it is
   Spec of the filtered colimit of B^Q_n. This is ind-etale, hence weakly etale, and small.
4. The representing limit sheaf is the sectionwise inverse limit of the constant rings;
   all ring operations and projections are determined coordinatewise.
5. By the inverse-image adjunction and Yoneda, inverse image of a representable sheaf
   is represented by base change; the adjunct sends each map to its base change.
6. Base change preserves these representing limits and their finite labelled objects.
   Thus the specific canonical limit comparison, rather than arbitrary limits, is invertible.
7. Finite-product preservation transports the ring operations; naturality with respect
   to these operations proves the comparisons are ring isomorphisms with the stated adjunct.
8. Projections determine the limit map uniquely. Label maps give transition and tower
   naturality. Identity base change preserves labels, and iterated base change agrees with
   composite base change; projectionwise uniqueness proves the coherence at the limit.
Dependencies: fpqc-representable-descent, scheme-coproduct-family, limit-affine-transition,
ind-etale-stability, sheaf-algebraic-structures-objects, coyoneda-iso-of-natural-hom-bijection,
presheaf-pullback-sets-left-exact and sheafification-sets-exact, all as listed in the DAG. -/
theorem proEtale_profinite_coefficient_inverse_image
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕᵒᵖ),
      IsIso ((proEtaleConstantComparison f).app (Q.obj n))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsIso (proEtaleProfiniteComparison f Q)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕᵒᵖ),
      proEtaleProfiniteComparison f Q ≫ limit.π (proEtaleCoefficientTower X Q) n =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (proEtaleCoefficientTower Y Q) n) ≫
            (proEtaleConstantComparison f).app (Q.obj n)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (a : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (limit (proEtaleCoefficientTower Y Q)) ⟶ limit (proEtaleCoefficientTower X Q)),
      (∀ n : ℕᵒᵖ, a ≫ limit.π (proEtaleCoefficientTower X Q) n =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (proEtaleCoefficientTower Y Q) n) ≫
            (proEtaleConstantComparison f).app (Q.obj n)) →
      a = proEtaleProfiniteComparison f Q) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n m : ℕᵒᵖ) (a : n ⟶ m),
      (proEtaleConstantComparison f).app (Q.obj n) ≫
          (proEtaleCoefficientTower X Q).map a =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((proEtaleCoefficientTower Y Q).map a) ≫
            (proEtaleConstantComparison f).app (Q.obj m)) ∧
    (∀ (P : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (P.obj n)]
      (a : Q ⟶ P) (X Y : Scheme.{u}) (f : X ⟶ Y),
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limMap (Functor.whiskerRight a
            (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}))) ≫
          proEtaleProfiniteComparison f P =
        proEtaleProfiniteComparison f Q ≫
          limMap (Functor.whiskerRight a
            (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}))) ∧
    (∀ (P : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (P.obj n)]
      (a : Q ⟶ P) (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕᵒᵖ),
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (a.app n)) ≫
          (proEtaleConstantComparison f).app (P.obj n) =
        (proEtaleConstantComparison f).app (Q.obj n) ≫
          (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (a.app n)) ∧
    (∀ (X : Scheme.{u}) (n : ℕᵒᵖ),
      (proEtaleConstantComparison (𝟙 X)).app (Q.obj n) =
        (proEtaleRingInverseImageId X).hom.app ((proEtaleCoefficientTower X Q).obj n)) ∧
    (∀ X : Scheme.{u}, proEtaleProfiniteComparison (𝟙 X) Q =
      (proEtaleRingInverseImageId X).hom.app (limit (proEtaleCoefficientTower X Q))) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕᵒᵖ),
      (proEtaleConstantComparison (f ≫ g)).app (Q.obj n) =
        (proEtaleRingInverseImageComp f g).hom.app ((proEtaleCoefficientTower Z Q).obj n) ≫
          (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
            ((proEtaleConstantComparison g).app (Q.obj n)) ≫
          (proEtaleConstantComparison f).app (Q.obj n)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z),
      proEtaleProfiniteComparison (f ≫ g) Q =
        (proEtaleRingInverseImageComp f g).hom.app (limit (proEtaleCoefficientTower Z Q)) ≫
          (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
            (proEtaleProfiniteComparison g Q) ≫ proEtaleProfiniteComparison f Q) := by
  sorry

end AlgebraicGeometry.Scheme
