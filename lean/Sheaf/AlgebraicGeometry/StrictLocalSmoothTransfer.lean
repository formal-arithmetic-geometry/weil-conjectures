/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ConstructibleSheaf.Defs
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import Sheaf.Paper.StrictlyHenselianEtaleAcyclic
import Sheaf.AlgebraicGeometry.GeometricPointCohomology
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf

/-! # Strict-local smooth transfer for constant affine-line sections

Source: Stacks Project, Tags 0EYU, 03QO, 03P5 and 01EZ--01FB; blueprint
`sk-prop-a1-kummer`, Reduction to a geometric fibre
(blueprint: lem-pur-strict-local-smooth-transfer).

The auxiliary arrows below spell out the canonical constant-coefficient identifications,
the specified derived unit, pullback and constants map in the bounded below categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

namespace StrictLocalSmoothTransfer

/-- The existing constant abelian sheaf placed in degree zero in the bounded below category.
Source: Stacks Tags 03P5 and 05RU (blueprint: lem-pur-strict-local-smooth-transfer). -/
abbrev constantObject (X : Scheme.{u}) (B : AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B)

/-- Canonical constant-section identification after exact derived inverse image.
Source: Stacks Tag 03P5 (blueprint: lem-pur-strict-local-smooth-transfer). -/
def constantPullbackIso {X Y : Scheme.{u}} (h : Y ⟶ X) (B : AddCommGrpCat.{u + 1}) :
    (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj (constantObject X B) ≅
      constantObject Y B :=
  ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlusSingleFunctor 0).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} h).app B)

/-- The derived adjunction unit, with the canonical constant-coefficient identification.
Source: Stacks Tags 0EYU and 03P5 (blueprint: lem-pur-strict-local-smooth-transfer). -/
def unit {X Y : Scheme.{u}} (h : Y ⟶ X) (B : AddCommGrpCat.{u + 1}) :
    constantObject X B ⟶
      (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj (constantObject Y B) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app _ ≫
    (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.map
      (constantPullbackIso h B).hom

/-- The canonical derived pullback of sections followed by the constant-section comparison.
Source: Stacks Tags 01F9--01FB and 03P5 (blueprint: lem-pur-strict-local-smooth-transfer). -/
def pullback {X Y : Scheme.{u}} (h : Y ⟶ X) (B : AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        (constantObject X B) ⟶
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        (constantObject Y B) :=
  abelianDerivedCohomologyPullback h (constantObject X B) ≫
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      (constantPullbackIso h B).hom

/-- The constants map is the derived constant-sheaf/global-sections adjunction unit at B[0],
followed by the canonical comparison between the exact constant functor and degree zero.
Source: Stacks Tags 03P5 and 01F9 (blueprint: lem-pur-strict-local-smooth-transfer). -/
def constants (X : Scheme.{u}) (B : AddCommGrpCat.{u + 1}) :
    (DerivedCategory.Plus.singleFunctor AddCommGrpCat.{u + 1} 0).obj B ⟶
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        (constantObject X B) :=
  (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).derivedPlus.unit.app _ ≫
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).hom.app B)

end StrictLocalSmoothTransfer

/-- Strict-local smooth transfer for the actual constant-coefficient unit and sections map.
Source: Stacks Tags 0EYU, 03QO, 03P5 and 01EZ--01FB; blueprint `sk-prop-a1-kummer`,
Reduction to a geometric fibre (blueprint: lem-pur-strict-local-smooth-transfer).

Proof:
1. Put P = Spec k and S = Spec R. The affine-space square is Cartesian. Its side
   A¹_k → P is smooth (sbc-lem-affine-space-smooth), whereas S → P is affine and hence
   qcqs (lem-weil-pbc-affine-morphism-permanence). The constant sheaf pulls back to the
   same coefficient sheaf (lem-kun-pullback-constant). The fixed power of the invertible
   prime killing B verifies the torsion hypothesis of smooth base change.
2. Both spectra are nonempty and connected, so their constant-section maps are
   isomorphisms (lem-weil-pbc-constant-sheaf-sections-connected). Strictly henselian
   acyclicity gives exact sections and positive cohomology vanishing for S and P
   (lem-weil-pbc-strictly-henselian-etale-acyclic). Geometric-point cohomology identifies
   global sections on P with every geometric stalk (lem-weil-pbc-geometric-point-cohomology).
3. Apply direct image to an injective resolution of B_S. Exact global sections commute
   with cohomology (lem-weil-pbc-exact-functor-complex-cohomology), so the unit for S → P
   induces isomorphisms on global sections of every cohomology sheaf, including degree zero
   with its actual constant sections. By the stalk criterion
   (lemma-weil-pbc-geometric-stalk-conservative), it is an isomorphism in the derived category.
4. Smooth base change (sbc-thm-smooth-base-change) identifies the derived exchange of
   sbc-def-base-change-map as an isomorphism in all nonnegative degrees; in negative degrees
   both sides vanish. Compose it with the inverse image of the unit in step 3.
5. Transpose this composite under the derived inverse-image/direct-image adjunction
   (prop-weil-pbc-derived-inverse-image-adjunction). The transpose formula for exchange
   reduces it to the inverse image of the counit after the pulled-back unit for S → P.
   The triangle identity makes that the identity on B over A¹_S. This is also the transpose
   of the unit for h, so the composite equals the specified unit.
6. Apply derived sections and the Leray comparison
   (lem-weil-pbc-cohomology-pullback-derived-unit). The result is the canonical pullback
   of def-weil-pbc-cohomology-pullback, hence invertible. On nonnegative injective
   representatives choose the target comparison after inverse image of the source resolution.
   Precomposing its section map with constants sends each b to the same constant b
   (lem-weil-pbc-sets-etale-inverse-image-constant-sheaf). This gives the last equality
   already on the representing complexes, hence in the bounded below derived category.
-/
theorem strictLocalSmoothTransfer
    (k R : Type u) [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    [IsStrictlyHenselianLocalRing R]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hunit : IsUnit (ℓ : k))
    (B : AddCommGrpCat.{u + 1}) [Finite B]
    (hB : ∃ a : ℕ, ∀ b : B, ℓ ^ a • b = 0) :
    IsIso (StrictLocalSmoothTransfer.unit
      (AffineSpace.map (n := ULift.{u} (Fin 1))
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))) B) ∧
    ((Sheaf.Γ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        (StrictLocalSmoothTransfer.unit
          (AffineSpace.map (n := ULift.{u} (Fin 1))
            (Spec.map (CommRingCat.ofHom (algebraMap k R)))) B) ≫
      (etaleLerayPlus (AffineSpace.map (n := ULift.{u} (Fin 1))
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))).hom.app
          (StrictLocalSmoothTransfer.constantObject
            (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))) B) =
      StrictLocalSmoothTransfer.pullback
        (AffineSpace.map (n := ULift.{u} (Fin 1))
          (Spec.map (CommRingCat.ofHom (algebraMap k R)))) B) ∧
    IsIso (StrictLocalSmoothTransfer.pullback
      (AffineSpace.map (n := ULift.{u} (Fin 1))
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))) B) ∧
    StrictLocalSmoothTransfer.constants (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))) B ≫
      StrictLocalSmoothTransfer.pullback
        (AffineSpace.map (n := ULift.{u} (Fin 1))
          (Spec.map (CommRingCat.ofHom (algebraMap k R)))) B =
      StrictLocalSmoothTransfer.constants (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))) B := by
  sorry

end AlgebraicGeometry.Etale
