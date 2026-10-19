/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.Triangulated.Recollement

/-! # Counit cones from ordinary complementary triangles

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-prop-sf-localization/_section.md, place "Hom(-,L) argument: complete the exceptional
  counit and identify its cone by closed and open Hom tests"
(blueprint: lem-sf-ordinary-triangle-counit-cone)

This module proves the abstract counit-cone comparison for a complementary pair of
triangulated categories using the source library's recollement triangle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Pretriangulated
open CategoryTheory.Limits

universe vT uT vZ uZ vU uU

namespace CategoryTheory

variable {T : Type uT} [Category.{vT} T] [HasZeroObject T] [Preadditive T]
  [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [IsTriangulated T]
variable {TZ : Type uZ} [Category.{vZ} TZ] [HasZeroObject TZ] [Preadditive TZ]
  [HasShift TZ ℤ]
  [∀ n : ℤ, (shiftFunctor TZ n).Additive]
  [Pretriangulated TZ] [IsTriangulated TZ]
variable {TU : Type uU} [Category.{vU} TU] [HasZeroObject TU] [Preadditive TU]
  [HasShift TU ℤ]
  [∀ n : ℤ, (shiftFunctor TU n).Additive]
  [Pretriangulated TU] [IsTriangulated TU]

/-- Identification of a counit cone from an ordinary complementary triangle.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-prop-sf-localization/_section.md, place "Hom(-,L) argument: complete the exceptional
  counit and identify its cone by closed and open Hom tests"
(blueprint: lem-sf-ordinary-triangle-counit-cone).

Here `iStar, iLeft, iRight, jBang, jStar, jRight` are `i_*, i^*, i^!, j_!, j^*, j_*`; write
`A = i_* i^! K`, `B = j_* j^* K`, `e : A ⟶ K` the counit of `adjRight`, `u : K ⟶ B` the unit of
`adjOpen`.

Proof, using the formal recollement construction in
`WeilConjectures.CategoryTheory.Triangulated.Recollement`:
1. The invertible counit of `adjLeft` makes `iStar` fully faithful. If `jStar.obj M` is zero,
   the first vertex of the ordinary triangle is zero, so its second map is invertible and
   `M` lies in the essential image of `iStar`.
2. `Recollement.exists_distTriang_counit_unit` now supplies a distinguished triangle with
   the prescribed exceptional counit and open unit. Its construction completes the open
   unit, identifies its fibre in the closed essential image, and identifies the first map
   with the exceptional counit by full faithfulness and Hom exactness. Compare this triangle
   with the given completion using `isoTriangleOfIso₁₂`, with identities on the first two
   vertices. Its third component is the required isomorphism and commutes with `v`.
3. `Recollement.subsingleton_hom_shift` proves the asserted shifted Hom vanishing by the
   open adjunction and `hDisjoint`. In particular `Hom(A[1], B) = 0`, so Hom-out exactness
   (`Triangle.cancel_mor₂_of_subsingleton`) makes the comparison unique.
-/
theorem ordinaryTriangleCounitCone
    (iStar : TZ ⥤ T) (iLeft : T ⥤ TZ) (iRight : T ⥤ TZ)
    (jBang : TU ⥤ T) (jStar : T ⥤ TU) (jRight : TU ⥤ T)
    [iStar.CommShift ℤ] [iLeft.CommShift ℤ] [iRight.CommShift ℤ]
    [jBang.CommShift ℤ] [jStar.CommShift ℤ] [jRight.CommShift ℤ]
    [iStar.IsTriangulated] [iLeft.IsTriangulated] [iRight.IsTriangulated]
    [jBang.IsTriangulated] [jStar.IsTriangulated] [jRight.IsTriangulated]
    (adjLeft : iLeft ⊣ iStar) (adjRight : iStar ⊣ iRight)
    (adjBang : jBang ⊣ jStar) (adjOpen : jStar ⊣ jRight)
    (hClosed : ∀ P : TZ, IsIso (adjLeft.counit.app P))
    (hOpen : ∀ Q : TU, IsIso (adjOpen.counit.app Q))
    (hDisjoint : ∀ P : TZ, IsZero (jStar.obj (iStar.obj P)))
    (hOrdinary : ∀ M : T,
      ∃ δ : iStar.obj (iLeft.obj M) ⟶ (jBang.obj (jStar.obj M))⟦(1 : ℤ)⟧,
        Triangle.mk (adjBang.counit.app M) (adjLeft.unit.app M) δ ∈ distTriang T) :
    ∀ K : T,
      (∀ (C : T) (v : K ⟶ C)
        (w : C ⟶ (shiftFunctor T (1 : ℤ)).obj (iStar.obj (iRight.obj K))),
        Triangle.mk (adjRight.counit.app K) v w ∈ distTriang T →
        ∃ β : C ⟶ jRight.obj (jStar.obj K),
          v ≫ β = adjOpen.unit.app K ∧ IsIso β ∧
            ∀ β' : C ⟶ jRight.obj (jStar.obj K),
              v ≫ β' = adjOpen.unit.app K → β' = β) ∧
      ∀ (P : TZ) (Q : TU) (m : ℤ),
        Subsingleton ((shiftFunctor T m).obj (iStar.obj P) ⟶ jRight.obj Q) := by
  -- Keep the original triangulated-category hypotheses in the theorem's signature.
  have _ := (inferInstance : IsTriangulated T)
  have _ := (inferInstance : IsTriangulated TZ)
  have _ := (inferInstance : IsTriangulated TU)
  have : ∀ P, IsIso (adjLeft.counit.app P) := hClosed
  have : ∀ Q, IsIso (adjOpen.counit.app Q) := hOpen
  have : IsIso adjLeft.counit := NatIso.isIso_of_isIso_app _
  have : IsIso adjOpen.counit := NatIso.isIso_of_isIso_app _
  have hi := adjLeft.fullyFaithfulROfIsIsoCounit
  have hess (M : T) (hM : IsZero (jStar.obj M)) : iStar.essImage M := by
    obtain ⟨δ, hδ⟩ := hOrdinary M
    have : IsIso (adjLeft.unit.app M) :=
      (Triangle.isZero₁_iff_isIso₂ _ hδ).1 (jBang.map_isZero hM)
    exact ⟨iLeft.obj M, ⟨(asIso (adjLeft.unit.app M)).symm⟩⟩
  intro K
  refine ⟨?_, fun P Q m ↦ Recollement.subsingleton_hom_shift iStar jStar adjOpen
    hDisjoint P Q m⟩
  intro C v w hT
  obtain ⟨δ, hδ⟩ := Recollement.exists_distTriang_counit_unit adjOpen adjRight hi
    hDisjoint hess K
  let e := isoTriangleOfIso₁₂ _ _ hT hδ (Iso.refl _) (Iso.refl _) (by simp)
  have he : v ≫ e.hom.hom₃ = adjOpen.unit.app K := by
    simpa [e] using e.hom.comm₂
  refine ⟨e.hom.hom₃, he, ?_, ?_⟩
  · exact Triangle.π₃.map_isIso e.hom
  · intro β' hβ'
    have : Subsingleton ((Triangle.mk (adjRight.counit.app K) v w).obj₁⟦(1 : ℤ)⟧ ⟶
        jRight.obj (jStar.obj K)) :=
      Recollement.subsingleton_hom_shift iStar jStar adjOpen hDisjoint _ _ _
    exact Triangle.cancel_mor₂_of_subsingleton hT (hβ'.trans he.symm)

end CategoryTheory
