/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q104, V4
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData

/-! # Normalized homogeneous Hom coordinates for the condensed bar

Source: direct-image stability, paragraph (3), internal bar expansion, steps 2–5 and 7
(blueprint: lem-sfb-condensed-bar-hom-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar

namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The coordinate comparison alone, for arbitrary coefficients. No injectivity or
exactness is asserted here. The augmented comparison uses the free invariants adjunction.
Source: internal bar expansion, steps 2–5 and 7
(blueprint: lem-sfb-condensed-bar-hom-coordinates). -/
structure HomCoordinates (F : InternalFunctions A) (B : BarDiagram (G := G) F)
    (V : Invariants A G) (a : Augmentation V B) (E : Resolution A.toMon G) where
  /-- These sheaf sections are exactly the parametrized equivariant Hom groups. -/
  homEquiv : ∀ (I : Equivariant A G) (n : ℕ) (S : Profinite.{u}),
    sections A ((cochains B).obj I |>.X n) S ≃+
      (E.tensorObjects (freeParameter A S) n ⟶ I)
  /-- The displayed homogeneous-to-inhomogeneous formula, at every generalized point. -/
  coordinates : ∀ (I : Equivariant A G) (n : ℕ) (S T : Profinite.{u})
      (x : sections A (((cochains B).obj I).X n) S) (s : T ⟶ S)
      (g : Fin (n + 1) → C(T, G)),
    onSections A.toMon ((homEquiv I n S x).val) T
      (onSections A.toMon (E.tensorIso (freeParameter A S) n).inv T
        (pureTensor A.toMon _ _ T
          (basis A.toMon G (n + 1) (E.objects n) (E.freeIso n) T g)
          (((freeAdjunction A.toMon).unit.app
            (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj S)).hom.app
              (op T) (ULift.up s)))) =
      I.act T (g 0)
        ((F.evaluate (power G n) S I.module
          (onSections A.toMon (B.term I n).hom S x)).val T s
            (tupleMap (fun j ↦ (g j.castSucc)⁻¹ * g j.succ)))
  /-- Every profinite base change commutes with the Hom identification. -/
  restriction : ∀ (I : Equivariant A G) (n : ℕ)
      (S T : Profinite.{u}) (k : T ⟶ S)
      (x : sections A (((cochains B).obj I).X n) S),
    (homEquiv I n T ((((cochains B).obj I).X n).X.obj.map k.op x)).val =
      (E.tensorIso (freeParameter A T) n).hom ≫
        (E.objects n).module ◁ (free A.toMon).map
          (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).map k) ≫
        (E.tensorIso (freeParameter A S) n).inv ≫ (homEquiv I n S x).val
  /-- Every equivariant coefficient map commutes with the Hom identification. -/
  naturality : ∀ (I J : Equivariant A G)
      (h : I ⟶ J) (n : ℕ) (S : Profinite.{u})
      (x : sections A (((cochains B).obj I).X n) S),
    homEquiv J n S (onSections A.toMon (((cochains B).map h).f n) S x) =
      homEquiv I n S x ≫ h
  /-- The cochain differential is precisely precomposition by the homogeneous boundary. -/
  differential : ∀ (I : Equivariant A G) (n : ℕ) (S : Profinite.{u})
      (x : sections A (((cochains B).obj I).X n) S),
    homEquiv I (n + 1) S
      (onSections A.toMon (((cochains B).obj I).d n (n + 1)) S x) =
        E.tensorBoundary (freeParameter A S) n ≫ homEquiv I n S x
  /-- The augmentation is the invariant inclusion, constant on homogeneous generators. -/
  augmentation : ∀ (I : Equivariant A G) (S T : Profinite.{u})
      (x : sections A (V.functor.obj I) S) (s : T ⟶ S) (g : Fin 1 → C(T, G)),
    onSections A.toMon
      (homEquiv I 0 S (onSections A.toMon ((a.map.app I).f 0) S x)).val T
      (onSections A.toMon (E.tensorIso (freeParameter A S) 0).inv T
        (pureTensor A.toMon _ _ T
          (basis A.toMon G 1 (E.objects 0) (E.freeIso 0) T g)
          (((freeAdjunction A.toMon).unit.app
            (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj S)).hom.app
              (op T) (ULift.up s)))) =
      I.module.X.obj.map s.op (onSections A.toMon (V.inclusion.app I) S x)
  /-- Free invariant sections represent maps from the trivially acted-on parameter. -/
  invariantsEquiv : ∀ (I : Equivariant A G) (S : Profinite.{u}),
    sections A (V.functor.obj I) S ≃+
      ((trivial (R := A.toMon) (P := G)).obj (freeParameter A S) ⟶ I)
  /-- The augmented coordinate square is precomposition by the tensored augmentation. -/
  augmentation_hom : ∀ (I : Equivariant A G) (S : Profinite.{u})
      (x : sections A (V.functor.obj I) S),
    homEquiv I 0 S (onSections A.toMon ((a.map.app I).f 0) S x) =
      E.tensorAugmentation (freeParameter A S) ≫ invariantsEquiv I S x

/-- Homogeneous equivariant Hom and the specified inhomogeneous cochains have the
normalized additive coordinate comparison, independently of injectivity.

Source: direct-image stability, paragraph (3), internal bar expansion, steps 2–5 and 7
(blueprint: lem-sfb-condensed-bar-hom-coordinates).

Proof:
1. Apply the free linearization and tensor universal properties to describe maps out
of P_n tensor A[S] by natural values on pairs of generalized generators.
2. Given an inhomogeneous family c, assign to (s;g_0,...,g_n) the value
 g_0 c(s;g_0^(-1)g_1,...,g_(n-1)^(-1)g_n). The assignment is natural and linear
and is equivariant because simultaneous left multiplication fixes all the ratios.
The inverse evaluates f on (s;1,b_1,b_1 b_2,...,b_1 ... b_n). Cumulative products
of adjacent ratios telescope, and equivariance cancels g_0, proving both inverses.
The InternalFunctions evaluation identifies exactly these natural families.
3. The same formulas commute with profinite restriction and equivariant
postcomposition. Deleting the first homogeneous vertex yields the action face;
deleting an interior vertex multiplies adjacent ratios; deleting the last drops the
last ratio. Summing with the deletion signs proves the differential identity.
4. The free adjunction followed by the invariants adjunction identifies invariant
sections with equivariant maps from the trivially acted-on A[S]. A map sends [s]
to s* x. The tensored augmentation sends every homogeneous generator paired with [s]
to [s], so precomposition gives the displayed augmentation square. The normalization
of a gives the same constant family, proving also its generator formula.
These arguments include degree zero and the empty profinite parameter: all formulas
are natural generalized-section formulas, with no basis claim about global sections.
-/
theorem nonempty_homCoordinates (F : InternalFunctions A) (B : BarDiagram (G := G) F)
    (V : Invariants A G) (a : Augmentation V B) (E : Resolution A.toMon G) :
    Nonempty (HomCoordinates F B V a E) := by
  sorry

end CategoryTheory.CondensedBar
