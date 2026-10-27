/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q03 and R4
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.CondensedInternalBarResolution
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.CondensedUnipotentClass
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Data.List.Induction

/-! # Canonical data for character lifts on the internal homogeneous bar

Source: blueprint, direct-image stability, paragraph (3), agent-written internal
homogeneous-bar normalization, proof steps 1--6
(blueprint: def-sfb-internal-bar-character-data).

The underlying integer-indexed complex is constructed from the recorded resolution.
Equivariance is retained on its components in the recorded internal action category.
The specifications below are not choices of data from a postponed existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar
open CategoryTheory.CondensedDerivedRestriction (Character)

namespace Profinite.CondensedAction.InternalBarCharacter

variable (A : CategoryTheory.CondensedBar.Ring.{u})
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

variable {A G}

/-- The unaugmented chain complex of underlying internal modules of the given resolution.
Source: the complex P, paragraph (3)
(blueprint: def-sfb-internal-bar-character-data). -/
def chains (D : Resolution A.toMon G) : ChainComplex (Modules A.toMon) ℕ :=
  ChainComplex.of (fun n ↦ (D.objects n).module) (fun n ↦ (D.boundary n).val)
    (fun n ↦ congrArg Subtype.val (D.boundary_boundary n))

/-- P in degrees -n, extended by zero in positive degrees; its differential at zero is zero.
Source: the complex P, paragraph (3)
(blueprint: def-sfb-internal-bar-character-data). -/
def complex (D : Resolution A.toMon G) : CochainComplex (Modules A.toMon) ℤ :=
  (chains D).extend ComplexShape.embeddingDownNat

/-- The canonical identification P^(-n) = P_n.
Source: the degree convention for P
(blueprint: def-sfb-internal-bar-character-data). -/
def termIso (D : Resolution A.toMon G) (n : ℕ) :
    (complex D).X (-(n : ℤ)) ≅ (D.objects n).module :=
  (chains D).extendXIso ComplexShape.embeddingDownNat rfl

/-- A degree-q cochain map, read as its P_(n+q) to P_n component, without a sign change.
Source: the shift and iteration convention, paragraph (3)
(blueprint: def-sfb-internal-bar-character-data). -/
def component (D : Resolution A.toMon G) {q : ℕ}
    (f : complex D ⟶ (complex D)⟦(q : ℤ)⟧) (n : ℕ) :
    (D.objects (n + q)).module ⟶ (D.objects n).module :=
  (termIso D (n + q)).inv ≫ f.f (-((n + q : ℕ) : ℤ)) ≫
    ((complex D).shiftFunctorObjXIso (q : ℤ) (-((n + q : ℕ) : ℤ))
      (-(n : ℤ)) (by omega)).hom ≫ (termIso D n).hom

/-- The character-deletion normalization, including internal equivariance in every degree.
Source: the first displayed formula of the character-lift lemma
(blueprint: def-sfb-internal-bar-character-data). -/
def IsLift (D : Resolution A.toMon G) (a : Character A G)
    (L : complex D ⟶ (complex D)⟦(1 : ℤ)⟧) : Prop :=
  (∀ n : ℕ, Equivariant (D.objects (n + 1)) (D.objects n) (component D L n)) ∧
  ∀ (n : ℕ) (S : Profinite.{u}) (x : Fin (n + 2) → C(S, G)),
    onSections A.toMon (component D L n) S
      (basis A.toMon G (n + 2) (D.objects (n + 1)) (D.freeIso (n + 1)) S x) =
        a.app S ((x 0)⁻¹ * x 1) •
          basis A.toMon G (n + 1) (D.objects n) (D.freeIso n) S (fun i ↦ x i.succ)

/-- The sole possible component of e[q] composed with F_q, transported to P_q to A.
Source: the augmented character formula, paragraph (3)
(blueprint: def-sfb-internal-bar-character-data). -/
def augmentedComponent (D : Resolution A.toMon G)
    (e : complex D ⟶ (HomologicalComplex.single (Modules A.toMon) (.up ℤ) 0).obj
      (Mod.regular A.X)) {q : ℕ} (Fq : complex D ⟶ (complex D)⟦(q : ℤ)⟧) :
    (D.objects q).module ⟶ Mod.regular A.X :=
  (termIso D q).inv ≫ (Fq ≫ e⟦(q : ℤ)⟧').f (-(q : ℤ)) ≫
    (CochainComplex.shiftFunctorObjXIso
      ((HomologicalComplex.single (Modules A.toMon) (.up ℤ) 0).obj (Mod.regular A.X))
      (q : ℤ) (-(q : ℤ)) 0 (by omega)).hom ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (Mod.regular A.X)).hom

/-- The degree-q component of an inhomogeneous cochain map A[-q] to U, in function coordinates.
Source: the internal-function cochain formula, paragraph (3)
(blueprint: def-sfb-internal-bar-character-data). -/
def cocycleComponent {H : CategoryTheory.CondensedBar.InternalFunctions A}
    (B : CategoryTheory.CondensedBar.BarDiagram (G := G) H) {q : ℕ}
    (c : (HomologicalComplex.single (Modules A.toMon) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ CategoryTheory.CondensedBar.extend
        ((CategoryTheory.CondensedBar.cochains B).obj
          ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)))) :
    Mod.regular A.X ⟶ (H.functor (CategoryTheory.CondensedBar.power G q)).obj
      (Mod.regular A.X) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (Mod.regular A.X)).inv ≫
    c.f (q : ℤ) ≫
    (((CategoryTheory.CondensedBar.cochains B).obj
      ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X))).extendXIso
        ComplexShape.embeddingUpNat rfl).hom ≫
    (B.term ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)) q).hom


/-- The ordered shifted composite, constructed by recursion from the right.
Source: character-lift calculation, step 3
(blueprint: def-sfb-internal-bar-character-data). -/
def orderedIterate (D : Resolution A.toMon G)
    (L : Character A G → (complex D ⟶ (complex D)⟦(1 : ℤ)⟧)) :
    ∀ a : List (Character A G), complex D ⟶ (complex D)⟦(a.length : ℤ)⟧ :=
  List.reverseRec
    ((shiftFunctorZero (CochainComplex (Modules A.toMon) ℤ) ℤ).inv.app (complex D))
    (fun a b F ↦ F ≫ (L b)⟦(a.length : ℤ)⟧' ≫
      (shiftFunctorAdd' (CochainComplex (Modules A.toMon) ℤ) 1 (a.length : ℤ)
        ((a ++ [b]).length : ℤ) (by simp; omega)).inv.app (complex D))

/-- The recursion starts with the zero-shift identity.
Source: character-lift calculation, step 3
(blueprint: def-sfb-internal-bar-character-data). -/
theorem orderedIterate_nil (D : Resolution A.toMon G)
    (L : Character A G → (complex D ⟶ (complex D)⟦(1 : ℤ)⟧)) :
    orderedIterate D L [] =
      (shiftFunctorZero (CochainComplex (Modules A.toMon) ℤ) ℤ).inv.app (complex D) := by
  simp [orderedIterate]

/-- Appending a character composes its shifted lift on the right, without reordering.
Source: character-lift calculation, step 3
(blueprint: def-sfb-internal-bar-character-data). -/
theorem orderedIterate_snoc (D : Resolution A.toMon G)
    (L : Character A G → (complex D ⟶ (complex D)⟦(1 : ℤ)⟧))
    (a : List (Character A G)) (b : Character A G) :
    orderedIterate D L (a ++ [b]) = orderedIterate D L a ≫
      (L b)⟦(a.length : ℤ)⟧' ≫
      (shiftFunctorAdd' (CochainComplex (Modules A.toMon) ℤ) 1 (a.length : ℤ)
        ((a ++ [b]).length : ℤ) (by simp; omega)).inv.app (complex D) := by
  simp [orderedIterate]

/-- The actual augmentation of the integer-indexed complex, obtained by extending the
augmentation of the nonnegative chain complex and identifying the resulting single object.
Source: character-lift calculation, step 4
(blueprint: def-sfb-internal-bar-character-data). -/
def barAugmentation (D : Resolution A.toMon G) : complex D ⟶
    (HomologicalComplex.single (Modules A.toMon) (.up ℤ) 0).obj (Mod.regular A.X) :=
  HomologicalComplex.extendMap
    ((ChainComplex.toSingle₀Equiv (chains D) (Mod.regular A.X)).symm
      ⟨D.augmentation.val, by
        change (D.boundary 0).val ≫ D.augmentation.val = 0
        exact congrArg Subtype.val D.boundary_augmentation⟩)
    ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (Mod.regular A.X) 0 0 rfl).hom

/-- The constructed augmentation is normalized by the given resolution augmentation.
Source: character-lift calculation, step 4
(blueprint: def-sfb-internal-bar-character-data). -/
theorem barAugmentation_zero (D : Resolution A.toMon G) :
    (termIso D 0).inv ≫ (barAugmentation D).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (Mod.regular A.X)).hom =
        D.augmentation.val := by
  simp [barAugmentation, HomologicalComplex.extendMap_f _ _ (show
    ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl),
    HomologicalComplex.extendSingleIso_hom_f, termIso, Category.assoc]

/-- A degree-one map has zero component in degree zero because P^1 is zero.
Source: the unaugmented endpoint convention, character-lift calculation, step 2
(blueprint: def-sfb-internal-bar-character-data). -/
theorem degreeOne_zero (D : Resolution A.toMon G)
    (L : complex D ⟶ (complex D)⟦(1 : ℤ)⟧) : L.f 0 = 0 := by
  have h : IsZero ((complex D).X (1 : ℤ)) :=
    (chains D).isZero_extend_X ComplexShape.embeddingDownNat 1 (by
      intro n
      change -(n : ℤ) ≠ 1
      omega)
  exact (h.of_iso ((complex D).shiftFunctorObjXIso 1 0 1 (by omega))).eq_of_tgt _ _

/-- Composing with the shifted augmentation leaves only its single possible degree.
Source: character-lift calculation, step 4
(blueprint: def-sfb-internal-bar-character-data). -/
theorem augmented_sole (D : Resolution A.toMon G) (q : ℕ)
    (F : complex D ⟶ (complex D)⟦(q : ℤ)⟧) (i : ℤ) (hi : i ≠ -(q : ℤ)) :
    (F ≫ (barAugmentation D)⟦(q : ℤ)⟧').f i = 0 := by
  have h := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (Mod.regular A.X)
    (i + (q : ℤ)) (by omega)
  exact (h.of_iso (CochainComplex.shiftFunctorObjXIso
    ((HomologicalComplex.single (Modules A.toMon) (.up ℤ) 0).obj (Mod.regular A.X))
      (q : ℤ) i (i + (q : ℤ)) rfl)).eq_of_tgt _ _

end Profinite.CondensedAction.InternalBarCharacter
