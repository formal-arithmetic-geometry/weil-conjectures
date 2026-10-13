/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Local alternating Čech cancellation

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Positive-degree signed insertion cancellation on the singleton open.
Source: Stacks Project, Tag 02FU, with the ordered convention of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-positive-contraction).

Proof: On a test open V contained in U i, for a tuple t not containing i,
insert i in its unique increasing position b. Project to that coordinate and
multiply by (-1)^b. The resulting intersection equals the old intersection
since V is contained in U i. For tuples containing i use zero. These linear maps
commute with restrictions. For a positive-degree tuple not containing i, deleting
the inserted i contributes the identity. Every other deletion in d h is paired
with insertion after deletion in h d; the two restrictions agree and their signs
are opposite. For tuples containing i, only deletion of i contributes, with
product of signs one. Sheafify these natural maps on the restricted site,
using the local sheafification identification with the restriction of the
sheafified complex; additivity preserves the equation. Transport through
extendXIso to integer degrees and put the maps equal to zero in negative degrees.
For empty test opens all modules vanish; r=0 has no i; degrees above the tuple
length have zero terms. This claim imposes no equation at degree zero.
-/
theorem alternatingCechSheaf_restrict_positive_contraction
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    ∃ h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k,
      ∀ k : ℤ, 0 < k → C.d k (k + 1) ≫ h k +
        (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
          h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by sorry

end AlgebraicGeometry
