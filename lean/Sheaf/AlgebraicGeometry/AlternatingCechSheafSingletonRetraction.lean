/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Singleton projection retracts the local alternating augmentation

Source: Stacks Project, Tag 02FU, the degree-zero insertion operator.
(blueprint: lem-pc-s3-alternating-cech-sheaf-singleton-retraction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The local augmentation has a left inverse in degree zero.
Source: Stacks Project, Tag 02FU, degree-zero insertion; Tag 01FM for increasing tuples.
(blueprint: lem-pc-s3-alternating-cech-sheaf-singleton-retraction).

Proof: Project the degree-zero product of intersection presheaves to the singleton
whose unique index is i. On a test open V contained in U i, its intersection with
U i is V, so the singleton restriction is identified with the identity of G(V).
These identifications are linear and natural under restrictions. Sheafify the
projection and restrict it to U i. Sheafification of G.val is identified with G
by the sheafification counit, inverse to its unit on sheaves. Thus projection
following augmentation is the identity. Extend to integer degrees: degree zero
is unchanged, up to the canonical extendXIso and its functorial image. Transport
the preceding retraction across these isomorphisms. For r=0 there is no i; for an
empty U i all the modules in question are zero and the assertion still holds. -/
theorem alternatingCechSheafAugmentation_restrict_degreeZero_retraction
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := ((CochainComplex.single₀ X.Modules).obj G).extend
      ComplexShape.embeddingUpNat
    let C := (alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat
    let a := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∃ π : F.obj (C.X 0) ⟶ F.obj (A.X 0), a.f 0 ≫ π = 𝟙 _ := by sorry

end AlgebraicGeometry
