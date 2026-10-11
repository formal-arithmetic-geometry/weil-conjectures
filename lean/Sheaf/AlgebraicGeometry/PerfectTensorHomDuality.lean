/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Tensor-Hom duality for perfect complexes

Source: Stacks Project, duality.tex, Tag 0A9T; cohomology.tex, Tags 08DQ,
0FPC and 0GM7 (blueprint: lem-pc-perfect-tensor-hom-duality).
-/

universe u₁ w₁

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Perfect complexes have a dual, evaluation and coevaluation satisfying the two
triangle identities, and the resulting tensor adjunctions. The full subcategory
D_QCoh has exactly the ambient Hom sets. Both left tensor adjunctions express the
specified Hom equivalences, naturally in both arguments. Their canonical forms are
Mathlib's `tensorLeftHomEquiv` for the respective exact pairings. The monoidal structure
on `schemeDerivedCategory X`, and on that of every `T`, is the global instance
`schemeDerivedTensorMonoidal` (def-pc-scheme-derived-tensor-structure).
Source: Stacks, Tags 0A9T, 08DQ, 0FPC, 0GM7 and 09UA
(blueprint: lem-pc-perfect-tensor-hom-duality).
Proof:
1. Define the dual globally as RHom(K,O_X). The perfect-RHom comparison
   (lem-pc-perfect-rhom-tensor-comparison) puts it in D_QCoh and supplies global
   evaluation and coevaluation satisfying the zig-zag identities (08DQ, 0FPC).
2. Apply lem-pc-dualizable-tensor-hom-equivalences to this exact pairing and its
   symmetric opposite. The two tensor adjunctions give the displayed natural Hom
   equivalences for every pair of quasi-coherent complexes.
3. On an open cover, represent K by strictly perfect complexes. The termwise
   pullback computes derived pullback (lem-pc-flat-complex-derived-pullback), and
   preserves finite free modules and their direct summands. Thus Lg*K is perfect.
   Both pulled objects have quasi-coherent cohomology
   (lem-pc-derived-pullback-tensor-qcoh). The global perfect-RHom comparison on the
   source identifies Lg*(Kdual) with RHom(Lg*K,O), transporting its exact pairing.
   Only isomorphism classes, not morphisms, are checked locally.
4. Apply the same exact-pairing Hom equivalences on the source of g, for arbitrary
   quasi-coherent A and B there. -/
theorem perfect_tensor_hom_duality
    (X : Scheme.{u₁})
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁}
        (SheafOfModules.{u₁} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedQCohCategory X) (hK : Scheme.IsPerfect X K.obj) :
    ∃ Kdual : schemeDerivedQCohCategory X,
      Nonempty (ExactPairing K.obj Kdual.obj) ∧
      Nonempty (ExactPairing Kdual.obj K.obj) ∧
      Nonempty (tensorLeft K.obj ⊣ tensorLeft Kdual.obj) ∧
      Nonempty (tensorLeft Kdual.obj ⊣ tensorLeft K.obj) ∧
      (∀ A : schemeDerivedQCohCategory X,
        schemeDerivedQCohProperty X (K.obj ⊗ A.obj) ∧
        schemeDerivedQCohProperty X (Kdual.obj ⊗ A.obj)) ∧
      ∀ (T : Scheme.{u₁}) (g : T ⟶ X)
        [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings T.toRingedSpace))]
        [∀ U : T.Opens,
          HasDerivedCategory.{w₁}
            (SheafOfModules.{u₁} ((moduleRings T.toRingedSpace).over U))],
        Scheme.IsPerfect T ((derivedPullback g).obj K.obj) ∧
        schemeDerivedQCohProperty T ((derivedPullback g).obj K.obj) ∧
        schemeDerivedQCohProperty T ((derivedPullback g).obj Kdual.obj) ∧
        Nonempty (ExactPairing
          ((derivedPullback g).obj K.obj) ((derivedPullback g).obj Kdual.obj)) ∧
        Nonempty (ExactPairing
          ((derivedPullback g).obj Kdual.obj) ((derivedPullback g).obj K.obj)) ∧
        Nonempty (tensorLeft ((derivedPullback g).obj K.obj) ⊣
          tensorLeft ((derivedPullback g).obj Kdual.obj)) ∧
        Nonempty (tensorLeft ((derivedPullback g).obj Kdual.obj) ⊣
          tensorLeft ((derivedPullback g).obj K.obj)) ∧
        ∀ A : schemeDerivedQCohCategory T,
          schemeDerivedQCohProperty T (((derivedPullback g).obj K.obj) ⊗ A.obj) ∧
          schemeDerivedQCohProperty T (((derivedPullback g).obj Kdual.obj) ⊗ A.obj) := by
  sorry

end AlgebraicGeometry
