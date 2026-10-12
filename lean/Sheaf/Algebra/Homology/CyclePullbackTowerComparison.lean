/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Algebra.Homology.CyclePullbackTower

/-!
# Pointwise comparisons for the explicit cycle-pullback tower

Source: Stacks Project, Derived Categories, Lemma 05T7 (1), together with pointwise
computation of kernels and pullbacks in functor categories.
-/

@[expose] public section

universe v u vB uB
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.CyclePullback

/-- Evaluation of the specific tower's current term is T of the pointwise cycle pullback.

Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: lem-pc-cycle-pullback-tower-comparison-stage3).

Proof: Write the stage in degree i as the successor of the stage in degree i+1.
Its current functor is, by definition, the pullback functor followed by T. Evaluation
preserves the kernel of the next differential, and identifies its inclusion with
the inclusion of the pointwise kernel. Evaluation also preserves the pullback.
Use these two canonical isomorphisms, and the proved degree transports, to identify
the evaluation of the pullback functor with the pullback in the statement. Apply T
to this isomorphism. Naturality of pi moves it past T of the comparison map. The
first projection equation of the pullback comparison is then the definition of
the augmentation; the second projection equation, followed by the kernel comparison
inclusion equation, is the definition of the differential. At i=N the preceding
stage is the initial zero stage and the identical universal-property calculation
applies. No preservation of limits or zero objects by T is used. The statement
concerns only the explicitly defined tower, never an arbitrary bounded complex. -/
theorem tower_comparison {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    let d := (differential T π F N (i + 1)).app b
    let f := (F.obj b).d i (i + 1)
    let g := kernel.ι d ≫ (augmentation T π F N (i + 1)).app b
    ∃ (c : (term T π F N i).obj b ≅ T.obj (pullback f g)),
      c.hom ≫ π.app (pullback f g) ≫ pullback.fst f g =
        (augmentation T π F N i).app b ∧
      c.hom ≫ π.app (pullback f g) ≫ pullback.snd f g ≫ kernel.ι d =
        (differential T π F N i).app b := by sorry

end CochainComplex.CyclePullback
