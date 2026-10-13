/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor
import Sheaf.Algebra.Homology.KFlatScalarExtensionCounit

/-! # Termwise Tor acyclicity for the universal base-tensor comparison

Source: Stacks Project, Tag 08IB, local affine comparison, and Tag 06Y6.
(blueprint: lem-pc-termwise-tor-acyclic-base-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB uD v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat.BaseDerivedTensorCohomologyModel

attribute [local instance] ULift.algebra'

variable {R : Type uR} {A : Type uA} {B : Type uB} {D : Type uD}
  [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} B)]
  {Q : CochainComplex (ModuleCat.{max uR uA uB uD v} A) ℤ}

/-- Source: Stacks Project, Tag 08IB, affine Tor-independent comparison;
Tag 06Y6, computation of a derived functor on K-flat resolutions.
(blueprint: lem-pc-termwise-tor-acyclic-base-comparison).

Proof: Lift R, B and each term to the common carrier universe. The equivalences
along the ring isomorphisms ULift R ≃ R and ULift B ≃ B preserve homology and
intertwine scalar extension with tensoring by ULift B (tensor symmetry accounts
for its placement on the right). Apply the termwise Tor-acyclic comparison to a
K-flat resolution of the restricted bounded complex. Its tensor augmentation is
a quasi-isomorphism. The left-derived counit computed on this resolution is
therefore an isomorphism; uniqueness of the universal derived pair transports
this to M.counit. More explicitly, in the naturality square for the resolution
augmentation, its image under the localized derived functor is invertible,
the counit at the K-flat source is invertible by
scalarExtensionCounit_isIso_of_kFlat after the same universe transport, and the
ordinary-tensor image of
the augmentation is invertible by termwise Tor acyclicity. Thus the fourth side,
the counit at Q, is invertible. The argument also applies to the zero complex,
zero rings and arbitrary bounds, including m > n. No localization or finite
projectivity is required. -/
theorem counit_isIso_of_termwise_tor_acyclic
    (M : BaseDerivedTensorCohomologyModel R A B Q D)
    (hbounded : ∃ m n : ℤ, ∀ i : ℤ, i < m ∨ n < i → IsZero (Q.X i))
    (hTor : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((CategoryTheory.Tor'
        (ModuleCat.{max uR uA uB uD v} (ULift.{max uR uA uB uD v} R)) i).obj
        (@ModuleCat.of (ULift.{max uR uA uB uD v} R) _
          (ULift.{max uR uA uB uD v} (Q.X n)) inferInstance
          (Module.compHom _ (algebraMap (ULift.{max uR uA uB uD v} R)
            (ULift.{max uR uA uB uD v} A))))).obj
        (ModuleCat.of (ULift.{max uR uA uB uD v} R)
          (ULift.{max uR uA uB uD v} B)))) :
    IsIso (M.counit.app ((HomotopyCategory.quotient _ _).obj
      (((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex
        (.up ℤ)).obj Q))) := by sorry

end ModuleCat.BaseDerivedTensorCohomologyModel
