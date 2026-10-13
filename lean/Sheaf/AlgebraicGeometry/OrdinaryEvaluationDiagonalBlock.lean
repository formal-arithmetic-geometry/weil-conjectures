/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData

/-! # Invertible evaluation diagonal

Source: Stacks Project, Tags 08DQ and 08DM.
(blueprint: lem-pc-ordinary-evaluation-diagonal-block).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] localEvaluationPreadditive

/-- The diagonal component is invertible whenever its module evaluation is.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`,
termwise evaluation; Tag 08DM, degree of the dual complex.
(blueprint: lem-pc-ordinary-evaluation-diagonal-block).

Proof: in degree -r of Hom(P,O[0]), every product factor except the r-th
vanishes, since O[0] is zero in all other degrees. The product universal property
therefore makes the r-th projection an isomorphism. Compose it with internal Hom
of the single-complex degree-zero unit isomorphism. In the displayed component,
r+(-r)=0 and (r+n)+(-r)=n. Naturality of tensor-Hom adjunction, the associator,
the braiding and the right unitor identify this component with tensoring that
dual projection by F^(r+n), followed by moduleDualEvaluation. The degree transport
is the identity because its endpoints coincide. Both factors are isomorphisms:
tensoring preserves the first and hblock supplies the second. This uses no bound
on P or F, and also applies to zero modules and the empty open. -/
theorem ordinaryEvaluation_diagonal_block (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) (n r : ℤ)
    (hblock : IsIso (SheafOfModules.moduleDualEvaluation
      (X.sheaf.over U) (P.X r) (F.X (r + n)))) :
    IsIso (localEvaluationComponent X U P F (r + n) (-r) n r (by omega)) := by sorry

end AlgebraicGeometry
