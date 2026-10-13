/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions

/-! # A step in the construction of homology evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Existence of the cycle-evaluation morphism.
Source: Stacks Project, Tag 0A8X, descent of the evaluation pairing.
(blueprint: new-b2-homology-evaluation-cycle-existence).

Proof: Write P = Hom(T,J). Its product projection defines the bilinear pairing
from P-cycles in degree n and T-cycles in degree -n to J in degree zero. For a
Hom cocycle phi and T-cycle z, the component differential equation gives
 d_J(phi(z)) = (-1)^n phi(d_T(z)) = 0.
Thus this pairing factors through J-cycles by their kernel universal property.
If phi = d_Hom(psi), with psi of degree n-1, evaluation on z is d_J(psi(z)),
since d_T(z)=0. If z=d_T(y), the cocycle equation in degree -n-1 gives
 phi(z)=(-1)^n d_J(phi(y)). Both values vanish after projecting to H^0(J).
The resulting bilinear pairing into H^0(J) therefore annihilates both boundary
subsheaves. Descend successively through the two cokernels defining homology.
These constructions commute with restriction because the product projections,
differentials and universal-property factorizations do. Curry the pairing by
internal Hom to obtain e. Its value on representatives is exactly the asserted
cycle formula. No cohomology concentration or finite-free hypothesis is needed.
For rank zero, zero complexes, or an empty open, the same universal properties
produce the zero pairing and the formula still holds. -/
theorem exists_homologyEvaluation_cycle (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    ∃ e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0),
      IsHomologyEvaluation X T J n e := by sorry

end CategoryTheory
