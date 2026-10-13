/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Int.Interval

/-! # Finite source decomposition

Source: Stacks Project, Tags 08DQ and 08DM.
(blueprint: lem-pc-ordinary-evaluation-source-biproduct).
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

/-- The total tensor degree is the finite biproduct of its possibly nonzero summands.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`, tensor sum.
(blueprint: lem-pc-ordinary-evaluation-source-biproduct).

Proof: the product projections of Hom(P,O[0]) identify degree q with
Hom(P^(-q),O): all factors except r=-q have zero target and hence are zero.
The projection followed by the degree-zero unit isomorphism is the identification.
Consequently this dual is zero outside [-b,-a]. Tensoring preserves zero objects,
so in total degree n all summands except p=r+n,q=-r with a<=r<=b vanish.
The coproduct universal property discards the zero summands and reindexes the
remaining ones by r. In an additive category a finite coproduct is a biproduct.
Its induced isomorphism has exactly the inclusion equations below; these equations
also determine it uniquely. If b<a, all summands vanish and the empty biproduct
is the zero object. No boundedness assumption on F is used. -/
theorem ordinaryEvaluation_source_biproduct (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) (a b n : ℤ)
    (hbounded : ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r)) :
    ∃ e : (⨁ fun r : ↥(Finset.Icc a b) ↦
        F.X (r.val + n) ⊗ (localEvaluationDual X U P).X (-r.val)) ≅
          (localEvaluationTensor X U P F).X n,
      ∀ r : ↥(Finset.Icc a b),
        biproduct.ι _ r ≫ e.hom =
          HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
            (curriedTensor _) (.up ℤ) (r.val + n) (-r.val) n
            (by change r.val + n + -r.val = n; omega) := by sorry

end AlgebraicGeometry
