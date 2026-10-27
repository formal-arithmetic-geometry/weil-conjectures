/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat

/-! # Flatness of component module pullback

Source: Hemo--Richarz--Scholbach, Construction (4.1) and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

/-- Component inverse image preserves flat internal modules.
Source: Hemo--Richarz--Scholbach, Construction (4.1), Proposition 4.3(3);
Stacks Project, Tag 05VD, lemma-pullback-flat
(blueprint: lem-zl-component-pullback-flat).

Proof: take the section ring and section module under the internal/sectionwise
module equivalences. The relative-test universal property says that componentTests
preserves finite limits. Its comma categories are filtered, so left Kan extension
and sheafification give a left exact inverse image on sets. The abelian and ring
lifts apply this same inverse image to the algebraic operations. Comparison of the
adjunctions with precomposition identifies their ring and module lifts, including
the scalar action, with the algebraic inverse image on section modules. The tensor
comparison is determined by the universal bilinear pairing; hence this identification
is compatible with the monoidal lift used by componentModules.

Use the local equational criterion for flatness. For a finite relation in the
inverse image module, first pass to a covering on which all its coefficients and
sections lift to the left Kan extension. After a further covering their relation
is zero there. Filteredness gives one source object on which all the lifted terms
and their relation are represented. Source flatness supplies locally a finite
factorization of the lifted sections whose coefficient matrix kills the relation.
Pull that covering and its factorization back to obtain the required factorization
of the original relation. Thus algebraic inverse image preserves site-flatness.
The coefficient isomorphism transports each relation and its factorization in both
directions, so restriction along its inverse preserves site-flatness. Finally use
the balanced tensor comparison to recover internal flatness. Empty finite lists,
the zero ring and the empty scheme satisfy the same argument. -/
theorem component_pullback_preservesFlat
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T)) :
    (componentModules Λ.X T α).PreservesFlat := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
