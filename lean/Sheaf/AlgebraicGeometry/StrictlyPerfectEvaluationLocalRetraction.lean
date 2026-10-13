/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # A local retraction of canonical derived evaluation

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ,
proof of lemma-dual-perfect-complex; Tags 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-local-retraction).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A local retraction of canonical derived evaluation.
Only one inverse identity is asserted. No representative of N and no
comparison square with a prescribed ordinary chain map is part of the statement.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ,
proof of lemma-dual-perfect-complex; Tags 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-local-retraction).

Proof:
1. Represent RN by a K-injective complex F. By 08DL and the representative
   computation of derived internal Hom, RH(K,N) is computed by Q Hom(P,F).
2. By 08DM the restricted derived dual is computed by Hom(P,O[0]). Its
   degree-q term is Hom(P^(-q),O). Dualize the finite free retractions of
   P to see that these terms are finite projective and flat. The support
   is the negation of the support of P, so this dual is bounded and K-flat.
   Exact restriction commutes with total tensor. Consequently R(N tensor D)
   is computed by Q Tot(F tensor Hom(P,O[0])).
3. The canonical tensor-Hom representative equation identifies R.map g
   between these models with ordinary evaluation. On the (p,q) summand
   and r-th Hom projection it evaluates the dual on P^r when r+q=0,
   then applies the right unit action on F^p; otherwise it is zero.
   Currying, associativity and the symmetry give this formula with the
   same order of the factors as in the statement.
4. On a summand F^p tensor Hom(P^(-q),O), evaluation followed by its
   inverse is the identity. Check this first for finite free terms on basis
   sections; the two maps are natural under the inclusion and projection of
   a finite free retraction, so the identity descends to P^(-q). The inverse
   commutes with differentials because the evaluation is a chain map.
5. Total-tensor inclusions detect equality in each degree. Thus evaluation
   followed by its inverse is the identity on the ordinary tensor complex.
   Localize this equation and conjugate by the source model isomorphism.
   It gives R.map g followed by r equal to the identity, as asserted.
Rank zero, zero complexes and empty opens give the same identities on zero
objects; F may be unbounded because the finite support is that of P.
-/
theorem exists_strictlyPerfect_evaluation_local_retraction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (_hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ r : R.obj (H.obj (op K, N)) ⟶ R.obj (N ⊗ D),
      R.map g ≫ r = 𝟙 (R.obj (N ⊗ D)) := by sorry

end AlgebraicGeometry
