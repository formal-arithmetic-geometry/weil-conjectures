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

/-! # A local section of canonical derived evaluation

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ,
proof of lemma-dual-perfect-complex; Tags 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-local-section).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A local section of canonical derived evaluation.
Only one inverse identity is asserted. No representative of N and no
comparison square with a prescribed ordinary chain map is part of the statement.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ,
proof of lemma-dual-perfect-complex; Tags 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-local-section).

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
4. On a factor Hom(P^r,F^(r+n)), the inverse of evaluation followed by
   evaluation is the identity. For a finite free term the inverse sends a
   map to the sum of its values on basis sections tensored with the dual
   basis. For a finite free retract, precompose with the projection and
   restrict the dual along the inclusion. Their composite is the identity
   because inclusion followed by projection is the identity on P^r.
   Evaluation is a chain map, so its degreewise inverse is a chain map.
5. The Hom product projections detect equality in every degree. Thus the
   inverse followed by evaluation is the identity on the Hom complex.
   Localize this equation and conjugate by the target model isomorphism.
   It gives s followed by R.map g equal to the identity, as asserted.
Rank zero, zero complexes and empty opens give the same identities on zero
objects; F may be unbounded because the finite support is that of P.
-/
theorem exists_strictlyPerfect_evaluation_local_section (X : Scheme.{u})
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
    ∃ s : R.obj (H.obj (op K, N)) ⟶ R.obj (N ⊗ D),
      s ≫ R.map g = 𝟙 (R.obj (H.obj (op K, N))) := by sorry

end AlgebraicGeometry
