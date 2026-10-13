/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Evaluation comparisons with a K-injective second representative

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ, 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-kinjective-evaluation-comparisons).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The local evaluation square when its second representative is already K-injective.
This only handles the resolved case; it does not assert the comparison for an arbitrary
second complex.

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ, 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-kinjective-evaluation-comparisons).

Proof:
1. Restrict derived internal Hom to U by 08DL. Transport its arguments through eK
   and eN. Because F is K-injective, the localization factorization directly
   computes this object as Q Hom(P,F), giving the target comparison b; no
   preservation of quasi-isomorphisms by Hom(P,-) is needed for this target.
2. Compute the restricted dual with Hom(P,O[0]) by 08DM. The bounded support of P
   identifies its degree-q term with Hom(P^(-q),O). Dualize each finite-free
   retraction of P^(-q), obtaining a finite-projective, hence flat, dual term.
   The bounded dual is K-flat. Exact open restriction commutes with total tensor,
   so F tensor Hom(P,O[0]) computes the source and gives the comparison a.
3. Apply the representative equation of the canonical tensor-Hom family to
   evaluation into F. On a total-tensor summand in bidegree (p,q), its uncurrying
   evaluates the degree-q dual on P^r when r+q=0, then applies the right unit
   action to F^p; every other component is zero. This is precisely hf.
4. The tensor coproduct inclusions and Hom product projections detect equality.
   Their component equalities identify the two chain maps. Localize and transport
   along eK, eN and the restriction factorization to obtain the stated square.
   All identifications use the same representative equation, rather than arbitrary
   isomorphisms. Rank-zero terms, zero complexes and empty U obey the same formula.
-/
theorem exists_strictlyPerfect_kInjective_evaluation_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    [F.IsKInjective]
    (_hstrict : Scheme.IsStrictlyPerfect X U P)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  sorry

end AlgebraicGeometry
