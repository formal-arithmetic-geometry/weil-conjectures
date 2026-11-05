/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Main
public import WeilConjectures.WeilObject.BoundedConstructible.Homology

/-!
# The `0`-th homology sheaf of the canonical Weil unit

Let `ℓ` be a prime, `X` a separated scheme of finite type over a field `k` with an automorphism
`e : X ≅ X` over `Spec k`, and write `e^* = (e.hom.left)^*⟦ℚ̲̄_ℓ⟧`. The canonical Weil unit
`ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ProEtale.CondensedRing.WeilBoundedConstructible.unit`) is the unit
module object placed in degree `0`, with structure isomorphism the inverse of the unit comparison
of the derived pullback `Le^*`. This file computes the structure isomorphism of its `0`-th
homology sheaf `H⁰(ℚ̲̄_ℓ,X)`: under the identification `H⁰(ℚ̲̄_ℓ[0]) ≅ ℚ̲̄_ℓ`, it is the inverse of
the unit comparison `ε : ℚ̲̄_ℓ ≅ e^* ℚ̲̄_ℓ` of the monoidal functor `e^*`.

The computation is reduced to a general statement about an exact functor `F` between abelian
categories (`DerivedCategory.mapDerivedCategoryHomologyFunctorIso_hom_app_comp_singleHom`): the
commutation `H⁰ ⋙ F ≅ D(F) ⋙ H⁰` at `A[0]`, followed by the morphism `F(A[0]) ⟶ B[0]` induced by
a morphism `φ : F A ⟶ B`, is `F(H⁰(A[0]) ≅ A) ≫ φ`.

## Main results

- `DerivedCategory.homologyFunctorZeroQhSingleIso`: the identification `H⁰(A[0]) ≅ A`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctor_obj_unit_str_hom_comp`: the
  structure isomorphism of `H⁰(ℚ̲̄_ℓ,X)` is the inverse of the unit comparison of `e^*`.
-/

@[expose] public section

universe w w' u u' v v'

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι)
  (j : ι) [DecidableEq ι]

/-- The inverse form of `Functor.mapHomologicalComplexHomologyIso_hom_app_single`. -/
@[reassoc]
lemma mapHomologicalComplexHomologyIso_inv_app_single (A : C) :
    (F.mapHomologicalComplexHomologyIso c j).inv.app ((HomologicalComplex.single C c j).obj A) ≫
        HomologicalComplex.homologyMap
          ((HomologicalComplex.singleMapHomologicalComplex F c j).hom.app A) j ≫
        (HomologicalComplex.homologyFunctorSingleIso D c j).hom.app (F.obj A) =
      F.map ((HomologicalComplex.homologyFunctorSingleIso C c j).hom.app A) := by
  rw [← mapHomologicalComplexHomologyIso_hom_app_single, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X) (n : ℤ)

/-- The Frobenius comparison of the `n`-th homology sheaf at `K` is the commutation
`e^* Hⁿ(K) ≅ Hⁿ(D(e^*) K)` followed by the identification of `D(e^*)` with `Le^*`. -/
lemma weilHomologyComparison_hom_app (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilHomologyComparison ℓ e n).hom.app K =
      ((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapDerivedCategoryHomologyFunctorIso n).hom.app
          K.obj ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
            e.hom.left).inv.app K.obj) := by
  simp [weilHomologyComparison, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- The structure isomorphism of the `n`-th homology sheaf `Hⁿ(K)` is `e^* Hⁿ(K) ≅ Hⁿ(Le^* K)`
followed by `Hⁿ(φ_K)`. -/
lemma WeilBoundedConstructible.homologyFunctor_obj_str (K : WeilBoundedConstructible ℓ e.hom) :
    ((WeilBoundedConstructible.homologyFunctor ℓ e n).obj K).str =
      (weilHomologyComparison ℓ e n).app K.carrier ≪≫
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ _

end AlgebraicGeometry.ProEtale.CondensedRing
