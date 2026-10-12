/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatTensorProduct
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Associativity of derived pullback tensor comparisons

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-associativity).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance]
  tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

/-- The extended natural tensor comparison satisfies the associativity law.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; parent descent proof, step 3 (associativity).
(blueprint: lem-pc-derived-pullback-tensor-associativity).
Proof: resolve the three derived arguments by K-flat complexes P, N, and R.
Their two bracketed tensor products are K-flat. The comparison formula hμ identifies
both sides, after composition with the invertible localization tensorators and counits,
with the two termwise maps from F(P) tensor F(N) tensor F(R) to F of the triple tensor.
Precompose in each total degree with the inclusion of each summand indexed by p,q,r.
The summand formula hφ identifies each occurrence of phi with the inverse tensorator
of mF. The resulting equality is precisely associativity of mF at P.X p, N.X q,
and R.X r. Coproduct extensionality proves equality of the complex maps; applying Q
and cancelling the invertible comparison maps gives the desired identity on these
K-flat representatives. Both composites are natural in all three derived arguments
because μ is an isomorphism of bifunctors. Transport the identity along the three
resolution isomorphisms to obtain it on arbitrary objects. No unit isomorphism or
unitality law is used. -/
theorem derivedPullback_tensor_associativity {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (μ : curriedTensorPre (derivedPullback g) ≅ curriedTensorPost (derivedPullback g))
    (hμ : ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := X.sheaf) P →
          CochainComplex.IsKFlat (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    : ∀ A B C : schemeDerivedCategory X,
        ((μ.app A).app B).hom ▷ (derivedPullback g).obj C ≫
            ((μ.app (A ⊗ B)).app C).hom ≫ (derivedPullback g).map (α_ A B C).hom =
          (α_ ((derivedPullback g).obj A) ((derivedPullback g).obj B)
            ((derivedPullback g).obj C)).hom ≫
            (derivedPullback g).obj A ◁ ((μ.app B).app C).hom ≫
            ((μ.app A).app (B ⊗ C)).hom := by sorry

end AlgebraicGeometry
