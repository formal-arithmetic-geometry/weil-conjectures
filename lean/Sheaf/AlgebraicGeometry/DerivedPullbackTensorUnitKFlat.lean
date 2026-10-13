/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitCounit
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Unit laws on K-flat representatives

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-unit-kflat-coherence).
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

/-- The explicitly constructed unit comparison satisfies both unit laws on Q(P)
when P is K-flat. No statement about arbitrary derived objects is made here.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product;
parent unit proof, step 2, using the degree-zero unit computation of step 1.
(blueprint: lem-pc-derived-pullback-tensor-unit-kflat-coherence).
Proof: the unit complex U is the structure sheaf in degree zero and is K-flat.
The supplied counit is invertible on K-flat representatives by uniqueness of
left-derived functors and the recorded K-flat pullback computation. The source
and target localization unit maps are invertible. For the left law substitute U
and P into hμ; postcompose with the counit and localization tensorator. The
normalization of η, namely the composite in derivedPullback_tensorUnitIso, removes
the counit at U and leaves the image of the underived unit map mF.εIso. Check the
remaining complex equality degree by degree and on each total-tensor summand.
For p != 0 the U term is zero, so both maps vanish. For p = 0 and q = n,
hφ and the single-complex comparison reduce the equality to mF.left_unitality
on P.X n. Coproduct extensionality yields the complex equality; localization and
cancellation yield the left law at Q(P). Repeat with P,U: summands with q != 0
vanish, and the summand (n,0) reduces to mF.right_unitality on P.X n. This gives
the right law. No associativity, braiding compatibility of μ, or boundedness of P
is used. At the zero complex and on an empty scheme the same calculation applies. -/
theorem derivedPullback_tensor_unit_kFlat {T X : Scheme.{uModel}} (g : T ⟶ X)
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
    [IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))]
    (P : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    : (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (λ_ ((derivedPullback g).obj A)).hom =
           η.hom ▷ (derivedPullback g).obj A ≫
             ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
             (derivedPullback g).map (λ_ A).hom) ∧
      (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (ρ_ ((derivedPullback g).obj A)).hom =
           (derivedPullback g).obj A ◁ η.hom ≫
             ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
             (derivedPullback g).map (ρ_ A).hom) := by sorry

end AlgebraicGeometry
