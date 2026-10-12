/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent

/-! # Unit laws for derived pullback tensor comparisons

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-unit).
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

/-- The extended natural tensor comparison admits a unit isomorphism satisfying
both unit laws. The associativity law is not assumed or asserted here.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; parent descent proof, step 3 (unit).
(blueprint: lem-pc-derived-pullback-tensor-unit).
Proof: take the structure sheaf concentrated in degree zero, which is K-flat and
represents the derived tensor unit with its recorded unit comparison. F sends the
underived tensor unit to the target tensor unit by mF. Apply Q to the unit isomorphism
of mF, then use the inverse of the supplied left-derived counit at this single complex;
that counit is invertible by comparison with the recorded K-flat computation.
Together with the source and target localization unit isomorphisms these maps give
an isomorphism η from the target derived unit to L of the source derived unit.
For a K-flat complex P, substitute the structure sheaf single complex and P into hμ.
Postcompose the proposed left unit identity with the invertible counit and localization
maps. On the summand of total degree n corresponding to (0,n), hφ reduces the identity
to left unitality of mF at P.X n. All other summands are zero. Coproduct extensionality
and cancellation give left unitality on Q(P). The same argument on summands (n,0),
using right unitality of mF, proves the right unit identity. Both sides are natural in
P, so K-flat resolutions transport these identities to every derived object.
This proof does not use the derived associativity law. -/
theorem derivedPullback_tensor_unit {T X : Scheme.{uModel}} (g : T ⟶ X)
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
    : ∃ η : 𝟙_ (schemeDerivedCategory T) ≅
        (derivedPullback g).obj (𝟙_ (schemeDerivedCategory X)),
        (∀ A : schemeDerivedCategory X,
          (λ_ ((derivedPullback g).obj A)).hom =
            η.hom ▷ (derivedPullback g).obj A ≫
              ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
              (derivedPullback g).map (λ_ A).hom) ∧
        (∀ A : schemeDerivedCategory X,
          (ρ_ ((derivedPullback g).obj A)).hom =
            (derivedPullback g).obj A ◁ η.hom ≫
              ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
              (derivedPullback g).map (ρ_ A).hom) := by sorry

end AlgebraicGeometry
