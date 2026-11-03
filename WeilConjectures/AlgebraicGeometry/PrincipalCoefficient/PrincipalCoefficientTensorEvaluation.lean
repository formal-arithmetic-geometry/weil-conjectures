/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientUniversalPair
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Homology.Monoidal

/-! # Finite-resolution evaluation for coefficient coinduction

Source: latest blueprint lem-fix-operation-reduction, the two-term free resolution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing
namespace AlgebraicGeometry.PrincipalCoefficient

/-- The ordinary tensor/coinduction map is specified by its evaluation counit,
on each homogeneous tensor summand. This is an equality of sheaf morphisms;
no choice of points, sectionwise sheafification inverse, or derived lift occurs.
Source: Stacks 0A70 and 0A71
(blueprint: lem-principal-coefficient-tensor-evaluation). -/
def CoinductionTensorEvaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (P I J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (p : P ⊗ I ⟶ J)
    (t :
      ((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((Etale.coextendScalars φ X).mapHomologicalComplex (.up ℤ)).obj I ⟶
      ((Etale.coextendScalars φ X).mapHomologicalComplex (.up ℤ)).obj J) : Prop :=
  let E := Sheaf.extendScalars X.smallEtaleTopology φ
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let H := Etale.coextendScalars φ X
  let a := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  ∀ (i j k : ℤ) (h : i + j = k),
    ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).unit.app (P.X i) ▷
        U.obj (H.obj (I.X j))) ≫
        Functor.LaxMonoidal.μ U (E.obj (P.X i)) (H.obj (I.X j)) ≫
        U.map ((HomologicalComplex.ιTensorObj
          ((E.mapHomologicalComplex (.up ℤ)).obj P)
          ((H.mapHomologicalComplex (.up ℤ)).obj I) i j k h) ≫ t.f k) ≫
        a.counit.app (J.X k) =
      (P.X i ◁ a.counit.app (I.X j)) ≫
        HomologicalComplex.ιTensorObj P I i j k h ≫ p.f k

/-- Evaluation against a regular quotient is a quasi-isomorphism on K-flat inputs.
Source: latest blueprint lem-fix-operation-reduction, the regular two-term free
coefficient resolution; Stacks 0A70, 0BZE, 0BZH and 08JJ
(blueprint: lem-principal-coefficient-tensor-evaluation).

Proof: resolve B by the bounded finite-free constant complex [A --a^n--> A].
Ordinary restriction identifies coinduction into a K-injective target with Hom
from the constant B-module. Precomposition with this resolution is a
quasi-isomorphism: its cone is acyclic, and Hom into a K-injective complex is
acyclic. For a bounded finite-free source, the signed tensor/Hom evaluation map
is an isomorphism of total complexes for every unbounded first factor. In each
degree its products have only two nonzero factors, and its signs agree with the
signed tensor differential. For the K-flat P, tensoring the comparison into I
preserves this quasi-isomorphism. Postcomposition with the quasi-isomorphism p
also preserves it because Hom from a bounded finite-free complex preserves
quasi-isomorphisms. The equation in CoinductionTensorEvaluation identifies the
resulting commuting square with t after restriction. Its other three arrows are
quasi-isomorphisms, so t is one as well. Exact restriction reflects this property.
All Hom comparisons are made for the actual sheaves (or on their slices), rather
than treating sheaf sections as an exact functor. For n=0 the resolution is
contractible and the quotient category is zero. -/
theorem principalTensorEvaluation_quasiIso
    {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) (X : Scheme.{u})
    (P I J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    [I.IsKInjective] [J.IsKInjective] (p : P ⊗ I ⟶ J) [QuasiIso p]
    (t :
      ((Sheaf.extendScalars X.smallEtaleTopology
        (Ideal.Quotient.mk (Ideal.span {a} ^ n))).mapHomologicalComplex (.up ℤ)).obj P ⊗
      ((Etale.coextendScalars
        (Ideal.Quotient.mk (Ideal.span {a} ^ n)) X).mapHomologicalComplex (.up ℤ)).obj I ⟶
      ((Etale.coextendScalars
        (Ideal.Quotient.mk (Ideal.span {a} ^ n)) X).mapHomologicalComplex (.up ℤ)).obj J)
    (ht : CoinductionTensorEvaluation (Ideal.Quotient.mk (Ideal.span {a} ^ n)) X P I J p t) :
    QuasiIso t := by
  sorry

end AlgebraicGeometry.PrincipalCoefficient
