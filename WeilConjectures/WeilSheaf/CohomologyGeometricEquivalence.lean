/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CohomologyExact

/-!
# The equivalence on constant-sheaf cohomology induced by a geometric isomorphism

Source: the isomorphism-invariance part of the base-change clause of
`sec-poincare-duality/sk-thm-poincare-duality/thm-weil-poincare-duality.md`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

/-- The linear equivalence induced by an isomorphism of geometric fibers.

Source: literature/blueprint/master/blueprint/sec-poincare-duality/
sk-thm-poincare-duality/thm-weil-poincare-duality.md, base-change clause.
(blueprint: def-pod-cohomology-geometric-equivalence)

Construction: identify Weil cohomology, after forgetting Frobenius, with homology of
derived global sections of the constant adic sheaf. The forgetful functor from Weil
sheaves preserves injective resolutions, and global sections at the geometric point
are exact, giving the first identification. Pushforward along e is an exact equivalence;
its composition with global sections is global sections on the source, and it carries
the constant adic sheaf to the constant adic sheaf. Derive this identity, apply homology,
and compose with the two identifications. All comparison isomorphisms are constructed
from the library's composition and exact-functor isomorphisms. -/
noncomputable def cohomologyLinearEquivOfGeometricFiberIso
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber) (i : ℤ) :
    ((WeilSheaf.adicConstant k' l Y).cohomology i).carrier ≃ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k l X).cohomology i).carrier := by
  let adicΓ (l : ℕ) [Fact l.Prime] (Z : Scheme.{u}) :
      ProEtale.AdicSheaf l Z ⥤ WeilCoefficients.{u} l :=
    ProEtale.AdicSheaf.forget Z ⋙ Sheaf.Γ _ _
  let adicLowerStarΓIso (l : ℕ) [Fact l.Prime]
      {Z W : Scheme.{u}} (g : Z ⟶ W) :
      ProEtale.adicLowerStar l g ⋙ adicΓ l W ≅ adicΓ l Z :=
    Functor.isoWhiskerLeft (ProEtale.AdicSheaf.forget Z)
      (ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l) g)
  let cohomologyCarrierIso (k : Type u) [Field k] [Finite k]
      (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))] (i : ℤ) :
      ((adicΓ l (X ↘ Spec (.of k)).geometricFiber).rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor _ i).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (ProEtale.AdicSheaf.unit l (X ↘ Spec (.of k)).geometricFiber)) ≅
        (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
          ((WeilComplex.homologySheaf i).obj ((WeilComplex.derivedLowerStar
            (X ↘ Spec (.of k))).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k l X)))).obj.carrier.X := by
    let a := X ↘ Spec (.of k)
    let f := Scheme.Hom.geometricFiberMap a (comp_over a (Spec (.of k)))
    let G := adicΓ l (Spec (.of k) ↘ Spec (.of k)).geometricFiber
    let F := adicΓ l a.geometricFiber
    let W := ProEtaleWeilSheaf.lowerStar k l a
    let M := (_root_.DerivedCategory.singleFunctor _ 0).obj (WeilSheaf.adicConstant k l X).obj
    let K := W.rightDerivedFunctor.obj M
    have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
      (ProEtale.AdicSheaf l a.geometricFiber) ℤ
    have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
      (ProEtale.AdicSheaf l a.geometricFiber) ℤ
    let e : (IsoAlgebra.forget _).mapDerivedCategory.obj K ≅
        (ProEtale.adicLowerStar l f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (ProEtale.AdicSheaf.unit l a.geometricFiber)) :=
      (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
        Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app
          (WeilSheaf.adicConstant k l X).obj)
    have : G.Additive := by dsimp [G, adicΓ]; infer_instance
    have : PreservesFiniteLimits G := by dsimp [G, adicΓ]; infer_instance
    have : G.PreservesEpimorphisms := by dsimp [G, adicΓ]; infer_instance
    have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
    have : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
    let e₀ := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (ProEtale.adicLowerStar l f) G).symm ≪≫
        Functor.rightDerivedFunctorNatIso (adicLowerStarΓIso l f)
    let e₁ := ((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso i).app K
    let e₂ := (G.mapDerivedCategoryHomologyFunctorIso i).app
      ((IsoAlgebra.forget _).mapDerivedCategory.obj K)
    exact ((G.mapIso e₁) ≪≫ e₂ ≪≫
      (_root_.DerivedCategory.homologyFunctor _ i).mapIso
        (G.mapDerivedCategory.mapIso e ≪≫ e₀.app _)).symm
  let FX := adicΓ l (X ↘ Spec (.of k)).geometricFiber
  let L := ProEtale.adicLowerStar l e.hom
  let U := ProEtale.AdicSheaf.unit l (Y ↘ Spec (.of k')).geometricFiber
  let M := (_root_.DerivedCategory.singleFunctor _ 0).obj U
  let eΓ := (Functor.rightDerivedFunctorCompIso' L FX (adicLowerStarΓIso l e.hom)).app M
  let eU := (L.singleFunctorCompRightDerivedFunctorIso).app U ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (ProEtale.adicLowerStarUnitIso l e)
  let eD := eΓ.symm ≪≫ FX.rightDerivedFunctor.mapIso eU
  exact WeilCoefficients.linearEquivOfIso
    ((cohomologyCarrierIso k' l Y i).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ i).mapIso eD ≪≫
        cohomologyCarrierIso k l X i)

end AlgebraicGeometry.WeilSheaf
