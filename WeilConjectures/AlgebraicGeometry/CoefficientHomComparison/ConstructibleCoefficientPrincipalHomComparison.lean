/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.PrincipalQuotientDualizable
import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.PrincipalScalarUnitProjection
import WeilConjectures.CategoryTheory.Monoidal.Closed.DualizableSecondHomExchange
import WeilConjectures.CategoryTheory.Adjunction.ScalarClosedProjectionFactorization
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.CoefficientHomTensorCompatibility
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! # Native Hom under principal reduction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.Adjunction

private theorem scalarClosedComparison_isIso
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    {F : C ⥤ D} {U : D ⥤ C} [F.Monoidal] (adj : F ⊣ U) (K L : C)
    (hp : ∀ M : C, IsIso (scalarUnitProjection adj M))
    (he : IsIso (MonoidalClosed.ihomTensorToIhom K L (U.obj (𝟙_ D)))) :
    IsIso (U.map ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app L)) := by
  have hh : IsIso (scalarUnitProjection adj ((ihom K).obj L) ≫
      U.map ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app L) ≫
        (scalarHomRestrictionIso adj K (F.obj L)).hom) := by
    rw [scalarClosedProjection_factorization]
    infer_instance
  have ht : IsIso (U.map ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app L) ≫
      (scalarHomRestrictionIso adj K (F.obj L)).hom) :=
    (isIso_comp_left_iff (scalarUnitProjection adj ((ihom K).obj L)) _).mp hh
  exact (isIso_comp_right_iff _ (scalarHomRestrictionIso adj K (F.obj L)).hom).mp ht

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

set_option maxHeartbeats 800000 in
-- Identify the quotient unit and its native derived scalar Hom comparison.
/-- Positive principal reduction preserves the specified native internal-Hom map.
Source: Bhatt--Scholze 6.8.14--15; Stacks 08JD, 08JJ, 08JC; the reduction paragraph
of lem-per-coefficient-comparison-finiteness.
Proof: put A = O_E and B = A/(pi^(n+1)). The uniformizer is a non-zero-divisor,
so the augmentation from the two-term free complex [A --pi^(n+1)--> A] to B is
an isomorphism in the ordinary derived category. Principal reduction normalization
identifies its tensor functor with extension followed by restriction, including
that augmentation and the scalar unit. The coefficient object B is perfect.
The perfect-factor exchange Hom(K,L) tensor B -> Hom(K,L tensor B) is invertible
by perfect duality (or by exactness and the same two-term cone). The derived scalar
internal-Hom adjunction identifies the restriction of the target with
Hom(K, restriction(extension L)). Its evaluation normalization identifies the
restriction of comparison with this perfect-factor exchange: uncurry both maps,
use the augmentation-preserving tensor comparison, and obtain evaluation tensored
with B followed by coefficient multiplication. Transport this identity through the
section-module equivalences; their tensor comparison and scalar adjunction preserve
the same balanced generators and derived units. Restriction is conservative, hence
reflects the invertibility of comparison. No completed Hom is substituted for the
ordinary derived Hom. Exponent n+1 is positive even at n=0; the same proof applies
to zero complexes and the empty scheme.
(blueprint: lem-per-constructible-coefficient-principal-hom-comparison). -/
theorem constructible_coefficient_principal_hom_comparison
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
    (K L : D X (integral.{u} ℓ E))
    (_hK : bc X (integral ℓ E) K) (_hL : bc X (integral ℓ E) L) :
    IsIso (comparison X (reductionMap ℓ E n) K L) := by
  let := scalarMonoidal X (reductionMap ℓ E n)
  let φ := coefficientMap (reductionMap ℓ E n) X
  let A := AdicCompletion.Modules ℓ (ULift.{u} E.val) X
  let B := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.finiteRing ℓ (ULift.{u} E.val) X n)
  let := DerivedCategory.symmetricCategory A
  let U : DerivedCategory B ⥤ DerivedCategory A := (Mod.comap φ).mapDerivedCategory
  let adj : scalar X (reductionMap ℓ E n) ⊣ U :=
    Mod.derivedExtendMapDerivedCategoryAdjunction φ
  let e : (DerivedCategory.singleFunctor A 0).obj
      (AdicCompletion.finiteModule ℓ (ULift.{u} E.val) X n) ≅ U.obj (𝟙_ (DerivedCategory B)) :=
    (DerivedCategory.singleFunctor A 0).mapIso
      (AdicCompletion.finiteModuleIso ℓ (ULift.{u} E.val) X n) ≪≫
    (((Mod.comap φ).mapDerivedCategorySingleFunctor 0).app (𝟙_ B)).symm ≪≫
    U.mapIso (DerivedCategory.singleFunctorObjUnitIso B)
  have hB : IsDualizable (U.obj (𝟙_ (DerivedCategory B))) :=
    (principal_quotient_dualizable X ℓ E n).of_iso e
  have hp (M : D X (integral.{u} ℓ E)) :
      IsIso (Adjunction.scalarUnitProjection adj M) :=
    principal_scalar_unit_projection X ℓ E n M
  have he : IsIso (MonoidalClosed.ihomTensorToIhom K L (U.obj (𝟙_ (DerivedCategory B)))) :=
    MonoidalClosed.isIso_ihomTensorToIhom_of_isDualizable K L _ hB
  have hmap : IsIso (U.map (comparison X (reductionMap ℓ E n) K L)) := by
    rw [comparison_eq]
    exact Adjunction.scalarClosedComparison_isIso adj K L hp he
  rw [DerivedCategory.isIso_iff]
  intro i
  have : IsIso ((Mod.comap φ).map ((DerivedCategory.homologyFunctor _ i).map
      (comparison X (reductionMap ℓ E n) K L))) :=
    (NatIso.isIso_map_iff ((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso i) _).2
      (by change IsIso ((DerivedCategory.homologyFunctor _ i).map
            (U.map (comparison X (reductionMap ℓ E n) K L)))
          infer_instance)
  exact isIso_of_reflects_iso _ (Mod.comap φ)

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
