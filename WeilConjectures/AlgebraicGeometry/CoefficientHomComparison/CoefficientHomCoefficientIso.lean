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
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # Constructibility under the actual scalar functor of a coefficient isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

/-- Derived extension along a coefficient isomorphism preserves finite constant models.
Source: Stacks 07A4 and 03EL; coefficient transport in Step 1 of
lem-per-constructible-coefficient-hom-comparison.
Proof: extension along the forward isomorphism is naturally isomorphic to restriction
along its inverse, by uniqueness of left adjoints. Both are exact equivalences, so
their derived functors have the same comparison. Inverse scalar restriction preserves
finite presentations, constant models on every cover, and finite stratifications.
Its derived functor preserves boundedness and commutes with every cohomology functor.
Transport these constructibility assertions through the derived comparison iso.
(blueprint: lem-per-coefficient-hom-coefficient-iso). -/
theorem coefficient_iso_preserves_bc
    (X : Scheme.{u}) {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : R ≅ S) [IsMonHom e.hom] (K : D X R) (hK : bc X R K) :
    bc X S ((scalar X e.hom).obj K) := by
  let φ := coefficientMap e.hom X
  have : IsIso φ := by dsimp [φ, coefficientMap]; infer_instance
  have hi : inv φ = coefficientMap e.inv X := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← coefficientMap_comp, e.hom_inv_id, coefficientMap_id]
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.inv X)
  have : G.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap e.inv X)).functor.IsEquivalence
  let F := Mod.extendScalars φ
  let ef : F ≅ G := Mod.extendScalarsIsoComapInv φ ≪≫ Mod.comapCongr hi
  have : F.IsEquivalence := Functor.isEquivalence_of_iso ef.symm
  let ed : scalar X e.hom ≅ G.mapDerivedCategory :=
    F.leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso ef
  have hG : bc X S (G.mapDerivedCategory.obj K) := by
    refine ⟨G.bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
    exact constructible_iso ((G.mapDerivedCategoryHomologyFunctorIso n).app K)
      (constructible_comap e.inv X _ (hK.2 n))
  have : (constantModelBoundedConstructible S X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined S X).2.1
  exact (constantModelBoundedConstructible S X).prop_of_iso (ed.app K).symm hG

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
