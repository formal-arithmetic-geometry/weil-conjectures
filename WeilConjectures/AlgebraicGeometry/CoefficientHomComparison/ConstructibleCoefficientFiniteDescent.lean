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
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Finite coefficient-field descent in the constant-model convention -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

/-- Every constructible algebraic-closure complex descends to a finite coefficient field.
Source: Bhatt--Scholze 6.8.14(2) and Hemo--Richarz--Scholbach Lemma 7.9; Step 5 of
lem-per-constructible-coefficient-hom-comparison.
Proof: compare the finite constant model predicate with bounded constructibility for
both coefficient fields. Apply essential surjectivity of the finite-field constructible
cocone to the given bounded constructible algebraic-closure object. Its scalar functor
is the actual left-derived extension along the finite-field inclusion. The full
subcategory inclusion sends the resulting isomorphism to the required ambient one.
The chosen algebraic-closure condensed ring is unchanged throughout.
(blueprint: lem-per-constructible-coefficient-finite-descent). -/
theorem constructible_coefficient_finite_descent
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime]
    (K : D X (Profinite.padicAlgClRingObj.{u} ℓ))
    (hK : bc X (Profinite.padicAlgClRingObj ℓ) K) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (L : D X (Profinite.continuousMapRingObj.{u} E.val)),
      bc X (Profinite.continuousMapRingObj E.val) L ∧
        Nonempty ((scalar X (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)).obj L ≅ K) := by
  have hK' : boundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) X) K := by
    rwa [(adicConstructibilityPredicateComparison ℓ X _ .algebraicClosure).2]
  obtain ⟨E, L, ⟨e⟩⟩ := constructibleCocone_essSurjObj X ℓ ⟨K, hK'⟩
  refine ⟨E, L.obj, ?_, ⟨(boundedConstructible _).ι.mapIso e⟩⟩
  change constantModelBoundedConstructible (Profinite.continuousMapRingObj E.val) X L.obj
  rw [← (adicConstructibilityPredicateComparison ℓ X _ (.continuous E.val)).2]
  exact L.property

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
