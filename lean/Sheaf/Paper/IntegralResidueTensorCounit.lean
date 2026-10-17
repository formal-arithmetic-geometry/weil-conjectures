module

public import Sheaf.Paper.IntegralResidueTensorPresentation

/-! # Canonical residue tensor counit and comparison equations

Source: Bhatt--Scholze, Lemma 6.5.9(3).
(blueprint: new-integral-residue-tensor-counit)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

/-- The generic scalar tensor presentation is fixed by its canonical counit.
Source: Bhatt--Scholze, Lemma 6.5.9(3); canonical balanced tensor presentation.
(blueprint: new-integral-residue-tensor-counit)
Proof. Unfold the generic constructor; both sides are the same derived tensor presentation. -/
theorem residueDerivedTensorIso_eq :
    letI := Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor φ
    residueDerivedTensorIso φ =
      CategoryTheory.derivedTensorPresentationIso _ _ (Mod.tensorPresentationDerivedCounit φ) := by
  unfold residueDerivedTensorIso
  rfl

end CategoryTheory.Mod

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The restricted regular residue module, before passing to degree zero.
Source: Bhatt--Scholze, Lemma 6.5.9(3), the scalar tensor presentation.
(blueprint: new-integral-residue-tensor-counit) -/
noncomputable abbrev residueExchangeOrdinaryCoefficientObj (T : Scheme.{u}) :=
  (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T))

/-- The canonical scalar tensor counit with the coefficient functors kept folded.
Source: Bhatt--Scholze, Lemma 6.5.9(3); the balanced tensor presentation.
(blueprint: new-integral-residue-tensor-counit) -/
@[irreducible] noncomputable def residueExchangeTensorCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ (residueExchangeReduction ℓ E T ⋙
      residueExchangeRestriction ℓ E T) ⟶
    (tensorLeft (residueExchangeOrdinaryCoefficientObj ℓ E T)).mapHomotopyCategory
      (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold residueExchangeOrdinaryCoefficientObj
  unfold residueExchangeReduction integralReduction residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit (coefficientMap (integralReductionMap ℓ E) T)

/-- The named counit exhibits restricted reduction as the derived tensor functor.
Source: Bhatt--Scholze, Lemma 6.5.9(3); uniqueness of derived scalar extension.
(blueprint: new-integral-residue-tensor-counit)
Proof. Unfold the coefficient functors and use the balanced tensor counit's
left-derived universal property. -/
theorem residueExchangeTensorCounit_isLeftDerivedFunctor (T : Scheme.{u}) :
    (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T).IsLeftDerivedFunctor
      (residueExchangeTensorCounit ℓ E T)
      (HomotopyCategory.quasiIso
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ)) := by
  unfold residueExchangeOrdinaryCoefficientObj residueExchangeTensorCounit
    residueExchangeReduction integralReduction
    residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor
    (coefficientMap (integralReductionMap ℓ E) T)

/-- The concrete tensor presentation is the one fixed by its named counit.
Source: Bhatt--Scholze, Lemma 6.5.9(3); canonical derived tensor presentation.
(blueprint: new-integral-residue-tensor-counit)
Proof. This is the defining equation of the concrete wrapper. -/
theorem residueExchangeTensorIso_eq (T : Scheme.{u}) :
    letI := residueExchangeTensorCounit_isLeftDerivedFunctor ℓ E T
    residueExchangeTensorIso ℓ E T =
      derivedTensorPresentationIso (residueExchangeOrdinaryCoefficientObj ℓ E T)
        (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T)
        (residueExchangeTensorCounit ℓ E T) := by
  unfold residueExchangeTensorIso residueExchangeTensorCounit
    residueExchangeOrdinaryCoefficientObj residueExchangeReduction integralReduction
    residueExchangeRestriction
  exact Mod.residueDerivedTensorIso_eq (coefficientMap (integralReductionMap ℓ E) T)

end AlgebraicGeometry.ProEtale.CondensedRing
