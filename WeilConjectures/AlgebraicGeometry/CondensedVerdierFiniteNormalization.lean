/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import WeilConjectures.Targets.FiniteFieldDualizingPullback
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.AlgebraicGeometry.CondensedVerdierCoefficientComparison
import WeilConjectures.AlgebraicGeometry.CondensedVerdierScalarTransport
import WeilConjectures.CategoryTheory.AdjointValueOfRepresentingObject
import all WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Normalizing the finite coefficient and dualizing-object presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Fix the site universe before inferring derived monoidal structures.
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The finite ring in the fixed universe used by the finite etale comparison.
Source: blueprint finite coefficient comparison
(blueprint: lem-sf-condensed-verdier-finite-normalization).
-/
abbrev condensedVerdierNormalizedCoefficient
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ+) :=
  finiteFieldDualizingCoefficient ℓ (ULift.{u} E.1) (n : ℕ)

/-- Apply constant sheafification to a ring equivalence, then compare the finite
constant and continuous coefficient presentations. -/
private def finiteConstantCoefficientIso
    (R : Type) (A : Type u) [CommRing R] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    (g : R ≃+* A) :
    Mon.mk (IntegralModelsEmbedded.discreteObj.{u} R) ≅
      Mon.mk (FiniteDiscreteOrdinary.coefficient A) := by
  let J := coherentTopology Profinite.{u}
  let f : ULift.{u + 1} R ≃+* ULift.{u + 1} A :=
    ULift.ringEquiv.trans (g.trans ULift.ringEquiv.symm)
  let D := constantSheaf J CommRingCat.{u + 1} ⋙
    sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let (X : CommRingCat.{u + 1}) : MonObj (D.obj X) :=
    Sheaf.monObj_sheafCompose_obj J
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj X))
  let d := D.mapIso f.toCommRingCatIso
  have : IsMonHom d.hom :=
    Sheaf.isMonHom_sheafCompose_map J
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf J CommRingCat.{u + 1}).map f.toCommRingCatIso.hom))
  have := constantCoefficientMap_isIso A
  exact Mon.mkIso' d ≪≫ Mon.mkIso' (asIso (constantCoefficientMap A))

/-- The displayed finite coefficient choice admits its explicit normalized presentation. -/
private theorem finiteNormalization_coefficientIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+)
    (he : Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj.{u}
      (PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ))))) :
    Nonempty (Mon.mk Λ ≅ Mon.mk (condensedVerdierNormalizedCoefficient ℓ E n).X) := by
  have : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional
  let A := Padic.coefficientExtensionRing ℓ (ULift.{u} E.1) (n : ℕ)
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := discreteTopology_bot A
  have : IsTopologicalRing A := DiscreteTopology.topologicalRing
  have : Finite A := Padic.finite_coefficientExtensionRing ℓ (ULift.{u} E.1) n n.pos
  obtain ⟨g⟩ := condensedVerdier_quotient_ringEquiv.{u} ℓ E π hπ n
  obtain ⟨e⟩ := he
  exact ⟨e ≪≫ finiteConstantCoefficientIso _ A g⟩

/-- The two compactifications give exactly the same prescribed support functor. -/
private theorem finiteNormalization_support_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k]
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    [QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom]
    [IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom] :
    rightDerivedLowerShriekOfCompactification Λ
        (compactificationOverField (Over.mkIdTerminal.from T)) =
      rightDerivedLowerShriekOfCompactification Λ (NagataCompactification T.hom) := by
  have hc {X Y : Scheme.{u}} (f g : X ⟶ Y)
      [HasCompactification f] [HasCompactification g] (h : f = g) :
      rightDerivedLowerShriekOfCompactification Λ (HasCompactification.compactification f) =
        rightDerivedLowerShriekOfCompactification Λ
          (HasCompactification.compactification g) := by
    subst g
    rfl
  have : HasCompactification T.hom := (NagataCompactification T.hom).hasCompactification
  have := HasCompactification.of_over (Over.mkIdTerminal.from T)
  exact hc _ _ ((Category.comp_id _).symm.trans (Over.w (Over.mkIdTerminal.from T)))

/-- Normalization data for a finite-coefficient dualizing object. These are only
coefficient, geometric pullback and adjunction comparisons; no biduality is asserted.
Source: blueprint coefficient proof (i), normalization and finite-field descent
(blueprint: lem-sf-condensed-verdier-finite-normalization). -/
structure CondensedVerdierFiniteNormalizationData
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ+)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (W : moduleDerived Λ X) where
  baseField : Type u
  [fieldInst : Field baseField]
  [algClosed : IsAlgClosed baseField]
  [charPrime : Fact (ringChar baseField).Prime]
  charNe : ringChar baseField ≠ ℓ
  geometricScheme : Scheme.{u}
  structureMap : geometricScheme ⟶ Spec (.of baseField)
  [separated : IsSeparated structureMap]
  [finiteType : LocallyOfFiniteType structureMap]
  [quasiCompact : QuasiCompact structureMap]
  [invertibleExponent : HasInvertibleExponent
    (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ (ULift.{u} E.1) (n : ℕ)))
    (Spec (.of baseField))]
  support_preserves : ∀ K : ConstantModelConstructibleFiniteTor
      (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme,
    dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X (Spec (.of baseField))
      ((rightDerivedLowerShriekOfCompactification
        (condensedVerdierNormalizedCoefficient ℓ E n).X
        (NagataCompactification structureMap)).obj K.obj)
  right : ConstantModelConstructibleFiniteTor
      (condensedVerdierNormalizedCoefficient ℓ E n).X (Spec (.of baseField)) ⥤
    ConstantModelConstructibleFiniteTor
      (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme
  adjunction : (dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X
      (Spec (.of baseField))).lift
      ((dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme).ι ⋙
        rightDerivedLowerShriekOfCompactification
          (condensedVerdierNormalizedCoefficient ℓ E n).X
          (NagataCompactification structureMap)) support_preserves ⊣ right
  unit_constructible : dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X
    (Spec (.of baseField)) (𝟙_ _)
  pull : moduleDerived Λ X ⥤
    moduleDerived (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme
  [monoidal : pull.Monoidal]
  symmetry :
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology geometricScheme) Ab.{u + 1})
        (condensedRingObj (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme))
    ∀ K L, Functor.LaxMonoidal.μ pull K L ≫ pull.map (β_ K L).hom =
      (β_ (pull.obj K) (pull.obj L)).hom ≫ Functor.LaxMonoidal.μ pull L K
  preserves : ∀ K, dctfPred Λ X K →
    dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme (pull.obj K)
  conservative : ∀ {K L : moduleDerived Λ X} (f : K ⟶ L),
    dctfPred Λ X K → dctfPred Λ X L → IsIso (pull.map f) → IsIso f
  dualizingIso : pull.obj W ≅ (right.obj ⟨𝟙_ _, unit_constructible⟩).obj
  beta_iso : ∀ K, dctfPred Λ X K →
    IsIso ((Functor.LaxMonoidal.ihomComparison pull K).natTrans.app W)

/-- Finite coefficient normalization and geometric pullback compare the actual
constructible adjunction with a normalized adjunction over an algebraically closed field.

Source: latest blueprint, det-pd-biduality-coefficients.proof.md, paragraph (i).
(blueprint: lem-sf-condensed-verdier-finite-normalization).

Proof:
1. Restriction along the inverse of the given coefficient isomorphism is an exact equivalence,
preserving the regular module, finite presentations, constant local models and Tor
intervals. Its K-flat tensor comparison is strong symmetric monoidal and its
closed comparison is invertible.
2. Exact scalar restriction commutes with open extension and derived direct image
along the proper compactification leg. Compose these two comparisons to identify
compact support. The prescribed compactification and Nagata both use
HasCompactification.compactification of the same underlying morphism; proof
irrelevance identifies their existence instances. The terminal-map equation
identifies their underlying morphisms. Restrict to constructible finite-Tor objects.
Both right adjoints
represent the same support Hom functor; adjointValueOfRepresentingObject identifies
the representing objects, and uniqueness of right adjoints gives the
counit-compatible dualizing-object isomorphism, with no arbitrary witness choice.
3. If k is algebraically closed, use k itself and the coefficient equivalence for
pull. It is conservative on all objects, hence on the indicated subcategory.
4. If k is finite, take its algebraic closure and the base change of T. Use
finiteField_dualizing_pullback for the chosen compactification. Its conservative
pullback preserves the constructible finite-Tor domain and has invertible closed
comparisons for the dualizing object. The representing Hom bijections identify
its W and Wbar with the two constructible adjoint values. Compose with the
coefficient and compactification comparisons of steps 1 and 2. Composition of
strong symmetric monoidal functors preserves the specified symmetry and closed
comparisons. The geometric field has the same positive characteristic, and the
finite ell-power exponent is invertible there since this characteristic differs
from ell. These are exactly the recorded fields, including for an empty scheme.
-/
theorem condensedVerdier_finite_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD ℓ k)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ+)
    (e : Mon.mk Λ ≅ Mon.mk (condensedVerdierNormalizedCoefficient ℓ E n).X)
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom]
    [QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom]
    [IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom]
    (G : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) ⥤
      ConstantModelConstructibleFiniteTor Λ T.left)
    (adj : ctfLowerShriek Λ ℓ k hcd (Over.mkIdTerminal.from T) hΛ ⊣ G)
    (N : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)))
    (hN : N.obj = 𝟙_ (moduleDerived Λ (Spec (.of k)))) :
    Nonempty (CondensedVerdierFiniteNormalizationData ℓ E n Λ T.left (G.obj N).obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
