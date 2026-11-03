/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit

/-!
# Projection formula with rational coefficients

Source: blueprint latest, sec-six-functors-basics/sk-thm-sf-pf-field,
node sk-thm-sf-pf-field (blueprint: sk-thm-sf-pf-field).

The theorem states tensor closure of the localizing closure of bounded constructible
finite-Tor module complexes and the proper projection formula in the ambient unbounded
derived categories. The coefficient hypothesis is exactly the two rational cases:
a finite subextension of `ℚ_ℓ` or the finite-subextension-valued algebraic closure.
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

attribute [local instance 1]
  AlgebraicGeometry.ProEtale.CondensedRing.ProjectionMorphismData.category

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Projection formula with rational coefficients on localizing closures.

Source: blueprint latest, sec-six-functors-basics/sk-thm-sf-pf-field, node
sk-thm-sf-pf-field (blueprint: sk-thm-sf-pf-field).

Proof:
1. The standing schemes are qcqs. The rational finite-Tor comparison identifies the
   constant-model constructible predicate with its finite-Tor intersection, hence their
   localizing closures agree. The finite-coefficient descent comparison identifies the
   constant-model and adopted bounded-constructible predicates for the two standard rings;
   exact restriction along a coefficient isomorphism transports this equality to `Λ`.
2. Apply `tensorClosureRational` to the resulting localizing predicates.
3. Use the shared `projection_localizing_of_interfaces` argument of the detailed rational
   localizing projection formula. Proper direct image preserves the generators and their
   coproducts, transported along the coefficient isomorphism. Pullback preserves bounded
   constructibility, and the tensor theorem supplies bounded tensor closure on both
   schemes. On generators, the rational bounded proper projection formula is transported
   by the coefficient-projection square. The two-variable localizing determination
   argument proves that the canonical projection map is an isomorphism. -/
theorem projectionFormulaField
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ (A B : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj Λ X.left))),
      localizingClosureProEtale Λ X.left A →
      localizingClosureProEtale Λ X.left B →
      localizingClosureProEtale Λ X.left
        (((derivedTensor Λ X.left).obj A).obj B)) ∧
    (∀ (p : X ⟶ Y) [IsProper p.left]
      (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj Λ X.left)))
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj Λ Y.left))),
      localizingClosureProEtale Λ X.left M →
      localizingClosureProEtale Λ Y.left N →
      IsIso (moduleObjectProjectionMap Λ p.left M N)) := by
  have hc :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hΛ with ⟨E, e⟩ | e
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr e⟩))
    · exact Or.inr (Or.inr (Or.inr e))
  have hctf (T : Over (Spec (.of k))) [QuasiCompact T.hom] [IsSeparated T.hom] :
      (constantModelBoundedConstructible Λ T.left ⊓ DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ T.left := by
    have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
    have : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
    exact (integral_ctf_equals_bc ℓ T.left (Mon.mk Λ) hc).2.2.2
  have hloc (T : Over (Spec (.of k))) [QuasiCompact T.hom] [IsSeparated T.hom] :
      localizingClosureProEtale Λ T.left =
        CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ T.left) := by
    unfold localizingClosureProEtale
    rw [hctf T]
  have hbc (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
      [QuasiCompact T.hom] [IsSeparated T.hom] :
      constantModelBoundedConstructible Λ T.left =
        boundedConstructible (condensedRingObj Λ T.left) := by
    let : T.left.Over (Spec (.of k)) := ⟨T.hom⟩
    let : LocallyOfFiniteType (T.left ↘ Spec (.of k)) := inferInstanceAs
      (LocallyOfFiniteType T.hom)
    let : QuasiCompact (T.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact T.hom)
    let : IsSeparated (T.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated T.hom)
    have heq := (finiteCoefficientDescentTwoColimit k (ringChar k) ℓ
      (Fact.out : (ringChar k).Prime).pos Fact.out T.left).2.2.2
    funext K
    apply propext
    rcases hΛ with ⟨E, he⟩ | he
    · obtain ⟨e⟩ := he
      exact (constantModel_derived_comap_iff e.inv.hom T.left K).symm.trans
        ((congrFun (heq.1 E).1 _).to_iff.trans
          (NormedCoefficientRealization.bounded_comap_iff (coefficientMap e.inv.hom T.left) K))
    · obtain ⟨e⟩ := he
      exact (constantModel_derived_comap_iff e.inv.hom T.left K).symm.trans
        ((congrFun heq.2.1.1 _).to_iff.trans
          (NormedCoefficientRealization.bounded_comap_iff (coefficientMap e.inv.hom T.left) K))
  constructor
  · intro A B hA hB
    rw [hloc X] at hA hB ⊢
    exact (tensorClosureRational ℓ (ringChar k)
      (Fact.out : (ringChar k).Prime).pos Fact.out X.hom Λ hΛ).2 A B hA hB
  · intro p hp M N hM hN
    let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := inferInstanceAs
      (LocallyOfFiniteType X.hom)
    let : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
    let : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
    let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := inferInstanceAs
      (LocallyOfFiniteType Y.hom)
    let : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
    let : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
    let : p.left.IsOver (Spec (.of k)) := ⟨p.w⟩
    have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
    have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
    have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
    have hproper : ProperLocalizingHypotheses Λ p.left := by
      rcases hΛ with ⟨E, he⟩ | he
      · obtain ⟨e⟩ := he
        exact properHypotheses_coefficientIso e p.left
          (proper_image_localizing_proper_coefficients ℓ E (ZMod ℓ) ⟨1, by simp⟩
            (Mon.mk _) (by simp) k p.left)
      · obtain ⟨e⟩ := he
        let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
        exact properHypotheses_coefficientIso e p.left
          (proper_image_localizing_proper_coefficients ℓ E (ZMod ℓ) ⟨1, by simp⟩
            (Mon.mk _) (by simp) k p.left)
    have htensor (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
        [QuasiCompact T.hom] [IsSeparated T.hom] :=
      (tensorClosureRational ℓ (ringChar k)
        (Fact.out : (ringChar k).Prime).pos Fact.out T.hom Λ hΛ).1
    rw [hloc X] at hM
    rw [hloc Y] at hN
    have h := projection_localizing_of_interfaces Λ p.left (hbc X) (hbc Y)
      (hctf X) (hctf Y) hproper
      (pullback_bounded_constructible Λ p.left (pullback_constructible Λ p.left))
      (htensor X) (htensor Y) (fun K L hK hL ↦ ?_) M N hM hN
    · simpa only [moduleObjectProjectionMate, moduleObjectDerivedTensorComparison,
        moduleObjectProjectionMap, moduleObjectProjectionData] using h.2.2
    · apply (canonical_projection_isIso Λ p.left K L).mp
      rcases hΛ with ⟨E, he⟩ | he
      · obtain ⟨e⟩ := he
        apply projection_isIso_of_coefficientIso e.hom.hom ℓ k p K L
        exact isIso_properProjectionMap_boundedConstructible_rational ℓ p
          (Mon.mk _) (Or.inl ⟨E, rfl⟩) _ _
          (bounded_scalar e X.left K hK) (bounded_scalar e Y.left L hL)
      · obtain ⟨e⟩ := he
        apply projection_isIso_of_coefficientIso e.hom.hom ℓ k p K L
        exact isIso_properProjectionMap_boundedConstructible_rational ℓ p
          (Mon.mk _) (Or.inr rfl) _ _
          (bounded_scalar e X.left K hK) (bounded_scalar e Y.left L hL)

end AlgebraicGeometry.ProEtale.CondensedRing
