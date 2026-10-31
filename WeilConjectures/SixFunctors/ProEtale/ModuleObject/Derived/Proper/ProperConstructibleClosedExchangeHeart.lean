/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperConstructibleLiftedTestRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedExchangeAffineDescent
import WeilConjectures.AlgebraicGeometry.ClosedLiftedTestIsomorphismCriterion.ClosedLiftedTestIsomorphismCriterion
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality

/-! # Proper closed exchange for constructible sheaves in degree zero

Source: blueprint latest, compactification coherence, refinement (2), closed-complement
calculation. This is the sheaf case of the closed lifted-test argument; no Tor bound
is imposed on the sheaf (blueprint: lem-sfb-proper-constructible-closed-exchange-heart).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  condensedAmbientExchange moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.sectionsOver
  ClosedTestDerivedExchangeModel.exchange ClosedTestDerivedExchangeModel.testRestriction

private theorem local_exchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (ClosedTestDerivedExchangeModel.closedMap A I))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  apply ClosedLiftedTestIsomorphismCriterion.closed_lifted_tests_detect_isomorphisms Λ A I
  intro V hV hW
  have := hV
  have := hW
  exact proper_constructible_lifted_test_restriction Λ ℓ hΛ A I f h fZ w M hM V

private theorem pulled_exchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (ClosedTestDerivedExchangeModel.closedMap A I))
    {Y : Scheme.{u}} (a : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ X ((upperStar Λ a).obj M)) :
    IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ a).obj M))) := by
  exact local_exchange Λ ℓ hΛ A I f h fZ w ((upperStar Λ a).obj M) hM

private theorem constructible_pullback_on_qcqs
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (a : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((upperStar Λ a).obj M) := by
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply stratified_pullback Λ a M
  simpa only [IsConstantModelConstructible, if_pos
    (show CompactSpace Y ∧ QuasiSeparatedSpace Y from ⟨inferInstance, inferInstance⟩)] using hM

private theorem base_change_qcqs
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] (A : Type u) [CommRing A]
    (XU : Scheme.{u}) (v : Spec (.of A) ⟶ Y) [IsOpenImmersion v]
    (a : XU ⟶ X) (fU : XU ⟶ Spec (.of A)) (wf : IsPullback a fU f v) :
    IsProper fU ∧ CompactSpace XU ∧ QuasiSeparatedSpace XU ∧
      CompactSpace X ∧ QuasiSeparatedSpace X := by
  have : IsProper fU := MorphismProperty.of_isPullback wf inferInstance
  have : CompactSpace XU := QuasiCompact.compactSpace_of_compactSpace fU
  have : QuasiSeparatedSpace XU := quasiSeparatedSpace_of_quasiSeparated fU
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem affine_local_proper_constructible_exchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    {X Y C : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] (c : C ⟶ Y) [IsClosedImmersion c]
    [QuasiCompact (Scheme.Opens.ι (X := Y)
      ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩)]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M)
    (A : Type u) [CommRing A] (I : Ideal A)
    (XU XZ : Scheme.{u}) (v : Spec (.of A) ⟶ Y) [IsOpenImmersion v]
    (a : XU ⟶ X) (fU : XU ⟶ Spec (.of A))
    (b : Spec (.of (A ⧸ I)) ⟶ C)
    (h : XZ ⟶ XU) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (wf : IsPullback a fU f v)
    (_wc : IsPullback b (ClosedTestDerivedExchangeModel.closedMap A I) c v)
    (w : IsPullback h fZ fU (ClosedTestDerivedExchangeModel.closedMap A I)) :
    IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ a).obj M))) := by
  obtain ⟨hfU, hXU, hqsXU, hX, hqsX⟩ := base_change_qcqs f A XU v a fU wf
  have := hfU
  have := hXU
  have := hqsXU
  have := hX
  have := hqsX
  have hMU := constructible_pullback_on_qcqs Λ a M hM
  exact pulled_exchange Λ ℓ hΛ A I fU h fZ w a M hMU

/-- Proper closed exchange on a constructible module sheaf in degree zero.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, paragraph (2),
together with the closed-test argument of
lem-sfb-qcqs-proper-constructible-closed-base-change, the degree-zero closed-test calculation
(blueprint: lem-sfb-proper-constructible-closed-exchange-heart).

Proof: Work over an affine open U of Y and write its closed subscheme as Spec(A/I).
The closed lifted-test cover supplies w-contractible V and W=Spec(B), with
V=Spec(B/IB). The ideal IB is contained in Jac(B), and V and W have the same
reduced closed-point subscheme Spec(B/Jac(B)); this also holds for the zero ring.
Restriction of M to X_U and closed inverse image preserve finite constant models:
pull back the constructible stratification and its pro-etale trivializing covers,
and apply the scalar-matrix inverse-image comparison. Hence the two restricted
sheaves belong to the weak Serre coproduct classes in the proper closed-fibre
rigidity theorem. Apply that theorem to X_U -> U at W and to X_Z -> Z at V.
Both canonical restriction maps to the same closed-point fibre are isomorphisms.
Functoriality of the inverse-image unit on sections identifies the first with the
restriction from X_W to X_V followed by the second, including the canonical
pullback-composition identifications. Cancel the second isomorphism. The nonaffine
closed-test exchange identification now makes the evaluated actual ambient mate
invertible. Conservative derived evaluation on lifted tests makes the affine-local
mate invertible. The localization comparisons preserve adjunction units, counits
and the square compositor; thus these affine-local mates are the restrictions of
the original mate. Conservativity along the inverse-image affine cover of C gives
the asserted isomorphism. The argument uses the given coefficient topology throughout
and applies to all six families, without coefficient scalar extension. -/
theorem proper_constructible_closed_exchange_heart
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    {X Y C : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] (c : C ⟶ Y) [IsClosedImmersion c]
    [QuasiCompact (Scheme.Opens.ι (X := Y)
      ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩)]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsIso ((condensedAmbientExchange Λ
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  apply condensed_closed_exchange_affine_descent Λ f c M
  intro A instA I XU XZ v instV a fU b h fZ wf wc w
  exact affine_local_proper_constructible_exchange Λ ℓ hΛ f c M hM A I XU XZ v a fU b h fZ wf wc w

end AlgebraicGeometry.ProEtale.CondensedRing
