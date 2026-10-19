/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.IntegralModelsDefinitions
import Sheaf.Paper.IntegralModelsCoefficientPresentation
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-! # Restriction on embedded complete coefficients

Source: blueprint main-20261015, sk-lem-integral-models, proof step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (q : R ⟶ S)
    {M N : ConstantCompletion.D R} (e : M ≅ N)
    (h : ConstantCompletion.IsComplete q M) : ConstantCompletion.IsComplete q N := by
  let : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
  let := fun U : C ↦ HasDerivedCategory.standard
    (ConstantCompletion.Mod (R.over U))
  intro U f hf
  exact (h U f hf).of_iso ((derivedInternalHom (J.over U) (R.over U)).mapIso
    ((Iso.refl _).prod ((ringedDerivedRestriction R U).mapIso e))).symm

private theorem transport_complete_equivalence
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (P' : ObjectProperty C') (Q' : ObjectProperty D')
    [P'.IsClosedUnderIsomorphisms] [Q'.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) (F' : C' ⥤ D')
    (eC : C ≌ C') (eD : D ≌ D')
    (hC : P'.inverseImage eC.functor = P) (hD : Q'.inverseImage eD.functor = Q)
    (α : eC.functor ⋙ F' ≅ F ⋙ eD.functor)
    (e : P'.FullSubcategory ≌ Q'.FullSubcategory)
    (β : e.functor ⋙ Q'.ι ≅ P'.ι ⋙ F') :
    ∃ t : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (t.functor ⋙ Q.ι ≅ P.ι ⋙ F) := by
  let a := eC.congrFullSubcategory hC
  let b := eD.congrFullSubcategory hD
  let t := (a.trans e).trans b.symm
  refine ⟨t, ⟨?_⟩⟩
  change a.functor ⋙ e.functor ⋙ b.inverse ⋙ Q.ι ≅ P.ι ⋙ F
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft a.functor β) eD.inverse ≪≫
    (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft P.ι
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight α eD.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft F eD.unitIso.symm ≪≫ Functor.rightUnitor F)

/-- Restriction along the actual embedded constant-to-continuous coefficient map is an
 equivalence on complete objects. The functor comparison records this specific restriction.

Source: blueprint main-20261015, sk-lem-integral-models, proof step 2; Stacks 099I, 099L.
(blueprint: lem-sfb-embedded-integral-complete-restriction).

Proof: the ambient coefficient-presentation theorem supplies equivalences to the
canonical constant ring and its quotient-tower limit, preserves both completeness
predicates, and identifies scalar restriction. The lifted integer ring is Noetherian
because the original integer ring is a principal ideal ring. Apply
ConstantCompletion.equivalence to its lifted uniformizer ideal. Local completeness is
invariant under isomorphisms: apply slice restriction and derived internal Hom to the
isomorphism in each vanishing test. Restrict both ambient equivalences using
Equivalence.congrFullSubcategory and compose with the canonical completion equivalence.
Whisker its specified functor isomorphism with the ambient comparisons, reassociate,
and cancel the constant-coefficient equivalence by its unit. This gives exactly the
specified ambient scalar restriction. Zero objects and empty schemes are included. -/
theorem embeddedIntegral_complete_restriction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    ∃ e : ObjectProperty.FullSubcategory (IntegralModelsEmbedded.completedComplete ℓ E π X) ≌
        ObjectProperty.FullSubcategory (IntegralModelsEmbedded.constantComplete ℓ E π X),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IntegralModelsEmbedded.constantComplete ℓ E π X) ≅
        ObjectProperty.ι (IntegralModelsEmbedded.completedComplete ℓ E π X) ⋙
          IntegralModelsEmbedded.restriction ℓ E X)  := by
  let A := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
  let I : Ideal A := Ideal.map ULift.ringEquiv.symm.toRingHom (Ideal.span {π})
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  have : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ ULift.ringEquiv.symm
  obtain ⟨eB, eR, hB, hR, ⟨α⟩⟩ :=
    embeddedIntegral_coefficient_presentation ℓ E π hπ X
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0)) :=
    ⟨fun e h ↦ complete_of_iso _ e h⟩
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (ConstantCompletion.IsComplete (ConstantCompletion.quotient J A I 0)) :=
    ⟨fun e h ↦ complete_of_iso _ e h⟩
  obtain ⟨e, ⟨β⟩⟩ := ConstantCompletion.equivalence J A I
  exact transport_complete_equivalence
    (IntegralModelsEmbedded.completedComplete ℓ E π X)
    (IntegralModelsEmbedded.constantComplete ℓ E π X)
    (ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0))
    (ConstantCompletion.IsComplete (ConstantCompletion.quotient J A I 0))
    (IntegralModelsEmbedded.restriction ℓ E X)
    (ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)) eB eR
    (funext fun K ↦ propext (hB K).symm)
    (funext fun L ↦ propext (hR L).symm) α e β

end AlgebraicGeometry.ProEtale
