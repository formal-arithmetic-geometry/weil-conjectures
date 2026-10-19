/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.CategoryTheory.Triangulated.LocalizingFunctor
import Sheaf.Paper.LocalizingClosureExistence
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.RationalRestrictionGlue
import all Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Rational geometric cohomology preservation

Source: det-existence-restriction.proof.md, rational and integral restriction bullets.
(blueprint: lem-sfb-adic-rational-constant-model-cohomology)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem hull_eq (X : Scheme.{u})
    (hc : (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ X) :
    localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X) =
      localizingClosureProEtale Λ X := by
  let S := constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _
  let D := DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  obtain ⟨sums, _, _, hbig, _, _, _, _⟩ := localizingClosure_exists Λ X S
  let : HasCoproducts.{u + 1} D := sums
  have bigToSmall : localizingClosureProEtale Λ X ≤
      localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X) := by
    obtain ⟨_, _, h, _⟩ := maps_localizingClosureProEtale Λ X
      (constantModelBoundedConstructible Λ X) (𝟭 D) (fun K hK P _ hP ↦ hP K (hc ▸ hK))
    exact h
  apply le_antisymm _ bigToSmall
  intro K hK
  let P := localizingClosureProEtale Λ X
  let : P.IsTriangulated := hbig.1
  let : P.IsClosedUnderIsomorphisms := hbig.2.1
  have bigSums (I : Type (u + 2)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro L ⟨F, hF⟩
    exact hbig.2.2 F inferInstance (fun i ↦ hF (.mk i))
  have smallSums (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    let := bigSums (ULift.{u + 2} I)
    exact ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence (P := P)
      (Discrete.equivalence Equiv.ulift)
  apply hK P ⟨hbig.1, hbig.2.1, ?_⟩
  · intro L hL Q _ hQ
    exact hQ L (hc.symm ▸ hL)
  · intro I F hF hL
    let := hF
    let := smallSums I
    exact P.prop_colimit F (fun i ↦ hL i.as)

private noncomputable def extensionByZeroIdIso (X : Scheme.{u}) :
    openImmersionLowerShriek Λ (𝟙 X) ≅ 𝟭 _ :=
  ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
    (upperStarId Λ X)).leftAdjointUniq Adjunction.id

private noncomputable def properIdentityCompactification
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : Compactification f :=
  Compactification.ofIsProper f

private noncomputable def properIdentityPushforwardIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriekOfCompactification Λ (properIdentityCompactification f) ≅
      R((f)_*⟦Λ⟧) :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso (extensionByZeroIdIso Λ X) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

private theorem field_coefficient_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} E) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} F)) := by
  let f : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let e : E ≃ₐ[ℚ_[ℓ]] f.fieldRange := f.equivFieldRange
  let : FiniteDimensional ℚ_[ℓ] f.fieldRange :=
    e.toLinearEquiv.finiteDimensional
  let F : PadicAlgCl.FiniteIntermediateField ℓ := ⟨f.fieldRange, inferInstance⟩
  let ec := e.toLinearEquiv.toContinuousLinearEquiv
  let es : Profinite.continuousMapRingSheaf.{u} E ≅
      Profinite.continuousMapRingSheaf.{u} F := by
    apply ObjectProperty.isoMk _
    refine NatIso.ofComponents (fun V ↦
      (ULift.ringEquiv.trans ((continuousMapRingEquiv e.toRingEquiv
        ec.continuous ec.symm.continuous V.unop).trans ULift.ringEquiv.symm)).toRingCatIso) ?_
    intro V V' a
    rfl
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso es
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ es.hom
  have : IsMonHom ea.inv := Sheaf.isMonHom_sheafCompose_map _ es.inv
  exact ⟨F, ⟨{ hom := ⟨ea.hom⟩
               inv := ⟨ea.inv⟩
               hom_inv_id := by apply Mon.Hom.ext; exact ea.hom_inv_id
               inv_hom_id := by apply Mon.Hom.ext; exact ea.inv_hom_id }⟩⟩

/-- The bounded finite-constant-model generators enter their ordinary localizing hull.
This is the defining intersection, with coproducts indexed in universe u+1. -/
theorem constantModel_le_localizingClosure (X : Scheme.{u}) :
    constantModelBoundedConstructible Λ X ≤
      localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X) := by
  intro K hK P _hP hSP
  exact hSP K hK

/-- The rational coefficient families: finite continuous extensions and the
finite-subextension-valued algebraic closure. The ring structure is indexed too. -/
inductive IsRationalEllAdicCoefficient (ℓ : ℕ) [Fact ℓ.Prime] :
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) → MonObj A → Prop
  | continuous (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] :
      IsRationalEllAdicCoefficient ℓ (Profinite.continuousMapRingObj E) inferInstance
  | algebraicClosure :
      IsRationalEllAdicCoefficient ℓ (Profinite.padicAlgClRingObj ℓ) inferInstance

/-- Rational geometric preservation on the ordinary finite-constant-model hull.
Source: det-existence-restriction.proof.md, rational bullet; sk-thm-restriction.
Proof: identify Dbc with Dctf for rational coefficients, using the same u+1 coproduct
universe. For a proper map use its identity compactification, whose compact-support
functor is derived pushforward. On finite affine charts factor the morphism through
a closed immersion followed by an affine-space projection. The local restriction
formula, rational affine-space calculation, and closed-adjoint support theorem show
constructibility there. Finite-open gluing gives constructibility globally. For
Qbar use its finite-subextension-valued coefficient, descending the finite charts
and matrices to a common finite extension. Uniqueness of the adjoint for this exact
left lift transports the answer to G. Empty schemes and zero complexes are included.
(blueprint: lem-sfb-adic-rational-constant-model-cohomology) -/
theorem ellAdic_rational_constantModel_rightAdjoint_homology_constructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left]
    (hΛ : IsRationalEllAdicCoefficient ℓ Λ inferInstance)
    (h : ∀ K, localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Z.left) K →
      localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Y.left)
        ((R((g.left)_*⟦Λ⟧)).obj K))
    (G : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Y.left)).FullSubcategory ⥤
      (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Z.left)).FullSubcategory)
    (adj : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Y.left)).lift
      ((localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Z.left)).ι ⋙ R((g.left)_*⟦Λ⟧))
      (fun K ↦ h K.obj K.property) ⊣ G)
    (K : (constantModelBoundedConstructible Λ Y.left).FullSubcategory) :
    ∀ n : ℤ, IsConstantModelConstructible Λ Z.left
      ((DerivedCategory.homologyFunctor _ n).obj
        (G.obj ((ObjectProperty.ιOfLE (constantModel_le_localizingClosure Λ Y.left)).obj
          K)).obj) := by
  have coeff : (∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj F))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    cases hΛ with
    | continuous E => exact Or.inl (field_coefficient_normalization ℓ E)
    | algebraicClosure => exact Or.inr ⟨Iso.refl _⟩
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : QuasiSeparatedSpace Z.left := inferInstance
  have : QuasiSeparatedSpace Y.left := inferInstance
  have comparison (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
      (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ X := by
    apply (localizingClosure_ctf_equals_bc ℓ X Λ ?_).1.2.2.1
    rcases coeff with ⟨F, hF⟩ | hF
    · exact Or.inr (Or.inr (Or.inl ⟨F, Or.inr hF⟩))
    · exact Or.inr (Or.inr (Or.inr hF))
  have eZ := hull_eq Λ Z.left (comparison Z.left)
  have eY := hull_eq Λ Y.left (comparison Y.left)
  let CZ := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Z.left)
  let CY := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Y.left)
  let iZ := ObjectProperty.ιOfLE (le_of_eq eZ.symm)
  let iY := ObjectProperty.ιOfLE (le_of_eq eY.symm)
  let jZ := ObjectProperty.ιOfLE (le_of_eq eZ)
  let Gc := iY ⋙ G ⋙ jZ
  let c : Compactification.BoundaryCompactification g.left :=
    ⟨⟨properIdentityCompactification g.left, by
      change QuasiCompact (𝟙 Z.left)
      infer_instance⟩⟩
  have hs : ∀ L, localizingClosureProEtale Λ Z.left L →
      localizingClosureProEtale Λ Y.left ((R((g.left)_*⟦Λ⟧)).obj L) := by
    intro L hL
    exact le_of_eq eY _ (h L (le_of_eq eZ.symm _ hL))
  have hd : ∀ L, localizingClosureProEtale Λ Z.left L →
      localizingClosureProEtale Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj L) := by
    intro L hL
    obtain ⟨_, _, _, hp, _, _, _, _⟩ := localizingClosure_exists Λ Y.left
      (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
    let : (localizingClosureProEtale Λ Y.left).IsClosedUnderIsomorphisms := hp.2.1
    exact ObjectProperty.prop_of_iso _ ((properIdentityPushforwardIso Λ g.left).app L).symm
      (hs L hL)
  let Fc := localizingLowerShriek Λ c.obj.obj hd
  let Fs := CY.lift (CZ.ι ⋙ R((g.left)_*⟦Λ⟧)) (fun L ↦ h L.obj L.property)
  have eF : iZ ⋙ Fs ≅ Fc ⋙ iY :=
    NatIso.ofComponents (fun L ↦
      ObjectProperty.isoMk _ ((properIdentityPushforwardIso Λ g.left).app L.obj).symm)
      (fun f ↦ by ext; exact ((properIdentityPushforwardIso Λ g.left).inv.naturality f.hom))
  have eG : iY ⋙ G ≅ Gc ⋙ iZ :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by simp; rfl)
  have adjc : Fc ⊣ Gc := adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _) eF eG
  obtain ⟨F, hF⟩ : ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj F)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases coeff with ⟨F, hF⟩ | hF
    · exact ⟨F, Or.inl hF⟩
    · exact ⟨⟨⊥, inferInstance⟩, Or.inr hF⟩
  have hF' : Nonempty (Mon.mk Λ ≅ Mon.mk
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (Profinite.padicSubfieldCondensedRing ℓ F.val))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    exact hF
  have : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : QuasiCompact (Z.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Z.hom)
  have : IsSeparated (Z.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Z.hom)
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  obtain ⟨_, _, _, hGc, _⟩ := (rationalRestrictionGlue.{u, u} Λ ℓ F.val hF'
    k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
    g.left c hd Gc adjc).2
  have hK : localizingClosureProEtale Λ Y.left K.obj :=
    le_of_eq eY _ (constantModel_le_localizingClosure Λ Y.left _ K.property)
  exact (hGc ⟨K.obj, hK⟩ K.property).2

end AlgebraicGeometry.ProEtale.CondensedRing
