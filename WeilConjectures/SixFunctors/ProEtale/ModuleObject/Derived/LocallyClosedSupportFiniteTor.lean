/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import all WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleDirectImage
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Finite-Tor constructibility of locally closed support -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem support_pullback_ctf {T Y : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : T ⟶ Y) (K : DerivedCategory (supportModules Λ Y))
    (hK : constantModelBoundedConstructible Λ Y K ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible Λ T ((supportPullback Λ f).mapDerivedCategory.obj K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((supportPullback Λ f).mapDerivedCategory.obj K) := by
  have : (constantModelBoundedConstructible Λ T).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ T).2.1
  let e := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ f) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm
  exact ObjectProperty.prop_of_iso
    (constantModelBoundedConstructible Λ T ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
    (e.symm.app K)
    ⟨pullback_bounded_constructible Λ f (fun M hM ↦ pullback_constructible Λ f M hM)
      K hK.1, pullback_tor Λ f K hK.2⟩

/-- Any ambient right adjoint to locally closed extension preserves constructible finite-Tor
objects. Source: internal-Hom stability proof, support-triangle membership argument.
Choose the open complement v of the closed immersion. Pullback and ordinary direct image
preserve Dctf. The support triangle and triangulated closure imply i_* RΓ_Z L is Dctf.
Pull back along i and use the invertible closed counit to deduce that RΓ_Z L is Dctf.
Open pullback then gives j^* RΓ_Z L in Dctf. The composite support adjunction identifies
this object with the value of any given right adjoint, by uniqueness of right adjoints.
(blueprint: lem-sfb-locally-closed-support-finite-tor).
-/
theorem locallyClosed_support_finiteTor
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X S Z : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (j : S ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (R : DerivedCategory (supportModules Λ X) ⥤ DerivedCategory (supportModules Λ S))
    (adj : ((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
      (lowerStar Λ i).rightDerivedFunctor) ⊣ R)
    (L : DerivedCategory (supportModules Λ X))
    (hL : constantModelBoundedConstructible Λ X L ∧
      _root_.DerivedCategory.finiteTorAmplitude _ L) :
    constantModelBoundedConstructible Λ S (R.obj L) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ (R.obj L) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : Z.Over (Spec (.of k)) := ⟨i ≫ (X ↘ Spec (.of k))⟩
  let : LocallyOfFiniteType (Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (i ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : QuasiCompact (Z ↘ Spec (.of k)) := by
    change QuasiCompact (i ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : IsSeparated (Z ↘ Spec (.of k)) := by
    change IsSeparated (i ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace j
  let : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated j
  let V : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U : Scheme.{u} := V
  let v : U ⟶ X := V.ι
  have hiv : Set.range i.base = (Set.range v.base)ᶜ := by
    change Set.range i.base = (Set.range V.ι.base)ᶜ
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let := closedSupport_lowerStarExact Λ i v hiv
  let : U.Over (Spec (.of k)) := ⟨v ≫ (X ↘ Spec (.of k))⟩
  let : v.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (U ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (v ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : QuasiCompact (U ↘ Spec (.of k)) := by
    change QuasiCompact (v ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : IsSeparated (U ↘ Spec (.of k)) := by
    change IsSeparated (v ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace v
  let : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated v
  let Γ := (closedSupport Λ i v).rightDerivedFunctor
  let I := (lowerStar Λ i).mapDerivedCategory
  let PX := constantModelBoundedConstructible Λ X ⊓
    _root_.DerivedCategory.finiteTorAmplitude (supportModules Λ X)
  have hsmall := CategoryTheory.brownHypotheses_admissible_small ℓ Λ hΛ X
  let : PX.IsTriangulated := hsmall.1
  let : PX.IsClosedUnderIsomorphisms := hsmall.2.1
  have hv := support_pullback_ctf Λ v L hL
  have hvv := constructibleFiniteTor_rightDerivedLowerStar_of_admissible ℓ k Λ hΛ v _ hv
  obtain ⟨δ, hδ⟩ := closedSupport_triangle Λ i v hiv
  have hI : PX (I.obj (Γ.obj L)) :=
    PX.ext_of_isTriangulatedClosed₁ _ (hδ L) hL hvv
  have hi := support_pullback_ctf Λ i (I.obj (Γ.obj L)) hI
  have hc := (condensedSupportDerivedLocalization Λ i v hiv).2.1 (Γ.obj L)
  let := hc
  have hΓ : constantModelBoundedConstructible Λ Z (Γ.obj L) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ (Γ.obj L) := by
    have : (constantModelBoundedConstructible Λ Z).IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined Λ Z).2.1
    exact ObjectProperty.prop_of_iso
      (constantModelBoundedConstructible Λ Z ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      (asIso ((closedPullbackDerivedAdjunction Λ i).counit.app (Γ.obj L))) hi
  have hj := support_pullback_ctf Λ j (Γ.obj L) hΓ
  let R₀ := Γ ⋙ (supportPullback Λ j).mapDerivedCategory
  let adj₀ : ((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
      (lowerStar Λ i).rightDerivedFunctor) ⊣ R₀ :=
    ((openSupportDerivedAdjunction Λ j).comp
      (closedSupportDerivedAdjunction Λ i v hiv)).ofNatIsoLeft
        (Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
          (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.symm)
  have : (constantModelBoundedConstructible Λ S).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ S).2.1
  exact ObjectProperty.prop_of_iso
    (constantModelBoundedConstructible Λ S ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
    ((adj₀.rightAdjointUniq adj).app L) hj
end AlgebraicGeometry.ProEtale.CondensedRing
