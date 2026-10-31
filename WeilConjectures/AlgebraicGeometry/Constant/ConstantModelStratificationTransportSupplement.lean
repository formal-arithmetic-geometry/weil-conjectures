/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport

/-!
# Transport of finite constant-model stratification witnesses

Source: blueprint main-20261015, sec-six-functors/sk-lem-sf-open-ctf/
sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

The adapters keep all partition and immersion data. The transport statements fix the
cover and scalar modules before changing the module being modelled. Constructibility
and bounded constructible cohomology use the finite constant-model convention.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

/-- The two descriptions of a stratification with a property are equivalent, and the
adapters are inverse. Their definitions retain number, subsets, schemes and maps literally.
Source: sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

Proof: forget only the constructibility fields and keep them as a separate family;
conversely adjoin that family. The arguments of P do not change. Record extensionality
and proof irrelevance identify both repackings with the original record (node step 1). -/
theorem constructibleStratification_iff_locallyClosed (T : Scheme.{u})
    (P : ∀ S : Scheme.{u}, (S ⟶ T) → Prop) :
    ((∃ S : Stratification T, ∀ a : Fin S.n, P (S.domain a) (S.immersion a)) ↔
      ∃ S : FiniteLocallyClosedStratification T,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ a : Fin S.n, P (S.domain a) (S.immersion a)) ∧
    (∀ S : Stratification T,
      S.toFiniteLocallyClosed.withConstructibleStrata S.isConstructible_stratum = S) ∧
    (∀ (S : FiniteLocallyClosedStratification T)
      (c : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)),
      (S.withConstructibleStrata c).toFiniteLocallyClosed = S) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨S, hS⟩
    exact ⟨S.toFiniteLocallyClosed, S.isConstructible_stratum, hS⟩
  · rintro ⟨S, c, hS⟩
    exact ⟨S.withConstructibleStrata c, hS⟩
  · intro S
    rfl
  · intro S c
    rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Transport a local-model witness while retaining its specified cover and scalar modules.
Source: sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

Proof: for every cover member compose the old model isomorphism with the inverse
of the pullback of e. Its inverse is the old inverse followed by the pullback of e;
the functor laws and inverse identities verify both composites. Retain the cover,
scalar modules and finite-presentation proofs (node step 2). -/
theorem finiteConstantModelsOnCover_of_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    (P : 𝒰.I₀ → Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : ∀ i : 𝒰.I₀, Mod.IsFinitelyPresented (scalarRingObj Λ) (P i))
    (hM : ∀ i : 𝒰.I₀, Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
      (finiteConstantScalarExtension Λ (𝒰.X i)).obj (P i))) :
    ∀ i : 𝒰.I₀, Mod.IsFinitelyPresented (scalarRingObj Λ) (P i) ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj N ≅
        (finiteConstantScalarExtension Λ (𝒰.X i)).obj (P i)) := by
  intro i
  obtain ⟨eM⟩ := hM i
  exact ⟨hP i, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eM⟩⟩

/-- The defining condensed-presentation witnesses also retain their covers and models.
Source: sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

Proof: apply the same pullback-isomorphism construction of node step 2 to each
specified presentation on the point. Only the model isomorphism changes; its inverse
identities follow from functoriality. The finite-presentation proofs are retained. -/
theorem finiteConstantPointModelsOnCover_of_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    (P : 𝒰.I₀ → Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : ∀ i : 𝒰.I₀, Mod.IsFinitelyPresented Λ (P i))
    (hM : ∀ i : 𝒰.I₀, Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
      ((upperStarFromPoint (𝒰.X i)).mapMod Λ).obj (P i))) :
    ∀ i : 𝒰.I₀, Mod.IsFinitelyPresented Λ (P i) ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj N ≅
        ((upperStarFromPoint (𝒰.X i)).mapMod Λ).obj (P i)) := by
  intro i
  obtain ⟨eM⟩ := hM i
  exact ⟨hP i, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eM⟩⟩

/-- Transport stratified scalar models without altering any strata, covers or modules.
Source: sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

Proof: retain S including its constructibility fields. Pull e back along each stratum
immersion, then apply the fixed-cover construction of step 2 to its model. This changes
only the isomorphisms, giving the witnesses required by node step 3. -/
theorem stratifiedConstantModels_of_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (S : Scheme.Stratification T)
    (𝒰 : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (P : ∀ a : Fin S.n, (𝒰 a).I₀ → Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i))
    (hM : ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      Nonempty ((CondensedRing.upperStar Λ ((𝒰 a).f i)).obj
        ((CondensedRing.upperStar Λ (S.immersion a)).obj M) ≅
          (finiteConstantScalarExtension Λ ((𝒰 a).X i)).obj (P a i))) :
    ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i) ∧
      Nonempty ((CondensedRing.upperStar Λ ((𝒰 a).f i)).obj
        ((CondensedRing.upperStar Λ (S.immersion a)).obj N) ≅
          (finiteConstantScalarExtension Λ ((𝒰 a).X i)).obj (P a i)) := by
  intro a
  exact finiteConstantModelsOnCover_of_iso Λ
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (𝒰 a) (P a) (hP a) (hM a)

/-- The same witness transport is available separately on every affine open.
Source: sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

Proof: restrict e and its inverse to the chosen affine open, then to its specified
strata. Apply the fixed-cover transport on each stratum. The functor laws show that
these restricted maps are inverse. Do this separately on each affine open; no common
finite stratification of a non-qcqs scheme is asserted (node step 4). -/
theorem affineStratifiedConstantModels_of_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (U : T.Opens) (hU : IsAffineOpen U)
    (S : Scheme.Stratification U.toScheme)
    (𝒰 : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (P : ∀ a : Fin S.n, (𝒰 a).I₀ → Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i))
    (hM : ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      Nonempty ((CondensedRing.upperStar Λ ((𝒰 a).f i)).obj
        ((CondensedRing.upperStar Λ (S.immersion a)).obj
          ((CondensedRing.upperStar Λ U.ι).obj M)) ≅
            (finiteConstantScalarExtension Λ ((𝒰 a).X i)).obj (P a i))) :
    ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i) ∧
      Nonempty ((CondensedRing.upperStar Λ ((𝒰 a).f i)).obj
        ((CondensedRing.upperStar Λ (S.immersion a)).obj
          ((CondensedRing.upperStar Λ U.ι).obj N)) ≅
            (finiteConstantScalarExtension Λ ((𝒰 a).X i)).obj (P a i)) := by
  cases hU
  exact stratifiedConstantModels_of_iso Λ
    ((CondensedRing.upperStar Λ U.ι).mapIso e) S 𝒰 P hP hM

/-- Isomorphic cohomology models give constructible cohomology and preserve its interval.
Source: sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

Proof: apply steps 3--4 to each e_q to obtain constructible H^q with the same witnesses.
Outside [r,s], transport the zero-object property of M_q through e_q: composition with
an isomorphism reduces uniqueness of maps to uniqueness for the zero object. These
vanishings give the bounded t-structure conditions. Together with constructible H^q,
this is exactly constantModelBoundedConstructible, using the same r and s (node step 5).
No tensor or Tor-amplitude condition enters. -/
theorem constantModelCohomology_transport (T : Scheme.{u})
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (M : ℤ → Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (e : ∀ q : ℤ, M q ≅ (DerivedCategory.homologyFunctor _ q).obj L)
    (hM : ∀ q : ℤ, IsConstantModelConstructible Λ T (M q)) :
    (∀ q : ℤ, IsConstantModelConstructible Λ T
      ((DerivedCategory.homologyFunctor _ q).obj L)) ∧
    (∀ r s : ℤ, (∀ q : ℤ, q < r ∨ s < q → IsZero (M q)) →
      constantModelBoundedConstructible Λ T L ∧
      ∀ q : ℤ, q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) := by
  have hcons : ∀ q : ℤ, IsConstantModelConstructible Λ T
      ((DerivedCategory.homologyFunctor _ q).obj L) :=
    fun q ↦ constantModelConstructible_transport Λ (e q) (hM q)
  refine ⟨hcons, fun r s hzero ↦ ?_⟩
  have hvanish : ∀ q : ℤ, q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L) :=
    fun q hq ↦ (hzero q hq).of_iso (e q).symm
  refine ⟨⟨⟨⟨r, ?_⟩, ⟨s, ?_⟩⟩, hcons⟩, hvanish⟩
  · exact (DerivedCategory.isGE_iff L r).mpr fun q hq ↦ hvanish q (Or.inl hq)
  · exact (DerivedCategory.isLE_iff L s).mpr fun q hq ↦ hvanish q (Or.inr hq)

end AlgebraicGeometry.ProEtale
