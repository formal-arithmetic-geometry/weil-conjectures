/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.AlgebraicGeometry.ProjTwistSectionBasicOpen
import WeilConjectures.TraceFormula.ProjCommonDegreeTwistInvertible
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.NonvanishingLocusRestrict
import all WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Sufficiently divisible twists on a quasi-compact Proj open

Source: Stacks Project, Constructions, Tag 01MW and Properties, Tag 01Q2
(blueprint: lem-trf-proj-qc-open-twist-ample).

The statement records the common positive degree whose restricted Proj twists are
invertible and ample, together with the canonical tensor-power identification.

This stage-2 statement record was revalidated by group Q16 on 2026-10-18.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The pure tensor of a tuple of local sections of a restricted Proj twist.
The empty tuple is the section `1` of the tensor unit; a nonempty tuple tensors
its first section with the tensor of its tail. This is the pure tensor used to
specify the canonical multiplication map in Stacks, Constructions, Equation
(multiply) and Tag 01MW (blueprint: lem-trf-proj-qc-open-twist-ample). -/
def Proj.twistTensorSection
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {U : Scheme.{u}} (j : U ⟶ Proj 𝒜) [IsOpenImmersion j]
    (e : ℕ) (V : U.Opens) :
    ∀ k : ℕ, (Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict j, V)) →
      Γ(((Proj.twist 𝒜 (Int.ofNat e)).restrict j).tensorPow k, V)
  | 0, _ => Scheme.Modules.unitSectionsEquiv V 1
  | k + 1, s => Scheme.Modules.tmulSection (s 0)
      (Proj.twistTensorSection 𝒜 j e V k (Fin.tail s))

set_option backward.isDefEq.respectTransparency false in
private theorem finite_positive_cover
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (V : (Proj 𝒜).Opens) [CompactSpace V.toScheme] :
    ∃ (I : Type u) (_ : Fintype I) (f : I → A) (d : I → ℕ),
      (∀ i, f i ∈ 𝒜 (d i)) ∧ (∀ i, 0 < d i) ∧
      V ≤ ⨆ i, Proj.basicOpen 𝒜 (f i) := by
  classical
  have : CompactSpace V := inferInstanceAs (CompactSpace V.toScheme)
  have hp (x : V) : ∃ (f : A) (d : ℕ),
      0 < d ∧ f ∈ 𝒜 d ∧ x.val ∈ Proj.basicOpen 𝒜 f := by
    obtain ⟨O, ⟨f, d, hd, hf, rfl⟩, hx, _⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.standardOpenProperties.{u, u, u} 𝒜).1 x.prop
    exact ⟨f, d, hd, hf, hx⟩
  choose f d hd hf hx using hp
  obtain ⟨t, ht⟩ := (@isCompact_univ V _ ‹CompactSpace V›).elim_finite_subcover
    (fun x : V ↦ {y : V | y.val ∈ Proj.basicOpen 𝒜 (f x)})
    (fun x ↦ (Proj.basicOpen 𝒜 (f x)).isOpen.preimage continuous_subtype_val)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨t, inferInstance, (fun i ↦ f i.val), (fun i ↦ d i.val),
    (fun i ↦ hf i.val), (fun i ↦ hd i.val), ?_⟩
  intro x hxV
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (⟨x, hxV⟩ : V)))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

set_option backward.isDefEq.respectTransparency false in
private theorem ample_of_twist_basis
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (V : (Proj 𝒜).Opens) [CompactSpace V.toScheme]
    (e : ℕ) (L : V.toScheme.Modules) [L.IsInvertible]
    (hB : TopologicalSpace.IsTopologicalBasis
      {S : Set V.toScheme | S ∈ Proj.twistSectionLoci 𝒜 e V ∧
        ∃ O : V.toScheme.Opens, (O : Set V.toScheme) = S ∧ IsAffineOpen O})
    (hμ : ∀ n : ℕ, 0 < n →
      Nonempty (L.tensorPow n ≅ (Proj.twist 𝒜 (Int.ofNat (e * n))).restrict V.ι)) :
    Scheme.Modules.IsAmple V.toScheme L := by
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨S, ⟨hS, O, hO, hAff⟩, hxS, _⟩ :=
    hB.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨n, hn, f, hf, hSf⟩ := hS
  obtain ⟨a⟩ := hμ n hn
  have hdeg : 0 + ((n * e : ℕ) : ℤ) = Int.ofNat (e * n) := by
    simp [Nat.mul_comm]
  let b := eqToIso (congrArg (fun q ↦ (Proj.twist 𝒜 q).restrict V.ι) hdeg)
  let s := b.hom.app ⊤ (Proj.twistSectionOnOpen 𝒜 V hf)
  let t := a.inv.app ⊤ s
  have ht : Scheme.Modules.nonvanishingLocus (L.tensorPow n) t = S := by
    exact (Scheme.Modules.nonvanishingLocus_iso a.symm s).trans
      ((Scheme.Modules.nonvanishingLocus_iso b
        (Proj.twistSectionOnOpen 𝒜 V hf)).trans hSf.symm)
  refine ⟨n, hn, t, O, ?_, hAff, ?_⟩
  · exact (Set.ext_iff.mp hO x).mpr hxS
  · intro y
    change y ∈ O ↔ y ∈ Scheme.Modules.nonvanishingLocus (L.tensorPow n) t
    rw [ht]
    exact Set.ext_iff.mp hO y

set_option backward.isDefEq.respectTransparency false in
private theorem common_degree_on_open
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (V : (Proj 𝒜).Opens) [CompactSpace V.toScheme] :
    ∃ e : ℕ, 0 < e ∧
      ∀ k : ℕ, 0 < k →
        ∃ hL : ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict V.ι).IsInvertible,
          @Scheme.Modules.IsAmple V.toScheme
            ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict V.ι) hL ∧
          ∃ μ : ((Proj.twist 𝒜 (Int.ofNat e)).restrict V.ι).tensorPow k ⟶
              (Proj.twist 𝒜 (Int.ofNat (e * k))).restrict V.ι,
            IsIso μ ∧
            ∀ (Q : V.toScheme.Opens)
              (s : Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict V.ι, Q))
              (x : V.ι ''ᵁ Q),
              (((Proj.twist 𝒜 (Int.ofNat (e * k))).restrictAppIso V.ι Q).hom
                (μ.app Q (Proj.twistTensorSection 𝒜 V.ι e Q k s))).val x =
              ∏ i : Fin k,
                ((((Proj.twist 𝒜 (Int.ofNat e)).restrictAppIso V.ι Q).hom (s i)).val x :
                  Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) := by
  classical
  obtain ⟨I, _, f, d, hf, hd, hcover⟩ := finite_positive_cover 𝒜 V
  let e := ∏ i, d i
  have he : 0 < e := Finset.prod_pos (fun i _ ↦ hd i)
  have hdiv : ∀ i, d i ∣ e := fun i ↦ Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  let W := ⨆ (α : ℕ) (β : ℕ) (a : 𝒜 α) (b : 𝒜 β) (_ : α = β + e),
    Proj.basicOpen 𝒜 ((a : A) * (b : A))
  obtain ⟨hVW, _, _, hinv, μ, hμ, hzero, hsucc⟩ :=
    Proj.commonDegreeTwistInvertible 𝒜 V I f d hf hd hcover e he hdiv W rfl
  have hL : ((Proj.twist 𝒜 (Int.ofNat e)).restrict V.ι).IsInvertible := by
    simpa using hinv 1 Nat.one_pos
  have hample : Scheme.Modules.IsAmple V.toScheme
      ((Proj.twist 𝒜 (Int.ofNat e)).restrict V.ι) :=
    ample_of_twist_basis 𝒜 V e _ (Proj.twistSectionBasicOpen 𝒜 e he W rfl V hVW).2.2
      (fun n hn ↦ ⟨@asIso _ _ _ _ (μ n) (hμ n hn)⟩)
  have hprod (k : ℕ) (Q : V.toScheme.Opens)
      (s : Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict V.ι, Q))
      (x : V.ι ''ᵁ Q) :
      (((Proj.twist 𝒜 (Int.ofNat (e * k))).restrictAppIso V.ι Q).hom
        ((μ k).app Q (Proj.twistTensorSection 𝒜 V.ι e Q k s))).val x =
      ∏ i : Fin k,
        ((((Proj.twist 𝒜 (Int.ofNat e)).restrictAppIso V.ι Q).hom (s i)).val x :
          Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) := by
    induction k with
    | zero => simpa only [Proj.twistTensorSection, Fin.prod_univ_zero] using hzero Q x
    | succ k ih =>
      rw [Proj.twistTensorSection, hsucc, ih, Fin.prod_univ_succ]
      rfl
  refine ⟨e, he, fun k hk ↦ ⟨hinv k hk, ?_, μ k, hμ k hk, hprod k⟩⟩
  have : ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict V.ι).IsInvertible := hinv k hk
  have : IsIso (μ k) := hμ k hk
  have : (((Proj.twist 𝒜 (Int.ofNat e)).restrict V.ι).tensorPow k).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso (asIso (μ k)).symm
  exact (Scheme.Modules.isAmple_iff_of_iso (asIso (μ k))).mp
    (Scheme.Modules.isAmple_positive_tensorPow _ hample k hk)

set_option backward.isDefEq.respectTransparency false in
private def tensorPowerIso {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N) :
    ∀ k : ℕ, M.tensorPow k ≅ N.tensorPow k
  | 0 => Iso.refl _
  | k + 1 => MonoidalCategory.tensorIso a (tensorPowerIso a k)

set_option backward.isDefEq.respectTransparency false in
private theorem compTwistIso_value
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X Y : Scheme.{u}} (i : Y ⟶ Proj 𝒜) (h : X ⟶ Y) (j : X ⟶ Proj 𝒜)
    [IsOpenImmersion i] [IsOpenImmersion h] [IsOpenImmersion j] (hfac : h ≫ i = j)
    (q : ℤ) (Q : X.Opens) (s : Γ((Proj.twist 𝒜 q).restrict j, Q))
    (x : i ''ᵁ (h ''ᵁ Q)) :
    (((Scheme.Modules.restrictCompIso (Proj.twist 𝒜 q) i h j hfac).hom.app Q s).val x :
      Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) =
    (s.val ⟨x.val, by
      obtain ⟨y, ⟨z, hz, rfl⟩, hxy⟩ := x.prop
      exact ⟨z, hz, (congrArg (fun f : X ⟶ Proj 𝒜 ↦ f z) hfac.symm).trans hxy⟩⟩ :
        Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) := by
  simp only [Scheme.Modules.restrictCompIso, Iso.trans_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rfl

private def tensorSection {X : Scheme.{u}} (M : X.Modules) (Q : X.Opens) :
    ∀ k : ℕ, (Fin k → Γ(M, Q)) → Γ(M.tensorPow k, Q)
  | 0, _ => Scheme.Modules.unitSectionsEquiv Q 1
  | k + 1, s => Scheme.Modules.tmulSection (s 0) (tensorSection M Q k (Fin.tail s))

private theorem tensorSection_twist
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (j : X ⟶ Proj 𝒜) [IsOpenImmersion j]
    (e k : ℕ) (Q : X.Opens)
    (s : Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict j, Q)) :
    tensorSection ((Proj.twist 𝒜 (Int.ofNat e)).restrict j) Q k s =
      Proj.twistTensorSection 𝒜 j e Q k s := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (Scheme.Modules.tmulSection (s 0)) (ih (Fin.tail s))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem powerComparison_sections
    {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h]
    (M : Y.Modules) (N : X.Modules) (a : N ≅ M.restrict h)
    (k : ℕ) (Q : X.Opens) (s : Fin k → Γ(N, Q)) :
    (tensorPowerIso a k ≪≫
      (Scheme.Modules.openRestrictionTensorPowIso h M k).symm).hom.app Q
        (tensorSection N Q k s) =
      tensorSection M (h ''ᵁ Q) k
        (fun z ↦ (M.restrictAppIso h Q).hom (a.hom.app Q (s z))) := by
  induction k with
  | zero =>
    change (h.appIso Q).inv (1 : Γ(X, Q)) = 1
    exact map_one _
  | succ k ih =>
    change (Scheme.Modules.openRestrictionTensorIso h M (M.tensorPow k)).inv.app Q
      ((MonoidalCategory.tensorHom (𝟙 (M.restrict h))
        (Scheme.Modules.openRestrictionTensorPowIso h M k).inv).app Q
        ((MonoidalCategory.tensorHom a.hom (tensorPowerIso a k).hom).app Q
          (Scheme.Modules.tmulSection (s 0) (tensorSection N Q k (Fin.tail s))))) = _
    rw [Scheme.Modules.tensorHom_app_tmulSection,
      Scheme.Modules.tensorHom_app_tmulSection,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
    have hc := Scheme.Modules.openRestrictionTensorIso_inv_tmul h M (M.tensorPow k) Q
      (a.hom.app Q (s 0))
      ((Scheme.Modules.openRestrictionTensorPowIso h M k).inv.app Q
        ((tensorPowerIso a k).hom.app Q (tensorSection N Q k (Fin.tail s))))
    refine hc.trans ?_
    change Scheme.Modules.tmulSection (M := M) (N := M.tensorPow k)
      (U := h ''ᵁ Q) (a.hom.app Q (s 0))
      (((tensorPowerIso a k ≪≫
        (Scheme.Modules.openRestrictionTensorPowIso h M k).symm).hom).app Q
          (tensorSection N Q k (Fin.tail s))) = _
    exact congrArg (Scheme.Modules.tmulSection (M := M) (N := M.tensorPow k)
      (U := h ''ᵁ Q) (a.hom.app Q (s 0))) (ih (Fin.tail s))

set_option backward.isDefEq.respectTransparency false in
private theorem ample_restrict_iso {X Y : Scheme.{u}} (h : X ⟶ Y) [IsIso h]
    (L : Y.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple Y L) :
    ∃ hR : (L.restrict h).IsInvertible,
      @Scheme.Modules.IsAmple X (L.restrict h) hR := by
  have : CompactSpace Y := hL.1
  have hR : (L.restrict h).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso ((Scheme.Modules.restrictFunctorIsoPullback h).symm.app L)
  refine ⟨hR, h.homeomorph.symm.compactSpace, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, O, hxO, hO, hs⟩ := hL.2 (h x)
  let r := ((L.tensorPow n).restrictAppIso h ⊤).inv
    ((L.tensorPow n).presheaf.map (homOfLE le_top).op s)
  let a := Scheme.Modules.openRestrictionTensorPowIso h L n
  let t := a.hom.app ⊤ r
  refine ⟨n, hn, t, h ⁻¹ᵁ O, hxO, hO.preimage h, ?_⟩
  intro y
  change h y ∈ O ↔ y ∈ Scheme.Modules.nonvanishingLocus _ t
  have ht := Scheme.Modules.nonvanishingLocus_iso a r
  have hr := Scheme.Modules.nonvanishingLocus_restrict h (L.tensorPow n) s
  exact (hs (h y)).trans (Set.ext_iff.mp (ht.trans hr) y).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem common_degree_transport
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {U : Scheme.{u}} (j : U ⟶ Proj 𝒜) [IsOpenImmersion j] [CompactSpace U]
    (V : (Proj 𝒜).Opens) (h : U ⟶ V.toScheme) [IsIso h]
    (hfac : h ≫ V.ι = j) :
    ∃ e : ℕ, 0 < e ∧
      ∀ k : ℕ, 0 < k →
        ∃ hL : ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j).IsInvertible,
          @Scheme.Modules.IsAmple U
            ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j) hL ∧
          ∃ μ : ((Proj.twist 𝒜 (Int.ofNat e)).restrict j).tensorPow k ⟶
              (Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j,
            IsIso μ ∧
            ∀ (V : U.Opens)
              (s : Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict j, V))
              (x : j ''ᵁ V),
              (((Proj.twist 𝒜 (Int.ofNat (e * k))).restrictAppIso j V).hom
                (Scheme.Modules.Hom.app μ V (Proj.twistTensorSection 𝒜 j e V k s))).val x =
              ∏ i : Fin k,
                ((((Proj.twist 𝒜 (Int.ofNat e)).restrictAppIso j V).hom (s i)).val x :
                  Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) := by
  classical
  have : CompactSpace V.toScheme := h.homeomorph.compactSpace
  obtain ⟨e, he, hdeg⟩ := common_degree_on_open 𝒜 V
  refine ⟨e, he, fun k hk ↦ ?_⟩
  obtain ⟨hL, hample, μ, hμ, hprod⟩ := hdeg k hk
  have : IsIso μ := hμ
  let L : V.toScheme.Modules := (Proj.twist 𝒜 (Int.ofNat e)).restrict V.ι
  let a : (Proj.twist 𝒜 (Int.ofNat e)).restrict j ≅ L.restrict h :=
    Scheme.Modules.restrictCompIso (Proj.twist 𝒜 (Int.ofNat e)) V.ι h j hfac
  let b : (Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j ≅
      ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict V.ι).restrict h :=
    Scheme.Modules.restrictCompIso
      (Proj.twist 𝒜 (Int.ofNat (e * k))) V.ι h j hfac
  let c : ((Proj.twist 𝒜 (Int.ofNat e)).restrict j).tensorPow k ≅
      (L.tensorPow k).restrict h :=
    tensorPowerIso a k ≪≫ (Scheme.Modules.openRestrictionTensorPowIso h L k).symm
  let ν := c.hom ≫ (Scheme.Modules.restrictFunctor h).map μ ≫ b.inv
  obtain ⟨hR, hRA⟩ := ample_restrict_iso h _ hample
  have hT : ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso b.symm
  refine ⟨hT, (Scheme.Modules.isAmple_iff_of_iso b.symm).mp hRA, ν, inferInstance, ?_⟩
  intro Q s x
  have hx : x.val ∈ V.ι ''ᵁ (h ''ᵁ Q) := by
    simpa only [← hfac, Scheme.Hom.comp_image] using x.prop
  let y : V.ι ''ᵁ (h ''ᵁ Q) := ⟨x.val, hx⟩
  have hs₀ := tensorSection_twist 𝒜 j e k Q s
  have hs₁ := powerComparison_sections (X := U) (Y := V.toScheme) h L
    ((Proj.twist 𝒜 (Int.ofNat e)).restrict j) a k Q s
  -- Keep the section comparison explicit: the two restrictions have different scalar rings.
  have hs₂ := tensorSection_twist 𝒜 V.ι e k (h ''ᵁ Q)
    (fun z ↦ (L.restrictAppIso h Q).hom (a.hom.app Q (s z)))
  have hs : c.hom.app Q (Proj.twistTensorSection 𝒜 j e Q k s) =
      Proj.twistTensorSection 𝒜 V.ι e (h ''ᵁ Q) k
        (fun z ↦ (L.restrictAppIso h Q).hom (a.hom.app Q (s z))) := by
    exact (congrArg (c.hom.app Q) hs₀.symm).trans (hs₁.trans hs₂)
  have hb := compTwistIso_value 𝒜 V.ι h j hfac (Int.ofNat (e * k)) Q
    (ν.app Q (Proj.twistTensorSection 𝒜 j e Q k s)) y
  have ha (z : Fin k) := compTwistIso_value 𝒜 V.ι h j hfac (Int.ofNat e) Q (s z) y
  have heq : ν ≫ b.hom = c.hom ≫ (Scheme.Modules.restrictFunctor h).map μ := by
    dsimp only [ν]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have heqapp := congrArg (fun φ ↦
    φ.app Q (Proj.twistTensorSection 𝒜 j e Q k s)) heq
  change b.hom.app Q (ν.app Q (Proj.twistTensorSection 𝒜 j e Q k s)) =
    μ.app (h ''ᵁ Q) (c.hom.app Q (Proj.twistTensorSection 𝒜 j e Q k s)) at heqapp
  rw [hs] at heqapp
  have hv := congrArg (fun t : Γ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict V.ι,
      h ''ᵁ Q) ↦ (t.val y : Localization.AtPrime y.val.asHomogeneousIdeal.toIdeal)) heqapp
  exact hb.symm.trans (hv.trans ((hprod (h ''ᵁ Q)
    (fun z ↦ (L.restrictAppIso h Q).hom (a.hom.app Q (s z))) y).trans
      (Finset.prod_congr rfl (fun z _ ↦ ha z))))

/-- Sufficiently divisible positive twists are ample on a quasi-compact open of Proj.

Source: Stacks Project, Constructions, Tag 01MW, clauses (2), (3), and (7), and
Properties, Tag 01Q2 (blueprint: lem-trf-proj-qc-open-twist-ample).

Proof: for the empty open take `e = 1`. Otherwise use the standard-open basis and
quasi-compactness (`lem-weil-pbc-proj-standard-open-inclusion`) to choose a finite
positive-degree homogeneous cover, and take a positive common multiple `e` of the
degrees. The common-degree lemma (`lem-trf-proj-common-degree-twist-invertible`)
puts the open inside the invertibility locus W_e and gives the invertibility of
every restricted twist of degree e*k and of the canonical multiplication maps.
Those maps multiply homogeneous local fractions, hence have the displayed action
on every tuple of local sections. Pure tensors locally generate the sheaf tensor
power, so this action specifies the multiplication morphism uniquely.
By `lem-trf-proj-twist-section-basic-open`, homogeneous sections have the standard
opens as their nonvanishing loci, and the affine ones form an open basis. For a
fixed positive k, replace their defining homogeneous elements by their k-th
powers. The nonvanishing loci stay the same and the degrees become multiples of
e*k. Use the multiplication identifications to view these sections as sections
of powers of O_U(e*k). This affine nonvanishing basis and quasi-compactness are
exactly `Scheme.Modules.IsAmple` for O_U(e*k). -/
theorem exists_common_degree_twist_ample
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {U : Scheme.{u}} (j : U ⟶ Proj 𝒜) [IsOpenImmersion j] [CompactSpace U] :
    ∃ e : ℕ, 0 < e ∧
      ∀ k : ℕ, 0 < k →
        ∃ hL : ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j).IsInvertible,
          @Scheme.Modules.IsAmple U
            ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j) hL ∧
          ∃ μ : ((Proj.twist 𝒜 (Int.ofNat e)).restrict j).tensorPow k ⟶
              (Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j,
            IsIso μ ∧
            ∀ (V : U.Opens)
              (s : Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict j, V))
              (x : j ''ᵁ V),
              (((Proj.twist 𝒜 (Int.ofNat (e * k))).restrictAppIso j V).hom
                (Scheme.Modules.Hom.app μ V (Proj.twistTensorSection 𝒜 j e V k s))).val x =
              ∏ i : Fin k,
                ((((Proj.twist 𝒜 (Int.ofNat e)).restrictAppIso j V).hom (s i)).val x :
                  Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) := by
  exact common_degree_transport 𝒜 j j.opensRange j.isoOpensRange.hom
    j.isoOpensRange_hom_ι

end AlgebraicGeometry
