/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.StrictLocalComparisonIndEtale
import WeilConjectures.AlgebraicGeometry.LocallyIndEtaleBaseChangeCharts
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing

/-! # Ind-etale invariance of strict localizations

Source: Stacks Project, Tags 05WR and 0GIP
(blueprint: lem-trf-ind-etale-strict-local-invariance).
This module records the full strict-local, base-change, and structural-map clauses.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem indEtale_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : e.toRingHom.IndEtale := by
  rw [RingHom.IndEtale.iff_ind_etale]
  exact MorphismProperty.le_ind _ _ (RingHom.Etale.of_bijective e.bijective)

private theorem across_of_indEtale {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.IndEtale) : f.IndEtaleAcrossUniverses := by
  exact (indEtale_of_ringEquiv ULift.ringEquiv.symm).comp
    (hf.comp (indEtale_of_ringEquiv ULift.ringEquiv))

private theorem strictLocal_isIso_of_chart
    {S T : Scheme.{u}} (g : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (A B : CommRingCat.{u}) (iU : Spec A ⟶ S) (iV : Spec B ⟶ T)
    [IsOpenImmersion iU] [IsOpenImmersion iV]
    (hs : (t ≫ g) (IsLocalRing.closedPoint Ω) ∈ Set.range iU)
    (ht : t (IsLocalRing.closedPoint Ω) ∈ Set.range iV)
    (f : A →+* B)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ iU = iV ≫ g)
    (hind : f.IndEtaleAcrossUniverses) : IsIso (strictHenselizationMap g t) := by
  let h : strictHenselizationRing (t ≫ g) ⟶ strictHenselizationRing t :=
    Spec.preimage (strictHenselizationMap g t)
  have hh : Spec.map h = strictHenselizationMap g t := Spec.map_preimage _
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, hS, hT, hlocal, _⟩ :=
    strictLocalComparison_indEtale g t A B iU iV hs ht f hf hind h hh
  let := hS
  let := hT
  let := hlocal
  let : Algebra (strictHenselizationRing (t ≫ g)) (strictHenselizationRing t) :=
    h.hom.toAlgebra
  have hindh := (hab a b ha hb).2.2.2.2
  have hweak : Algebra.WeaklyEtale
      (strictHenselizationRing (t ≫ g)) (strictHenselizationRing t) := by
    let : Algebra (ULift.{u} (strictHenselizationRing (t ≫ g)))
        (ULift.{u} (strictHenselizationRing t)) :=
      ULift.algebra' (strictHenselizationRing (t ≫ g))
        (ULift.{u} (strictHenselizationRing t))
    apply Algebra.WeaklyEtale.ulift_iff.mp
    apply RingHom.weaklyEtale_algebraMap_iff.mp
    exact hindh.weaklyEtale
  let := hweak
  have hbij : Function.Bijective h.hom :=
    Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing
  let e := (RingEquiv.ofBijective h.hom hbij).toCommRingCatIso
  have he : e.hom = h := rfl
  rw [← hh, ← he]
  infer_instance

private theorem strictLocal_isIso_of_charts
    {S T : Scheme.{u}} (g : T ⟶ S)
    (hu : ∀ x : T, ∃ (A B : CommRingCat.{u}) (f : A ⟶ B)
      (iV : Spec B ⟶ T) (iU : Spec A ⟶ S),
      IsOpenImmersion iV ∧ IsOpenImmersion iU ∧ x ∈ Set.range iV ∧
      Spec.map f ≫ iU = iV ≫ g ∧ RingHom.IndEtaleAcrossUniverses f.hom)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    IsIso (strictHenselizationMap g t) := by
  obtain ⟨A, B, f, iV, iU, hV, hU, ⟨x, hx⟩, hf, hind⟩ :=
    hu (t (IsLocalRing.closedPoint Ω))
  let := hV
  let := hU
  apply strictLocal_isIso_of_chart g t A B iU iV _ ⟨x, hx⟩ f.hom hf hind
  refine ⟨Spec.map f x, ?_⟩
  have hp := congrArg (fun k ↦ k x) hf
  simpa only [Scheme.Hom.comp_apply, hx] using hp

-- The fixed statement names an equality binder unused in the conclusion.
set_option linter.unusedVariables false in
/-- An ind-etale morphism induces the canonical strict-local isomorphism at every geometric
point, compatibly with arbitrary scheme base change and with the structural map.
Source: Stacks Project, Tags 05WR and 0GIP.
(blueprint: lem-trf-ind-etale-strict-local-invariance).
Proof steps:
1. Choose affine charts around the source and target points. The strict-henselization limit
   construction and functoriality give strictly henselian local rings, the structural square,
   and the canonical local homomorphism whose residue map is the inclusion of separable closures.
2. The affine-chart ind-etale lemma makes both strict-henselization rings ind-etale over the
   target affine ring. Stability under composition and relative maps makes the canonical local
   homomorphism weakly etale.
3. Olivier's theorem for a weakly etale map from a strictly henselian local ring makes this
   homomorphism an isomorphism. Its spectrum is the required canonical isomorphism over the base,
   and the residue compatibility is exactly the displayed evaluation equation.
4. After an arbitrary base change, intersect the inverse images of the chosen affine charts and
   identify the resulting affine open with the tensor-product fibre-product chart. Ind-etaleness
   is stable under this base change, so steps 1--3 apply to every resulting geometric point.
5. For the structural map localized at its closed geometric point, put
   `s̃ = Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barS))`. The same
   argument applies to `s̃` and `strictHenselizationStructuralMap barS`; the canonical map
   `strictHenselizationMap (strictHenselizationStructuralMap barS) s̃` is therefore an
   isomorphism (and has the two canonical structural and evaluation equations).
-/
theorem indEtale_strictLocal_invariance
    {S T : Scheme.{u}} (u : T ⟶ S)
    (hlocal : ∀ (t : T), ∃ (V : T.Opens) (U : S.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine U.toScheme ∧
      ∃ e : V.toScheme ⟶ U.toScheme,
        e ≫ U.ι = V.ι ≫ u ∧ proAffineEtale e) :
    ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (barT : Spec (.of Ω) ⟶ T) (barS : Spec (.of Ω) ⟶ S)
      (hbar : barS = barT ≫ u),
      ∃ e : strictHenselizationScheme barT ≅ strictHenselizationScheme barS,
        e.hom ≫ strictHenselizationStructuralMap barS =
          strictHenselizationStructuralMap barT ≫ u ∧
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barT)) ≫ e.hom =
          Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barS)) ∧
        (∀ (S' : Scheme.{u}) (g : S' ⟶ S)
          {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
          (barT' : Spec (.of Ω') ⟶ pullback u g),
          ∃ e' : strictHenselizationScheme barT' ≅
              strictHenselizationScheme (barT' ≫ pullback.snd u g),
            e'.hom ≫ strictHenselizationStructuralMap (barT' ≫ pullback.snd u g) =
              strictHenselizationStructuralMap barT' ≫ pullback.snd u g ∧
            Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barT')) ≫
                e'.hom =
              Spec.map (CommRingCat.ofHom
                (strictHenselizationPointEvaluation (barT' ≫ pullback.snd u g)))) ∧
        IsIso (strictHenselizationMap (strictHenselizationStructuralMap barS)
          (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barS)))) := by
  classical
  have hu : ∀ x : T, ∃ (A B : CommRingCat.{u}) (f : A ⟶ B)
      (iV : Spec B ⟶ T) (iU : Spec A ⟶ S),
      IsOpenImmersion iV ∧ IsOpenImmersion iU ∧ x ∈ Set.range iV ∧
      Spec.map f ≫ iU = iV ≫ u ∧ RingHom.IndEtaleAcrossUniverses f.hom := by
    intro x
    obtain ⟨V, U, hx, hV, hU, e, he, hind⟩ := hlocal x
    let := hV
    let := hU
    refine ⟨Γ(U.toScheme, ⊤), Γ(V.toScheme, ⊤), e.appTop,
      V.toScheme.isoSpec.inv ≫ V.ι, U.toScheme.isoSpec.inv ≫ U.ι,
      inferInstance, inferInstance, ?_, ?_, ?_⟩
    · refine ⟨V.toScheme.isoSpec.hom ⟨x, hx⟩, ?_⟩
      change ((V.toScheme.isoSpec.hom ≫ V.toScheme.isoSpec.inv) ≫ V.ι) ⟨x, hx⟩ = x
      simp
    · rw [← Category.assoc, Scheme.isoSpec_inv_naturality, Category.assoc, he]
      simp only [Category.assoc]
    · exact across_of_indEtale _ (proAffineEtale_iff_appTop.mp hind)
  intro Ω _ _ barT barS hbar
  subst hbar
  let := strictLocal_isIso_of_charts u hu barT
  refine ⟨asIso (strictHenselizationMap u barT), strictHenselizationMap_over u barT,
    (Classical.choose_spec (strictHenselizationMap_existsUnique u barT)).1.2, ?_, ?_⟩
  · intro S' g Ω' _ _ barT'
    let := strictLocal_isIso_of_charts (pullback.snd u g)
      (locally_indEtale_base_change_charts u hu g).2 barT'
    exact ⟨asIso (strictHenselizationMap (pullback.snd u g) barT'),
      strictHenselizationMap_over (pullback.snd u g) barT',
      (Classical.choose_spec
        (strictHenselizationMap_existsUnique (pullback.snd u g) barT')).1.2⟩
  · let s := barT ≫ u
    obtain ⟨A, iU, hU, x, hx⟩ := Scheme.exists_Spec_apply_eq
      (s (IsLocalRing.closedPoint Ω))
    let := hU
    let r : strictHenselizationRing (s ≫ 𝟙 S) ⟶ strictHenselizationRing s :=
      Spec.preimage (strictHenselizationMap (𝟙 S) s)
    have hr : Spec.map r = strictHenselizationMap (𝟙 S) s := Spec.map_preimage _
    have hs : (s ≫ 𝟙 S) (IsLocalRing.closedPoint Ω) ∈ Set.range iU := by
      exact ⟨x, by simpa using hx⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, _⟩ := strictLocalComparison_indEtale (𝟙 S) s
      A A iU iU hs ⟨x, hx⟩ (RingHom.id A) (by simp)
      (across_of_indEtale _ (indEtale_of_ringEquiv (RingEquiv.refl A))) r hr
    have hbind : b.IndEtaleAcrossUniverses := (hab a b ha hb).2.2.1
    let t := Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation s))
    apply strictLocal_isIso_of_chart (strictHenselizationStructuralMap s) t
      A (strictHenselizationRing s) iU (𝟙 _) _ ⟨_, rfl⟩ b _ hbind
    · rw [show t ≫ strictHenselizationStructuralMap s = s from
        strictHenselizationClosedLift_over s]
      exact ⟨x, hx⟩
    · simpa using hb

end AlgebraicGeometry.Scheme
