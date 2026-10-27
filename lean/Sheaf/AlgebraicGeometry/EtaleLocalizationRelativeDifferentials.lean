/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityExact
import Sheaf.AlgebraicGeometry.SmoothDifferentialTransitivityShortExact
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRochCoherent

/-!
# Relative differentials under étale localization

Source: Stacks Project, More on Morphisms, Tag 04BX,
`lemma-sheaf-differentials-etale-localization`; canonical map: Tag 01UV
(blueprint: lem-sfb-etale-localization-relative-differentials).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

private theorem etale_differentials_zero {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    IsZero f.relativeDifferentials := by
  have : f.relativeDifferentials.IsFiniteLocallyFreeOfRank 0 :=
    f.isFiniteLocallyFreeOfRank_relativeDifferentials 0
  exact Modules.isZero_of_isFiniteLocallyFreeOfRank_zero _

private theorem congr_d {X S : Scheme.{u}} (f g : X ⟶ S) (h : f = g)
    (W : X.Opens) (r : Γ(X, W)) :
    (relativeDifferentialsCongr f h).hom.app W
      (f.relativeDifferentialsDerivation.d (X := op W) r) =
      g.relativeDifferentialsDerivation.d (X := op W) r := by
  subst h
  rfl

private theorem tensor_restrict {X Y : Scheme.{u}} (a : X ⟶ Y) (M : Y.Modules)
    (O : X.Opens) :
    ∃ e : ((Modules.tensorPullback a).obj M).restrict O.ι ≅
        (Modules.tensorPullback (O.ι ≫ a)).obj M,
      ∀ (W : Y.Opens) (m : Γ(M, W)),
        e.hom.app (O.ι ⁻¹ᵁ (a ⁻¹ᵁ W))
          (((Modules.tensorPullback a).obj M).presheaf.map
            (homOfLE (O.ι.image_preimage_le (a ⁻¹ᵁ W))).op
              (Modules.tensorPullbackSection a M W m)) =
          Modules.tensorPullbackSection (O.ι ≫ a) M W m := by
  let adj := ((Modules.tensorPullbackSectionAdjunction a).comp
    (Modules.restrictAdjunction O.ι)).ofNatIsoRight (Modules.pushforwardComp O.ι a)
  let adj' := Modules.tensorPullbackSectionAdjunction (O.ι ≫ a)
  let e := (adj.leftAdjointUniq adj').app M
  refine ⟨e, ?_⟩
  intro W m
  have he := adj.unit_leftAdjointUniq_hom_app adj' M
  have hunit : adj.unit.app M =
      (Modules.tensorPullbackSectionAdjunction a).unit.app M ≫
        (Modules.pushforward a).map
          ((Modules.restrictAdjunction O.ι).unit.app ((Modules.tensorPullback a).obj M)) ≫
        (Modules.pushforwardComp O.ι a).hom.app _ := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.homEquiv_id, Adjunction.comp_unit_app, Category.assoc]
    rfl
  rw [hunit] at he
  have hs := congrArg (fun k ↦ k.app W m) he
  have hn := (Classical.choose_spec
    (Modules.existsUnique_tensorPullbackSectionAdjunction a)).1 M W m
  have hn' := (Classical.choose_spec
    (Modules.existsUnique_tensorPullbackSectionAdjunction (O.ι ≫ a))).1 M W m
  change e.hom.app (O.ι ⁻¹ᵁ (a ⁻¹ᵁ W))
      (((Modules.tensorPullback a).obj M).presheaf.map
        (homOfLE (O.ι.image_preimage_le (a ⁻¹ᵁ W))).op
          (((Modules.tensorPullbackSectionAdjunction a).unit.app M).app W m)) =
      ((Modules.tensorPullbackSectionAdjunction (O.ι ≫ a)).unit.app M).app W m at hs
  change ((Modules.tensorPullbackSectionAdjunction a).unit.app M).app W m = _ at hn
  change ((Modules.tensorPullbackSectionAdjunction (O.ι ≫ a)).unit.app M).app W m = _ at hn'
  erw [hn, hn'] at hs
  exact hs

private theorem restrict_d {X S U : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X)
    [IsOpenImmersion j] (W : X.Opens) (r : Γ(X, W)) :
    (f.relativeDifferentialsRestrictIso j).hom.app (j ⁻¹ᵁ W)
      (f.relativeDifferentials.presheaf.map (homOfLE (j.image_preimage_le W)).op
        (f.relativeDifferentialsDerivation.d (X := op W) r)) =
      (j ≫ f).relativeDifferentialsDerivation.d (X := op (j ⁻¹ᵁ W)) (j.app W r) := by
  have he := ((Modules.restrictAdjunction j).homEquiv _ _).apply_symm_apply
    ((f.relativeDifferentialsHomEquiv _).symm (f.pushforwardDerivation j))
  rw [Adjunction.homEquiv_unit] at he
  have hs := congrArg (fun k ↦ k.app W (f.relativeDifferentialsDerivation.d r)) he
  exact hs.trans (f.pushforwardDerivation_desc_app_d j W r)

private theorem restriction_square_apply {X : Scheme.{u}} (O : X.Opens)
    {M N : X.Modules} {P Q : O.toScheme.Modules}
    (e : M.restrict O.ι ≅ P) (c : M ⟶ N) (α : N.restrict O.ι ⟶ Q) (d : P ⟶ Q)
    (h : (Modules.restrictFunctor O.ι).map c ≫ α = e.hom ≫ d)
    (W : X.Opens) (m : Γ(M, W)) :
    d.app (O.ι ⁻¹ᵁ W)
        (e.hom.app (O.ι ⁻¹ᵁ W)
          (M.presheaf.map (homOfLE (O.ι.image_preimage_le W)).op m)) =
      α.app (O.ι ⁻¹ᵁ W)
        (N.presheaf.map (homOfLE (O.ι.image_preimage_le W)).op (c.app W m)) := by
  have hh := congrArg (fun k ↦ k.app (O.ι ⁻¹ᵁ W)
    (M.presheaf.map (homOfLE (O.ι.image_preimage_le W)).op m)) h
  change α.app (O.ι ⁻¹ᵁ W)
      (c.app (O.ι ''ᵁ (O.ι ⁻¹ᵁ W))
        (M.presheaf.map (homOfLE (O.ι.image_preimage_le W)).op m)) =
    d.app (O.ι ⁻¹ᵁ W) (e.hom.app (O.ι ⁻¹ᵁ W)
      (M.presheaf.map (homOfLE (O.ι.image_preimage_le W)).op m)) at hh
  exact hh.symm.trans (congrArg (fun t ↦ α.app (O.ι ⁻¹ᵁ W) t)
    (PresheafOfModules.naturality_apply c.val
      (homOfLE (O.ι.image_preimage_le W)).op m))

private theorem pullback_d {X Y S : Scheme.{u}} (f : Y ⟶ S) (a : X ⟶ Y)
    (W : Y.Opens) (r : Γ(Y, W)) :
    (f.relativeDifferentialsPullbackMap a).app (a ⁻¹ᵁ W)
        (Modules.tensorPullbackSection a f.relativeDifferentials W
          (f.relativeDifferentialsDerivation.d (X := op W) r)) =
      (a ≫ f).relativeDifferentialsDerivation.d (X := op (a ⁻¹ᵁ W)) (a.app W r) := by
  exact (Classical.choose_spec (existsUnique_relativeDifferentialsPullbackMap f a)).1 W r

private theorem etale_source_map_isIso {X Y S : Scheme.{u}} (a : X ⟶ Y) (f : Y ⟶ S)
    [Etale a] : IsIso (f.relativeDifferentialsPullbackMap a) := by
  obtain ⟨_, _, zp, hp⟩ := relativeDifferentials_transitivity_shortExact_of_smooth a f
  exact hp.isIso_f_iff.mpr (etale_differentials_zero a)

private theorem etale_base_comparison {X Y S : Scheme.{u}} (f : X ⟶ Y) (b : Y ⟶ S)
    [Etale b] :
    ∃ q : (f ≫ b).relativeDifferentials ⟶ f.relativeDifferentials,
      IsIso q ∧ ∀ (O : X.Opens) (r : Γ(X, O)),
        q.app O ((f ≫ b).relativeDifferentialsDerivation.d (X := op O) r) =
          f.relativeDifferentialsDerivation.d (X := op O) r := by
  obtain ⟨q, hq, ⟨zq, hex⟩, hqepi, _⟩ := relativeDifferentials_transitivity_exact f b
  have hf : b.relativeDifferentialsPullbackMap f = 0 := by
    apply ((Modules.tensorPullbackSectionAdjunction f).homEquiv _ _).injective
    exact (etale_differentials_zero b).eq_of_src _ _
  have : Mono q := (ShortComplex.exact_iff_mono _ hf).mp hex
  have : Epi q := hqepi
  exact ⟨q, isIso_of_mono_of_epi q, hq⟩

private theorem exists_iso_composite {X : Scheme.{u}} {M N P Q : X.Modules}
    (p : M ⟶ N) (e : N ≅ P) (q : P ⟶ Q) [IsIso p] [IsIso q] :
    ∃ c : M ⟶ Q, IsIso c ∧ ∀ (W : X.Opens) (m : Γ(M, W)),
      c.app W m = q.app W (e.hom.app W (p.app W m)) := by
  exact ⟨p ≫ e.hom ≫ q, inferInstance, fun _ _ ↦ rfl⟩

private theorem exists_etale_comparison
    {X₁ X₂ S₁ S₂ : Scheme.{u}} (a : X₂ ⟶ X₁) (b : S₂ ⟶ S₁)
    (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂) [Etale a] [Etale b]
    (h : a ≫ f₁ = f₂ ≫ b) :
    ∃ c : (Modules.tensorPullback a).obj f₁.relativeDifferentials ⟶ f₂.relativeDifferentials,
      IsIso c ∧ ∀ (W : X₁.Opens) (r : Γ(X₁, W)),
        c.app (a ⁻¹ᵁ W)
            (Modules.tensorPullbackSection a f₁.relativeDifferentials W
              (f₁.relativeDifferentialsDerivation.d (X := op W) r)) =
          f₂.relativeDifferentialsDerivation.d (X := op (a ⁻¹ᵁ W)) (a.app W r) := by
  obtain ⟨q, hqi, hq⟩ := etale_base_comparison f₂ b
  have : IsIso q := hqi
  have : IsIso (f₁.relativeDifferentialsPullbackMap a) := etale_source_map_isIso a f₁
  obtain ⟨c, hci, hc⟩ := exists_iso_composite (f₁.relativeDifferentialsPullbackMap a)
    (relativeDifferentialsCongr (a ≫ f₁) h) q
  refine ⟨c, hci, ?_⟩
  intro W r
  rw [hc, pullback_d, congr_d, hq]

private theorem exists_restriction_square {X : Scheme.{u}} (O : X.Opens)
    {M N : X.Modules} {P Q : O.toScheme.Modules}
    (e : M.restrict O.ι ≅ P) (c : M ⟶ N) (α : N.restrict O.ι ⟶ Q) :
    ∃ d : P ⟶ Q,
      (Modules.restrictFunctor O.ι).map c ≫ α = e.hom ≫ d ∧
      ∀ (W : X.Opens) (m : Γ(M, W)),
        d.app (O.ι ⁻¹ᵁ W)
            (e.hom.app (O.ι ⁻¹ᵁ W)
              (M.presheaf.map (homOfLE (O.ι.image_preimage_le W)).op m)) =
          α.app (O.ι ⁻¹ᵁ W)
            (N.presheaf.map (homOfLE (O.ι.image_preimage_le W)).op (c.app W m)) := by
  let d := e.inv ≫ (Modules.restrictFunctor O.ι).map c ≫ α
  have h : (Modules.restrictFunctor O.ι).map c ≫ α = e.hom ≫ d := by
    simp [d]
  exact ⟨d, h, restriction_square_apply O e c α d h⟩

/-- In a commutative square with étale horizontal arrows, the canonical comparison
`a* Ω(X₁/S₁) → Ω(X₂/S₂)` is an isomorphism. Its formula on actual tensor-unit
sections specifies the map, including compatibility with the universal derivations.
On every source open, the restricted map is the comparison with the same formula;
the first-term identification is normalized on all pulled-back module sections.
Thus the existential maps are the canonical maps, not arbitrary isomorphisms.

Source: Stacks Project, More on Morphisms, Tag 04BX, and Morphisms, Tag 01UV
(blueprint: lem-sfb-etale-localization-relative-differentials).

Proof:
1. Apply lem-weil-pbc-etale-smooth-zero-dimensional-fibres to a and b. They are
   smooth of relative dimension zero. By lem-sc-smooth-omega-finite-locally-free
   and def-amb-finite-locally-free-module, their differential sheaves are locally
   free of rank zero, hence zero: sections vanish on a covering and therefore vanish.
2. Apply lem-a1-differential-sheaf-transitivity-exact to X₂ → S₂ → S₁.
   Its first term is the pullback of Ω(S₂/S₁), hence zero. Its second arrow q is
   therefore an isomorphism Ω(X₂/S₁) → Ω(X₂/S₂), sending dv to dv.
3. Apply lem-sfb-smooth-differential-transitivity-short-exact to X₂ → X₁ → S₁.
   Smoothness of a gives left exactness and Ω(X₂/X₁) = 0 gives right exactness,
   so p : a* Ω(X₁/S₁) → Ω(X₂/S₁) is an isomorphism, sending 1 tensor dr to d(a♯r).
4. Compose p with q and use commutativity of the square. The composite has the
   displayed universal-derivation formula, so is the canonical comparison of 01UV.
   Differential symbols generate Ω locally (def-weil-pbc-kahler-differentials),
   and their tensor units generate its pullback (def-pc-module-pullback), proving
   uniqueness from that formula. Restrict the tensor pullback and the differential
   sheaf to any open O. Their standard restriction identifications carry tensor
   units and differentials to the corresponding units and differentials. The same
   formula defines cO, and equality on these local generators gives the displayed
   restriction diagram. No Cartesian-square hypothesis is required. -/
theorem etale_localization_relativeDifferentials
    {X₁ X₂ S₁ S₂ : Scheme.{u}} (a : X₂ ⟶ X₁) (b : S₂ ⟶ S₁)
    (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂) [Etale a] [Etale b]
    (h : a ≫ f₁ = f₂ ≫ b) :
    ∃ c : (Modules.tensorPullback a).obj f₁.relativeDifferentials ⟶ f₂.relativeDifferentials,
      IsIso c ∧
      (∀ (W : X₁.Opens) (r : Γ(X₁, W)),
        c.app (a ⁻¹ᵁ W)
            (Modules.tensorPullbackSection a f₁.relativeDifferentials W
              (f₁.relativeDifferentialsDerivation.d (X := op W) r)) =
          f₂.relativeDifferentialsDerivation.d (X := op (a ⁻¹ᵁ W)) (a.app W r)) ∧
      (∀ O : X₂.Opens,
        ∃ (e : ((Modules.tensorPullback a).obj f₁.relativeDifferentials).restrict O.ι ≅
              (Modules.tensorPullback (O.ι ≫ a)).obj f₁.relativeDifferentials)
          (cO : (Modules.tensorPullback (O.ι ≫ a)).obj f₁.relativeDifferentials ⟶
              (O.ι ≫ f₂).relativeDifferentials),
          (∀ (W : X₁.Opens) (m : Γ(f₁.relativeDifferentials, W)),
            e.hom.app (O.ι ⁻¹ᵁ (a ⁻¹ᵁ W))
                (((Modules.tensorPullback a).obj f₁.relativeDifferentials).presheaf.map
                  (homOfLE (O.ι.image_preimage_le (a ⁻¹ᵁ W))).op
                  (Modules.tensorPullbackSection a f₁.relativeDifferentials W m)) =
              Modules.tensorPullbackSection (O.ι ≫ a) f₁.relativeDifferentials W m) ∧
          (∀ (W : X₁.Opens) (r : Γ(X₁, W)),
            cO.app ((O.ι ≫ a) ⁻¹ᵁ W)
                (Modules.tensorPullbackSection (O.ι ≫ a) f₁.relativeDifferentials W
                  (f₁.relativeDifferentialsDerivation.d (X := op W) r)) =
              (O.ι ≫ f₂).relativeDifferentialsDerivation.d
                (X := op ((O.ι ≫ a) ⁻¹ᵁ W)) ((O.ι ≫ a).app W r)) ∧
          (Modules.restrictFunctor O.ι).map c ≫
              (f₂.relativeDifferentialsRestrictIso O.ι).hom = e.hom ≫ cO) := by
  obtain ⟨c, hci, hc⟩ := exists_etale_comparison a b f₁ f₂ h
  refine ⟨c, hci, hc, ?_⟩
  intro O
  obtain ⟨e, he⟩ := tensor_restrict a f₁.relativeDifferentials O
  obtain ⟨cO, hcomm, hformula⟩ := exists_restriction_square O e c
    (f₂.relativeDifferentialsRestrictIso O.ι).hom
  refine ⟨e, cO, he, ?_, hcomm⟩
  intro W r
  have hh := hformula (a ⁻¹ᵁ W)
    (Modules.tensorPullbackSection a f₁.relativeDifferentials W
      (f₁.relativeDifferentialsDerivation.d (X := op W) r))
  have heval := congrArg
    (fun m ↦ cO.app ((O.ι ≫ a) ⁻¹ᵁ W) m)
    (he W (f₁.relativeDifferentialsDerivation.d (X := op W) r))
  have hval := congrArg
    (fun m : Γ(f₂.relativeDifferentials, a ⁻¹ᵁ W) ↦
      (f₂.relativeDifferentialsRestrictIso O.ι).hom.app (O.ι ⁻¹ᵁ (a ⁻¹ᵁ W))
        (f₂.relativeDifferentials.presheaf.map
          (homOfLE (O.ι.image_preimage_le (a ⁻¹ᵁ W))).op m)) (hc W r)
  exact heval.symm.trans (hh.trans
    (hval.trans (restrict_d f₂ O.ι (a ⁻¹ᵁ W) (a.app W r))))

end AlgebraicGeometry.Scheme.Hom
