/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
import WeilConjectures.AlgebraicGeometry.FineLogStalkChartSpreading
import WeilConjectures.TraceFormula.FsFaceSharpening
import WeilConjectures.AlgebraicGeometry.ChartFaceLocalizationLogification
import WeilConjectures.GroupTheory.IntegralMonoidFreeSharpeningSplitting

/-!
# Sharp charts for log regular fs log schemes

Source: ILO, Exposé VI, 1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-log-regular-sharp-chart).

The chart is modeled on the actual characteristic monoid, and its characteristic
map at the distinguished point is the identity under the canonical stalk identification.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private noncomputable def completionEquiv {P R : Type u} [CommMonoid P] [CommMonoid R]
    (e : P ≃* R) : Algebra.GrothendieckGroup P ≃* Algebra.GrothendieckGroup R :=
  (Localization.monoidOf (⊤ : Submonoid P)).mulEquivOfMulEquiv
    (Localization.monoidOf (⊤ : Submonoid R)) (j := e) (by
      ext r
      simp only [Submonoid.mem_map, Submonoid.mem_top, true_and]
      exact ⟨fun _ ↦ trivial, fun _ ↦ e.surjective r⟩)

private theorem completionEquiv_of {P R : Type u} [CommMonoid P] [CommMonoid R]
    (e : P ≃* R) (p : P) :
    completionEquiv e (Algebra.GrothendieckGroup.of p) =
      Algebra.GrothendieckGroup.of (e p) :=
  Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq _ _ _

private theorem fs_of_equiv {P R : Type u} [CommMonoid P] [CommMonoid R]
    (e : P ≃* R) (hP : IsFineSaturatedMonoid P) : IsFineSaturatedMonoid R := by
  classical
  have : Monoid.FG P := ⟨hP.1⟩
  have : Monoid.FG R := Monoid.fg_of_surjective e.toMonoidHom e.surjective
  refine ⟨Monoid.FG.fg_top, ?_, ?_⟩
  · intro a b hab
    apply e.symm.injective
    apply hP.2.1
    apply (completionEquiv e).injective
    simpa only [completionEquiv_of, e.apply_symm_apply] using hab
  · intro g n hn ⟨r, hr⟩
    obtain ⟨p, hp⟩ := hP.2.2 ((completionEquiv e).symm g) n hn
      ⟨e.symm r, (completionEquiv e).injective (by
        simpa only [completionEquiv_of, map_pow, e.apply_symm_apply,
          MulEquiv.apply_symm_apply] using hr)⟩
    exact ⟨e p, by rw [← completionEquiv_of, hp, MulEquiv.apply_symm_apply]⟩

private theorem face_units_equiv
    {Q : Type u} [CommMonoid Q] (F : Submonoid Q)
    (hu : ∀ r : Algebra.faceLocalization Q F,
      IsUnit r ↔ r.val ∈ Subgroup.closure
        (Algebra.GrothendieckGroup.of '' (F : Set Q))) :
    ∃ e : (Algebra.faceLocalization Q F)ˣ ≃*
        Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q)),
      ∀ a, (e a).val = (a.val).val := by
  let R := Algebra.faceLocalization Q F
  let H := Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q))
  let f : Rˣ →* Algebra.GrothendieckGroup Q := R.subtype.comp (Units.coeHom R)
  have hH : H ≤ f.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨q, hq, rfl⟩
    let r : R := ⟨Algebra.GrothendieckGroup.of q, ⟨q, 1, by simp⟩⟩
    obtain ⟨a, ha⟩ := (hu r).mpr (Subgroup.subset_closure ⟨q, hq, rfl⟩)
    exact ⟨a, congrArg Subtype.val ha⟩
  let fH : Rˣ →* H := f.codRestrict H (fun a ↦ (hu a.val).mp a.isUnit)
  have hfH : Function.Bijective fH := by
    constructor
    · intro a b hab
      apply Units.ext
      apply Subtype.ext
      exact congrArg (fun x : H ↦ x.val) hab
    · intro v
      obtain ⟨a, ha⟩ := hH v.property
      exact ⟨a, Subtype.ext ha⟩
  exact ⟨MulEquiv.ofBijective fH hfH, fun _ ↦ rfl⟩

private theorem stalkChart_of_sharp_product
    {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    {P : Type u} [CommMonoid P] (h : P →* M.toEtalePrelogStructure.stalk t)
    (hu : ∀ p, IsUnit (M.toEtalePrelogStructure.stalkAlpha t (h p)) ↔ p = 1)
    (e : (P × (strictLocalRing X t)ˣ) ≃* M.toEtalePrelogStructure.stalk t)
    (he : ∀ p a, e (p, a) = h p * M.unitsIn t a) : M.IsStalkChart t h := by
  have hf : h.coprod (M.unitsIn t) = e.toMonoidHom := by
    ext x
    exact (he x.1 x.2).symm
  have hc : divisorialChartCongruence
      ((M.toEtalePrelogStructure.stalkAlpha t).comp h).mrangeRestrict = ⊥ := by
    apply le_antisymm _ bot_le
    apply Con.conGen_le.mpr
    rintro x y ⟨p, a, ha, rfl, rfl⟩
    have hunit : IsUnit (M.toEtalePrelogStructure.stalkAlpha t (h p)) := by
      change M.toEtalePrelogStructure.stalkAlpha t (h p) = a.val at ha
      rw [ha]
      exact a.isUnit
    have hp : p = 1 := (hu p).mp hunit
    subst p
    have ha1 : a = 1 := Units.ext (by simpa using ha.symm)
    subst a
    exact (⊥ : Con (P × (strictLocalRing X t)ˣ)).refl _
  constructor
  · rw [hf]
    exact e.surjective
  · rw [hc, hf]
    apply Con.ext
    intro a b
    exact e.injective.eq_iff

/-- A log regular fs log scheme has an affine pointed étale chart modeled on its
sharp characteristic monoid. Source: ILO VI 1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-log-regular-sharp-chart).

Proof plan:
1. Choose an fs chart `Q` at the point and let `F` be the face mapping to local units.
The stalk pushout identifies the characteristic with `Q_F / Fᵍᵖ`.
2. Apply `lem-trf-fs-face-sharpening`: this quotient is fs sharp and its group completion
is free of finite rank, while the units of `Q_F` are precisely `Fᵍᵖ`.
3. Lift a finite basis of the characteristic group to `Qᵍᵖ`. The resulting group section
lands on the monoid in `Q_F`, since its difference from any representative is a unit.
This splits `Q_F` as the product of the characteristic monoid with `Fᵍᵖ`.
4. Push out this splitting along `Fᵍᵖ → Aˣ`. It gives a stalk chart from the characteristic
monoid whose induced map to the characteristic quotient is the identity.
5. Apply `lem-trf-fine-log-stalk-chart-spreading` to this specified germ to obtain an
affine pointed étale chart. Étale implies locally of finite presentation and hence locally
of finite type; `pqf-lem-locnoeth-lft` (Stacks Tag 01T6) gives local Noetherianity.
-/
theorem exists_sharp_chart_of_logRegular
    (X : FineSaturatedLogScheme.{u}) (_hX : X.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) :
    IsFineSaturatedMonoid (X.logStructure.characteristic t) ∧
      (∀ p : X.logStructure.characteristic t, IsUnit p → p = 1) ∧
      ∃ (W : X.scheme.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (β : X.logStructure.characteristic t →*
          X.logStructure.monoidSheaf.obj.obj (op W)),
        IsAffine W.left ∧ IsLocallyNoetherian W.left ∧
          X.logStructure.IsChart W β ∧
          ∀ p : X.logStructure.characteristic t,
            Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W w (β p)) = p := by
  classical
  let M := X.logStructure
  have : IsLocallyNoetherian X.scheme := X.locallyNoetherian
  obtain ⟨V, v, Q, instQ, c, hQ, hc⟩ := X.fineSaturated Ω t
  let β := (M.toEtalePrelogStructure.stalkAlpha t).comp
    ((M.toEtalePrelogStructure.germ t V v).hom.comp c)
  let F := (IsUnit.submonoid (strictLocalRing X.scheme t)).comap β
  obtain ⟨hF, ell, _hell, _huniq, _hpush, ι, _hι, hsplit⟩ :=
    chart_face_localization_logification X t V v Q hQ c hc β rfl F rfl
  -- Compare the two canonical presentations of the localized sharpening.
  let R := Algebra.faceLocalization Q F
  let B := (chartFaceQuotientCon F).Quotient
  obtain ⟨hR, hUnits, hA, _hsharp, φ, hφ, hφinj, _hgroup, hfree⟩ :=
    face_sharpening Q hQ F hF
  have hφval (r : R) : φ (Associates.mk r) =
      QuotientGroup.mk'
        (Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q))) r.val := by
    simpa [Algebra.faceLocalizationGroupMap, Algebra.GrothendieckGroup.lift] using hφ r
  have hker (r s : R) : chartFaceQuotientCon F r s ↔
      Associates.mk r = Associates.mk s := by
    change QuotientGroup.mk' _ r.val = QuotientGroup.mk' _ s.val ↔ _
    rw [← hφval r, ← hφval s]
    exact hφinj.eq_iff
  let a : B →* Associates R :=
    (chartFaceQuotientCon F).lift Associates.mkMonoidHom (fun r s h ↦ (hker r s).mp h)
  have habij : Function.Bijective a := by
    constructor
    · intro b d h
      obtain ⟨r, rfl⟩ := (chartFaceQuotientCon F).mk'_surjective b
      obtain ⟨s, rfl⟩ := (chartFaceQuotientCon F).mk'_surjective d
      exact (Con.eq _).mpr ((hker r s).mpr h)
    · intro b
      obtain ⟨r, rfl⟩ := Associates.mk_surjective b
      exact ⟨(chartFaceQuotientCon F).mk' r, rfl⟩
  let eA : B ≃* Associates R := MulEquiv.ofBijective a habij
  let eP : Associates R ≃* M.characteristic t := eA.symm.trans ι
  have hP : IsFineSaturatedMonoid (M.characteristic t) := fs_of_equiv eP hA
  refine ⟨hP, fun p hp ↦ (Associates.isUnit_iff_eq_one p).mp hp, ?_⟩
  obtain ⟨_hinj, _hsurj, _hkerG, tg, _htg, _htgmem,
    j, _hjg, hj, e, he, _heinv⟩ :=
    Algebra.integral_monoid_free_sharpening_splitting R hR.2.1 hfree
  -- The algebraic splitter uses actual units; logification uses the face subgroup.
  obtain ⟨eU, heU⟩ := face_units_equiv F hUnits
  let s : B →* R := j.comp eA.toMonoidHom
  have hs (b : B) : (chartFaceQuotientCon F).mk' (s b) = b := by
    apply eA.injective
    change Associates.mk (j (eA b)) = eA b
    exact DFunLike.congr_fun hj (eA b)
  let eSplit : (B × Subgroup.closure
      (Algebra.GrothendieckGroup.of '' (F : Set Q))) ≃* R :=
    (MulEquiv.prodCongr eA eU.symm).trans e
  have heSplit (b : B) (v : Subgroup.closure
      (Algebra.GrothendieckGroup.of '' (F : Set Q))) :
      (eSplit (b, v)).val = (s b).val * v.val := by
    change (e (eA b, eU.symm v)).val = _
    rw [he]
    change (j (eA b)).val * ((eU.symm v).val).val = _
    rw [← heU, eU.apply_symm_apply]
    rfl
  obtain ⟨hsunit, ⟨es, hes⟩, _hlog, hchar⟩ := hsplit s hs eSplit heSplit
  -- Reparametrize by the actual characteristic, retaining its specified identity map.
  let h : M.characteristic t →* M.toEtalePrelogStructure.stalk t :=
    (ell.comp s).comp ι.symm.toMonoidHom
  let ep : (M.characteristic t × (strictLocalRing X.scheme t)ˣ) ≃*
      M.toEtalePrelogStructure.stalk t :=
    (MulEquiv.prodCongr ι.symm (MulEquiv.refl _)).trans es
  have hh : M.IsStalkChart t h := by
    have hu : ∀ p, IsUnit (M.toEtalePrelogStructure.stalkAlpha t (h p)) ↔ p = 1 := by
      intro p
      change IsUnit (M.toEtalePrelogStructure.stalkAlpha t (ell (s (ι.symm p)))) ↔ p = 1
      rw [hsunit, ← ι.symm.map_one]
      exact ι.symm.injective.eq_iff
    exact stalkChart_of_sharp_product M t h hu ep (fun p a ↦ hes (ι.symm p) a)
  have hM : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
      (t' : Spec (.of Ω') ⟶ X.scheme),
      ∃ (V : X.scheme.Etale) (_v : (Scheme.pointSmallEtale t').fiber.obj V)
        (Q : Type u) (_ : CommMonoid Q) (q : Q →* M.monoidSheaf.obj.obj (op V)),
        Monoid.FG Q ∧
          Function.Injective (Algebra.GrothendieckGroup.of (M := Q)) ∧ M.IsChart V q := by
    intro Ω' _ _ t'
    obtain ⟨V', v', Q', iQ', q', hQ', hq'⟩ := X.fineSaturated Ω' t'
    exact ⟨V', v', Q', iQ', q', ⟨hQ'.1⟩, hQ'.2.1, hq'⟩
  obtain ⟨W, w, b, hW, hb, hbgerm⟩ :=
    M.exists_affine_chart_of_isStalkChart hM t ⟨hP.1⟩ hP.2.1 h hh
  refine ⟨W, w, b, hW, LocallyOfFiniteType.isLocallyNoetherian (Y := X.scheme) W.hom, hb, ?_⟩
  intro p
  have hg := DFunLike.congr_fun hbgerm p
  change M.toEtalePrelogStructure.germ t W w (b p) = h p at hg
  rw [hg]
  exact (hchar (ι.symm p)).trans (ι.apply_symm_apply p)

end AlgebraicGeometry
