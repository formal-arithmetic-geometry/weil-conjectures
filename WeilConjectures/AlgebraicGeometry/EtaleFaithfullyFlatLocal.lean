/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationNearOfFieldExtension
import WeilConjectures.RingTheory.IsEtaleAtFieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Pointwise étaleness descends along a field extension

Source: Stacks Project, Varieties, Tag 0C4Y and Descent, Tag 02VN
(blueprint: lem-sc-etale-faithfully-flat-local).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Formal étaleness respects isomorphisms of source and target rings. -/
private theorem formallyEtale_respectsIso : RingHom.RespectsIso @RingHom.FormallyEtale := by
  apply RingHom.StableUnderComposition.respectsIso
    (fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg)
  intro R S _ _ e
  have h := RingHom.Etale.of_bijective (f := e.toRingHom) e.bijective
  let := e.toRingHom.toAlgebra
  have : Algebra.Etale R S := h
  exact inferInstanceAs (Algebra.FormallyEtale R S)

/-- An étale ring map induces formally étale maps on local rings. -/
private theorem formallyEtale_localRingHom
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Etale)
    (q : Ideal S) [q.IsPrime] :
    (Localization.localRingHom (q.comap φ) q φ rfl).FormallyEtale := by
  algebraize [φ]
  let p := q.comap φ
  have : q.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FormallyEtale R (Localization.AtPrime q) := inferInstance
  have : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_restrictScalars (R := R)
  exact this

/-- An étale scheme morphism has formally étale stalk maps. -/
private theorem formallyEtale_stalk_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    (f.stalkMap x).hom.FormallyEtale := by
  exact HasRingHomProperty.stalkMap_of_respectsIso (P := @Etale)
    formallyEtale_respectsIso (fun φ hφ q _ ↦ formallyEtale_localRingHom φ hφ q)
    inferInstance x

/-- An étale neighbourhood suffices to make the designated stalk map formally étale. -/
private theorem formallyEtale_stalk_of_near
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) :
    (f.stalkMap x).hom.FormallyEtale := by
  obtain ⟨U, hx, hU⟩ := h
  have : Etale (U.ι ≫ f) := hU
  have h := formallyEtale_stalk_of_etale (U.ι ≫ f) ⟨x, hx⟩
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    formallyEtale_respectsIso.cancel_right_isIso] at h
  exact h

/-- For spectra, formal étaleness of the stalk map gives étaleness at the prime. -/
private theorem isEtaleAt_of_formallyEtale_stalk
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (h : ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q).hom.FormallyEtale) :
    Algebra.IsEtaleAt R q.asIdeal := by
  have h := (formallyEtale_respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)).mp h
  let p := q.asIdeal.comap (algebraMap R S)
  have : q.asIdeal.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := h
  exact Algebra.FormallyEtale.comp R (Localization.AtPrime p) _

/-- A finitely presented algebra étale at a prime has an étale basic neighbourhood. -/
private theorem near_etale_of_isEtaleAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : PrimeSpectrum S)
    [Algebra.IsEtaleAt R q.asIdeal] :
    ∃ U : (Spec (CommRingCat.of S)).Opens, q ∈ U ∧
      Etale (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  obtain ⟨r, hr, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) q.asIdeal
  have : Algebra.Etale R (Localization.Away r) := he
  let j := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))
  have hj : Etale (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [← Spec.map_comp]
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  refine ⟨j.opensRange, ?_, ?_⟩
  · change q ∈ Set.range j
    change q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away r)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  · let e := IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by
      rw [Scheme.Opens.range_ι]; rfl)
    have : Etale (e.inv ≫ (j ≫ Spec.map
        (CommRingCat.ofHom (algebraMap R S)))) := inferInstance
    dsimp [e] at this
    simpa only [← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac] using this

/-- Formal étaleness of stalk maps is unchanged by restricting both affine charts. -/
private theorem formallyEtale_stalk_of_open_square
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ T)
    (a : Z ⟶ X) (b : T ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b]
    (hsq : a ≫ f = g ≫ b) (z : Z)
    (h : (f.stalkMap (a z)).hom.FormallyEtale) :
    (g.stalkMap z).hom.FormallyEtale := by
  have h' : ((a ≫ f).stalkMap z).hom.FormallyEtale := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      formallyEtale_respectsIso.cancel_right_isIso]
    exact h
  rw [hsq, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    formallyEtale_respectsIso.cancel_left_isIso] at h'
  exact h'

/-- An étale neighbourhood in an open chart gives an étale neighbourhood in the scheme. -/
private theorem near_etale_of_open_chart
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ X) [IsOpenImmersion i]
    (z : Z) (h : ∃ V : Z.Opens, z ∈ V ∧ Etale (V.ι ≫ i ≫ f)) :
    ∃ U : X.Opens, i z ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨V, hz, hV⟩ := h
  let j := V.ι ≫ i
  have : Etale (j ≫ f) := by simpa only [j, Category.assoc] using hV
  let e := IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by
    rw [Scheme.Opens.range_ι]; rfl)
  refine ⟨j.opensRange, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
  have : Etale (e.inv ≫ (j ≫ f)) := inferInstance
  dsimp [e] at this
  simpa only [← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac] using this

/-- Apply primewise field descent in compatible affine charts and return to the scheme. -/
private theorem tensor_chart_descent
    (k K A B : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra A B] [Algebra k B]
    [IsScalarTower k A B] [Algebra.FinitePresentation A B]
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y)
    (a : Spec (CommRingCat.of B) ⟶ X.left)
    (b : Spec (CommRingCat.of A) ⟶ Y.left)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : Spec.map (CommRingCat.ofHom (algebraMap k B)) = a ≫ X.hom)
    (hb : Spec.map (CommRingCat.ofHom (algebraMap k A)) = b ≫ Y.hom)
    (hf : a ≫ f.left = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ b)
    (q : PrimeSpectrum B)
    (xK : (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hx : pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) xK = a q)
    (h : ∃ U : (pullback X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
      xK ∈ U ∧ Etale (U.ι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left)) :
    ∃ U : X.left.Opens, a q ∈ U ∧ Etale (U.ι ≫ f.left) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let sA := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let sB := Spec.map (CommRingCat.ofHom (algebraMap k B))
  let φ := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let fK := ((Over.pullback i).map f).left
  let mA := pullback.map sA i Y.hom i b (𝟙 _) (𝟙 _)
    (by simpa [sA] using hb) (by simp)
  let mB := pullback.map sB i X.hom i a (𝟙 _) (𝟙 _)
    (by simpa [sB] using ha) (by simp)
  let aK := (pullbackSpecIso k B K).inv ≫ mB
  let bK := (pullbackSpecIso k A K).inv ≫ mA
  have : IsOpenImmersion mA := inferInstance
  have : IsOpenImmersion mB := inferInstance
  have : IsOpenImmersion aK := inferInstance
  have : IsOpenImmersion bK := inferInstance
  have hxrange : xK ∈ Set.range mB := by
    dsimp [mB]
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨q, hx.symm⟩, ⟨_, rfl⟩⟩
  obtain ⟨z, hz⟩ := hxrange
  let qK : PrimeSpectrum (TensorProduct k B K) := (pullbackSpecIso k B K).hom z
  have hqK : aK qK = xK := by
    dsimp [aK, qK]
    rw [Scheme.hom_inv_apply]
    exact hz
  let ψ := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B)
    (AlgHom.id k K)).toRingHom
  let : Algebra (TensorProduct k A K) (TensorProduct k B K) := ψ.toAlgebra
  let φK := Spec.map (CommRingCat.ofHom ψ)
  have haK : aK ≫ pullback.fst X.hom i =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (B := K))) ≫ a := by
    dsimp [aK, mB]
    simp [Category.assoc, pullback.map, sB, i]
  have hbK : bK ≫ pullback.fst Y.hom i =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := K))) ≫ b := by
    dsimp [bK, mA]
    simp [Category.assoc, pullback.map, sA, i]
  have haKs : aK ≫ pullback.snd X.hom i =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := K)).toRingHom) := by
    dsimp [aK, mB]
    simp [Category.assoc, pullback.map, sB, i]
  have hbKs : bK ≫ pullback.snd Y.hom i =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K)).toRingHom) := by
    dsimp [bK, mA]
    simp [Category.assoc, pullback.map, sA, i]
  have hsquare : aK ≫ fK = φK ≫ bK := by
    apply pullback.hom_ext
    · change aK ≫ fK ≫ pullback.fst Y.hom i = _
      have hfK := (baseChange_morphism_projections f (Over.mk i)).1
      change fK ≫ pullback.fst Y.hom i = pullback.fst X.hom i ≫ f.left at hfK
      rw [hfK, ← Category.assoc, haK, Category.assoc, hf, Category.assoc, hbK]
      dsimp [φK]
      simp only [← Category.assoc, ← Spec.map_comp]
      congr 2
    · change aK ≫ fK ≫ pullback.snd Y.hom i = _
      have hfK := (baseChange_morphism_projections f (Over.mk i)).2
      change fK ≫ pullback.snd Y.hom i = pullback.snd X.hom i at hfK
      rw [hfK, haKs, Category.assoc, hbKs]
      dsimp [φK]
      rw [← Spec.map_comp]
      congr 1
      ext t
      simp [ψ]
  have hformal : (φK.stalkMap qK).hom.FormallyEtale := by
    apply formallyEtale_stalk_of_open_square fK φK aK bK hsquare qK
    apply formallyEtale_stalk_of_near
    exact hqK.symm ▸ h
  have hupper : Algebra.IsEtaleAt (TensorProduct k A K) qK.asIdeal :=
    isEtaleAt_of_formallyEtale_stalk qK hformal
  have hcontract : Ideal.comap
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (B := K)) qK.asIdeal =
        q.asIdeal := by
    have hpoint : (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (B := K)))) qK = q := by
      apply a.isOpenEmbedding.injective
      rw [← hx, ← hqK]
      change (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (B := K))) ≫ a) qK =
          (aK ≫ pullback.fst X.hom i) qK
      rw [haK]
    exact congrArg PrimeSpectrum.asIdeal hpoint
  have : q.asIdeal.IsPrime := q.isPrime
  have : qK.asIdeal.IsPrime := qK.isPrime
  have : Algebra.IsEtaleAt A q.asIdeal :=
    Algebra.IsEtaleAt.of_fieldExtension k K A B q.asIdeal qK.asIdeal hcontract hupper
  apply near_etale_of_open_chart f.left a q
  obtain ⟨U, hq, hU⟩ := near_etale_of_isEtaleAt (R := A) q
  have : Etale (U.ι ≫ φ) := hU
  refine ⟨U, hq, ?_⟩
  rw [hf, ← Category.assoc]
  infer_instance

/-- Étaleness at a point descends along a faithfully flat field extension.
Source: Stacks Project, Varieties, Tag 0C4Y and Descent, Tag 02VN
(blueprint: lem-sc-etale-faithfully-flat-local).

Proof:
1. Choose affine open neighbourhoods `Spec B` of `x` in `X` and `Spec A` of
   `f x` in `Y`, with `f` restricting to `Spec B ⟶ Spec A`; let `q` be the
   prime of `B` corresponding to `x` (def-pc-scheme, def-pc-morphism-conventions).
   The point `xK` determines a prime `qK` of `B ⊗[k] K` over `q` (def-pc-base-change).
   Étaleness on an open neighbourhood of `xK` gives local finite presentation
   there (def-weil-etale-morphism, def-sbc-locally-finite-presentation).
   Pointwise descent of finite presentation (lem-sc-lfp-field-extension-pointwise-descent)
   lets us shrink so that `B` is finitely presented over `A`. The affine criterion
   for étaleness then gives `Algebra.IsEtaleAt (A ⊗[k] K) qK`.
2. By Tag 0C4Y, `B_q ⟶ (B ⊗[k] K)_qK` is faithfully flat. The hypotheses of
   lem-sc-etale-local-ring-faithfully-flat-descent are supplied by Step 1:
   `B` is finitely presented over the `k`-algebra `A`, `qK` contracts to `q`,
   and the base-changed algebra is étale at `qK`. Applying this lemma descends
   `Algebra.IsEtaleAt` to `q`; the affine criterion (def-weil-etale-morphism)
   supplies an étale open neighbourhood of `x`, which is the conclusion. -/
theorem etale_of_faithfullyFlat_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y)
    (x : X.left)
    (xK : (pullback X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hx : (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) xK = x) :
    (let fK := ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left
     ∃ U : (pullback X.hom
       (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
       xK ∈ U ∧ Etale (U.ι ≫ fK)) →
      ∃ U : X.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left) := by
  intro h
  have hlfp : ∃ U : X.left.Opens, x ∈ U ∧
      LocallyOfFinitePresentation (U.ι ≫ f.left) := by
    apply locallyOfFinitePresentation_near_of_fieldExtension k K X Y f x xK hx
    obtain ⟨W, hxW, hW⟩ := h
    have : Etale (W.ι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left) := hW
    exact ⟨W, hxW, inferInstance⟩
  obtain ⟨U, hxU, hU⟩ := hlfp
  have : LocallyOfFinitePresentation (U.ι ≫ f.left) := hU
  let g := U.ι ≫ f.left
  obtain ⟨V, W, hxW, e, hφ⟩ :=
    (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
      (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finitePresentation_holdsForLocalizationAway).left).mp
      (show LocallyOfFinitePresentation g from inferInstance) ⟨x, hxU⟩
  let A := Γ(Y.left, V.1)
  let B := Γ(U.toScheme, W.1)
  let : Algebra A B := (g.appLE V W e).hom.toAlgebra
  have : Algebra.FinitePresentation A B := hφ
  let b := V.2.fromSpec
  let a := W.2.fromSpec ≫ U.ι
  let : Algebra k A := (Spec.preimage (b ≫ Y.hom)).hom.toAlgebra
  let : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k A)) = b ≫ Y.hom :=
    Spec.map_preimage _
  have hf : a ≫ f.left = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ b := by
    exact (IsAffineOpen.SpecMap_appLE_fromSpec g V.2 W.2 e).symm
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k B)) = a ≫ X.hom := by
    change Spec.map (CommRingCat.ofHom ((algebraMap A B).comp (algebraMap k A))) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hb, ← Category.assoc, ← hf,
      Category.assoc, Over.w f]
  let q := W.2.primeIdealOf ⟨⟨x, hxU⟩, hxW⟩
  have haq : a q = x := by
    dsimp [a, q]
    rw [IsAffineOpen.fromSpec_primeIdealOf]
  have hx' : pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) xK = a q := hx.trans haq.symm
  obtain ⟨T, hqT, hT⟩ := tensor_chart_descent k K A B f a b ha hb hf q xK hx' h
  exact ⟨T, haq ▸ hqT, hT⟩

end AlgebraicGeometry
