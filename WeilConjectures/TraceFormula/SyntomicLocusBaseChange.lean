/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.CompleteIntersectionFibres
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.RingTheory.CompleteIntersectionLocalAlgebra
import WeilConjectures.TraceFormula.LciPointwiseCriterion
import WeilConjectures.TraceFormula.LciFieldChangeLocal
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionBaseChange
import WeilConjectures.RingTheory.GlobalCompleteIntersectionPrincipalLocalization
import WeilConjectures.TraceFormula.SyntomicPointwiseLocalModel

/-!
# The fibrewise complete-intersection locus

Source: Stacks Project, Morphisms, Tag 02V3 (lemma-set-points-where-fibres-lci),
with the local-ring convention of Algebra, Tag 00SD
(blueprint: lem-trf-syntomic-locus-base-change).

## Main definitions and statements

* `Scheme.Hom.IsCompleteIntersectionAtFiberPoint`: the local-ring condition on a fibre.
* `Scheme.Hom.fiberCompleteIntersectionLocus`: the subset `V_f` of the source.
* `Scheme.Hom.HasCompleteIntersectionFibres`: the condition on all local rings of all fibres.
* `syntomic_locus_base_change`: arbitrary base change and the largest syntomic source open.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciLocal_equiv {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : Algebra.IsCompleteIntersectionLocalAlgebra k A) :
    Algebra.IsCompleteIntersectionLocalAlgebra k B := by
  obtain ⟨hlocal, hft, R, hR, aR, hr, hRft, xs, hxs, hm, ⟨eR⟩⟩ := h
  have : IsLocalRing B := e.toRingEquiv.isLocalRing
  have : Algebra.EssFiniteType k B := (Algebra.EssFiniteType.iff_of_algEquiv e).mp hft
  exact ⟨inferInstance, inferInstance, R, hR, aR, hr, hRft, xs, hxs, hm,
    ⟨eR.trans e⟩⟩

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciLocal_iff {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [Algebra.EssFiniteType k A] :
    Algebra.IsCompleteIntersectionLocalAlgebra k A ↔
      Algebra.IsCompleteIntersectionLocal k A := by
  constructor
  · rintro ⟨_, _, R, hR, aR, hr, hft, xs, hxs, hm, he⟩
    exact ⟨R, hR, aR, hr, hft, xs, hxs, hm, he⟩
  · rintro ⟨R, hR, aR, hr, hft, xs, hxs, hm, he⟩
    exact ⟨inferInstance, inferInstance, R, hR, aR, hr, hft, xs, hxs, hm, he⟩

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ofList_eq (R : Type u) [CommRing R] (xs : List R) :
    Ideal.ofList xs = Ideal.span (Set.range (fun i : Fin xs.length ↦ xs.get i)) := by
  change Ideal.span _ = _
  congr 1
  ext x
  simp [List.mem_iff_get]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciLocal_to_presentation {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] (h : Algebra.IsCompleteIntersectionLocalAlgebra k A) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R)
      (_ : IsLocalRing R) (_ : IsNoetherianRing R),
      IsRegularLocalRing R ∧ Algebra.EssFiniteType k R ∧
        ∃ xs : List R, RingTheory.Sequence.IsRegular R xs ∧
          Nonempty ((R ⧸ Ideal.span (Set.range
            (fun i : Fin xs.length ↦ xs.get i))) ≃ₐ[k] A) := by
  obtain ⟨_, _, R, hR, aR, hr, hft, xs, hxs, _, ⟨e⟩⟩ := h
  rw [ofList_eq] at e
  exact ⟨R, hR, aR, inferInstance, inferInstance, hr, hft, xs, hxs, ⟨e⟩⟩

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciLocal_presentation {k A : Type u} [Field k] [CommRing A]
    [Algebra k A]
    (h : ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R)
      (_ : IsLocalRing R) (_ : IsNoetherianRing R),
      IsRegularLocalRing R ∧ Algebra.EssFiniteType k R ∧
        ∃ xs : List R, RingTheory.Sequence.IsRegular R xs ∧
          Nonempty ((R ⧸ Ideal.span (Set.range
            (fun i : Fin xs.length ↦ xs.get i))) ≃ₐ[k] A)) :
    Algebra.IsCompleteIntersectionLocalAlgebra k A := by
  obtain ⟨R, hR, aR, hl, hn, hr, hft, xs, hxs, ⟨e⟩⟩ := h
  rw [← ofList_eq] at e
  have hne : Ideal.ofList xs ≠ ⊤ := by
    intro heq
    exact hxs.top_ne_smul (by simp [heq])
  have : Nontrivial (R ⧸ Ideal.ofList xs) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ Ideal.ofList xs) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalRing A := e.toRingEquiv.isLocalRing
  have : Algebra.EssFiniteType k A :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  refine ⟨inferInstance, inferInstance, R, hR, aR, hr, hft, xs, hxs, ?_, ⟨e⟩⟩
  intro x hx
  apply IsLocalRing.le_maximalIdeal (J := Ideal.ofList xs) ?_ (Ideal.subset_span hx)
  intro heq
  exact hxs.top_ne_smul (by simp [heq])

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem globalCI_equiv {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : Algebra.IsGlobalCompleteIntersection k A) :
    Algebra.IsGlobalCompleteIntersection k B := by
  rcases h with h | ⟨n, c, f, hcn, ⟨ef⟩, hdim⟩
  · exact Or.inl (e.toEquiv.subsingleton_congr.mp h)
  · refine Or.inr ⟨n, c, f, hcn, ⟨ef.trans e⟩, ?_⟩
    rw [← (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).isHomeomorph.topologicalKrullDim_eq]
    exact hdim

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem globalCI_of_relative_field {k : Type u} [Field k] {n c : ℕ}
    (h : Fin c → MvPolynomial (Fin n) k)
    (hh : Algebra.IsRelativeGlobalCompleteIntersectionPresentation h) :
    Algebra.IsGlobalCompleteIntersection k
      (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range h)) := by
  classical
  let B := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range h)
  by_cases hz : Subsingleton B
  · exact Or.inl hz
  have : Nontrivial B := not_subsingleton_iff_nontrivial.mp hz
  let p : Ideal k := ⊥
  let e : p.Fiber B ≃ₐ[k] B :=
    (Algebra.TensorProduct.congr p.algEquivResidueFieldOfField.symm
      (AlgEquiv.refl : B ≃ₐ[k] B)).trans (Algebra.TensorProduct.lid k B)
  have : Nontrivial (p.Fiber B) := e.toEquiv.nontrivial
  obtain ⟨hc, hd⟩ := hh p inferInstance
  refine Or.inr ⟨n, c, h, hc, ⟨AlgEquiv.refl⟩, ?_⟩
  let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  exact (IsHomeomorph.topologicalKrullDim_eq H H.isHomeomorph).symm.trans hd

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem globalCI_relative_tensor {R k B : Type u} [CommRing R] [Field k]
    [CommRing B] [Algebra R k] [Algebra R B] {n c : ℕ}
    (h : Fin c → MvPolynomial (Fin n) R)
    (hh : Algebra.IsRelativeGlobalCompleteIntersectionPresentation h)
    (e : B ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range h))) :
    Algebra.IsGlobalCompleteIntersection k (k ⊗[R] B) := by
  obtain ⟨⟨e₀, _⟩, hbc⟩ := Algebra.relativeGlobalCompleteIntersection_baseChange R k n c h
  have hci := globalCI_of_relative_field _ (hbc hh)
  exact globalCI_equiv (e₀.trans (Algebra.TensorProduct.congr
    (AlgEquiv.refl : k ≃ₐ[k] k) e.symm)) hci

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciLocal_of_globalCI {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (h : Algebra.IsGlobalCompleteIntersection k B)
    (q : Ideal B) [q.IsPrime] :
    Algebra.IsCompleteIntersectionLocalAlgebra k (Localization.AtPrime q) := by
  have hl : Algebra.IsLocalCompleteIntersection k B := by
    refine ⟨{1}, ?_, ?_⟩
    · simp
    · intro g hg
      have hg' : g = 1 := Set.mem_singleton_iff.mp hg
      subst g
      exact Algebra.isGlobalCompleteIntersection_localizationAway k B h 1
  have hc := (lci_pointwise_criterion k (Spec (.of k)) (𝟙 _)).2.2 B
    inferInstance inferInstance inferInstance
  exact ciLocal_presentation ((hc.mp hl) q inferInstance)

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private def ciAt {k : Type u} [Field k] {Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) (z : Z) : Prop :=
  @Algebra.IsCompleteIntersectionLocalAlgebra k (Z.presheaf.stalk z) _ _
    (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      Z.presheaf.germ ⊤ z trivial).hom.toAlgebra)

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciAt_open {k : Type u} [Field k] {Z W : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) (i : W ⟶ Z) [IsOpenImmersion i] (w : W) :
    ciAt (i ≫ s) w ↔ ciAt s (i w) := by
  let : Algebra k (Z.presheaf.stalk (i w)) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      Z.presheaf.germ ⊤ (i w) trivial).hom.toAlgebra)
  let : Algebra k (W.presheaf.stalk w) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ s).appLE ⊤ ⊤ le_top ≫
      W.presheaf.germ ⊤ w trivial).hom.toAlgebra)
  let e : (Z.presheaf.stalk (i w)) ≃ₐ[k] (W.presheaf.stalk w) :=
    AlgEquiv.ofRingEquiv (f := (asIso (i.stalkMap w)).commRingCatIsoToRingEquiv) (by
      intro a
      change (i.stalkMap w) ((Z.presheaf.germ ⊤ (i w) trivial)
        ((s.appLE ⊤ ⊤ le_top) ((Scheme.ΓSpecIso (.of k)).inv a))) = _
      simp only [Scheme.Hom.germ_stalkMap_apply]
      simp [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE])
  exact ⟨ciLocal_equiv e.symm, ciLocal_equiv e⟩

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciAt_comp {k : Type u} [Field k] {Z W : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) (i : W ⟶ Z) [IsOpenImmersion i]
    (t : W ⟶ Spec (.of k)) (ht : i ≫ s = t) (w : W) :
    ciAt t w ↔ ciAt s (i w) := by
  subst t
  exact ciAt_open s i w

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciAt_chart {k : Type u} [Field k] {Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) (U : Z.Opens) (hU : IsAffineOpen U) (z : U) :
    let : Algebra k Γ(Z, U) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U le_top).hom.toAlgebra)
    ciAt s z ↔ Algebra.IsCompleteIntersectionLocalAlgebra k
      (Localization.AtPrime (hU.primeIdealOf z).asIdeal) := by
  dsimp only
  let : Algebra k Γ(Z, U) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U le_top).hom.toAlgebra)
  let : Algebra Γ(Z, U) (Z.presheaf.stalk z) :=
    Z.presheaf.algebra_section_stalk z
  let : Algebra k (Z.presheaf.stalk z) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      Z.presheaf.germ ⊤ z trivial).hom.toAlgebra)
  have : IsScalarTower k Γ(Z, U) (Z.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = Z.presheaf.germ U z z.2
        ((s.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (.of k)).inv a))
      simp [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE,
        TopCat.Presheaf.germ_res_apply]
  have := hU.isLocalization_stalk z
  let e := (IsLocalization.algEquiv (hU.primeIdealOf z).asIdeal.primeCompl
    (Z.presheaf.stalk z) (Localization.AtPrime (hU.primeIdealOf z).asIdeal)).restrictScalars k
  exact ⟨ciLocal_equiv e, ciLocal_equiv e.symm⟩

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciAt_fieldChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z W : Scheme.{u}} (s : Z ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (t : W ⟶ Spec (.of K)) (a : W ⟶ Z)
    (H : IsPullback a t s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (w : W) :
    ciAt t w ↔ ciAt s (a w) := by
  obtain ⟨U, hU, hw, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := a w) (U := ⊤) (by trivial)
  let V := a ⁻¹ᵁ U ⊓ t ⁻¹ᵁ ⊤
  have hV : IsAffineOpen V := by
    have : IsAffine U.toScheme := hU
    have : IsAffine (⊤ : (Spec (.of k)).Opens).toScheme := isAffineOpen_top _
    have : IsAffine (⊤ : (Spec (.of K)).Opens).toScheme := isAffineOpen_top _
    exact IsAffine.of_isIso
      (Scheme.Hom.isPullback_resLE H (UT := ⊤) (US := ⊤)
        (UX := U) le_top le_top (UY := V) rfl).isoPullback.hom
  have hwV : w ∈ V := ⟨hw, trivial⟩
  let B := Γ(Z, U)
  let D := Γ(W, V)
  let β := (Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U le_top
  let δ := (Scheme.ΓSpecIso (.of K)).inv ≫ t.appLE ⊤ V le_top
  let j := a.appLE U V inf_le_left
  let : Algebra k B := β.hom.toAlgebra
  let : Algebra K D := δ.hom.toAlgebra
  let : Algebra B D := j.hom.toAlgebra
  let : Algebra k D := (δ.hom.comp (algebraMap k K)).toAlgebra
  have hscalar : (algebraMap k D) = j.hom.comp β.hom := by
    change (CommRingCat.ofHom (algebraMap k K) ≫ δ).hom = (β ≫ j).hom
    dsimp only [β, δ, j]
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    apply congrArg CommRingCat.Hom.hom
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE]
    rw [H.w, Scheme.Hom.comp_appLE]
    simp
  have : IsScalarTower k K D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k B D := IsScalarTower.of_algebraMap_eq' hscalar
  have hp := (isIso_pushoutSection_iff H (UT := ⊤) (US := ⊤) (UX := U)
    le_top le_top (UY := V) rfl).mp
      (isIso_pushoutSection_of_isAffineOpen H le_top le_top rfl
        (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hp' : IsPushout (CommRingCat.ofHom (algebraMap k K)) β δ j := by
    refine hp.flip.of_iso (Scheme.ΓSpecIso (.of k)) (Scheme.ΓSpecIso (.of K))
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ (by rfl)
    · simp [Scheme.Hom.appLE]
    · simp [β]
    · simp [δ]
  have : Algebra.IsPushout k K B D := CommRingCat.isPushout_iff_isPushout.mp hp'
  let E : (K ⊗[k] B) ≃ₐ[K] D := Algebra.IsPushout.equiv k K B D
  have : Algebra.FiniteType k B := by
    exact (s.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  let qD := (hV.primeIdealOf ⟨w, hwV⟩).asIdeal
  let qE := qD.comap E.toRingHom
  have hq : qE.comap (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom =
      (hU.primeIdealOf ⟨a w, hw⟩).asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV inf_le_left hwV
    change qE.comap _ = _
    rw [← congrArg PrimeSpectrum.asIdeal h]
    ext b
    change E (1 ⊗ₜ[k] b) ∈ qD ↔ j b ∈ qD
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl
  have eLoc := Localization.localAlgEquiv qE qD E rfl
  have hf := Algebra.isCompleteIntersectionLocal_fieldChange k K B qE
  rw [← ciLocal_iff, ← ciLocal_iff] at hf
  let qB := (hU.primeIdealOf ⟨a w, hw⟩).asIdeal
  let eBase := Localization.localAlgEquiv
    (qE.comap (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom)
    qB (AlgEquiv.refl : B ≃ₐ[k] B) (hq.trans (by ext b; rfl))
  have hb : Algebra.IsCompleteIntersectionLocalAlgebra k
      (Localization.AtPrime qB) ↔ Algebra.IsCompleteIntersectionLocalAlgebra K
        (Localization.AtPrime qE) :=
    (Iff.intro (ciLocal_equiv eBase.symm) (ciLocal_equiv eBase)).trans hf
  exact (ciAt_chart t V hV ⟨w, hwV⟩).trans
    ((Iff.intro (ciLocal_equiv eLoc.symm) (ciLocal_equiv eLoc)).trans
      (hb.symm.trans (ciAt_chart s U hU ⟨a w, hw⟩).symm))

/-- The points `x` whose local ring in the fibre over `f x` is a complete intersection
over `κ(f x)`. The canonical point `f.asFiber x` is provided by the fibre homeomorphism.
Source: Stacks Project, Morphisms, Tag 02V3 (lemma-set-points-where-fibres-lci)
(blueprint: lem-trf-syntomic-locus-base-change). -/
def Scheme.Hom.fiberCompleteIntersectionLocus {X S : Scheme.{u}} (f : X ⟶ S) : Set X :=
  {x | f.IsCompleteIntersectionAtFiberPoint (f x) (f.asFiber x)}

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem fiberPoint_iff_locus {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (s : S) (hs : f x = s) (y : f.fiber s) (hy : f.fiberι s y = x) :
    f.IsCompleteIntersectionAtFiberPoint s y ↔ x ∈ f.fiberCompleteIntersectionLocus := by
  subst s
  have he : y = f.asFiber x := (f.fiberι _).isEmbedding.injective
    (hy.trans (f.fiberι_asFiber x).symm)
  subst y
  rfl

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ciAt_of_relative_chart {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (eUV : U ≤ f ⁻¹ᵁ V) (n c : ℕ) (rels : Fin c → MvPolynomial (Fin n) Γ(S, V))
    (hr : Algebra.IsRelativeGlobalCompleteIntersectionPresentation rels)
    (E : @AlgEquiv Γ(S, V) Γ(X, U)
      (MvPolynomial (Fin n) Γ(S, V) ⧸ Ideal.span (Set.range rels))
      _ _ _ (f.appLE V U eUV).hom.toAlgebra _) :
    (U : Set X) ⊆ f.fiberCompleteIntersectionLocus := by
  intro x hx
  let s := f x
  let k := S.residueField s
  let Z := f.fiber s
  let t := f.fiberToSpecResidueField s
  let a := f.fiberι s
  let g := S.fromSpecResidueField s
  let W := a ⁻¹ᵁ U ⊓ t ⁻¹ᵁ ⊤
  have htop : (⊤ : (Spec k).Opens) ≤ g ⁻¹ᵁ V := by
    intro y _
    change g y ∈ V
    simpa [g, s] using eUV hx
  have H : IsPullback a t f g := IsPullback.of_hasPullback f g
  have hW : IsAffineOpen W := by
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    have : IsAffine (⊤ : (Spec k).Opens).toScheme := isAffineOpen_top _
    exact IsAffine.of_isIso (Scheme.Hom.isPullback_resLE H htop eUV rfl).isoPullback.hom
  let R := Γ(S, V)
  let B := Γ(X, U)
  let D := Γ(Z, W)
  let α := f.appLE V U eUV
  let β := g.appLE V ⊤ htop ≫ (Scheme.ΓSpecIso k).hom
  let δ := (Scheme.ΓSpecIso k).inv ≫ t.appLE ⊤ W inf_le_right
  let j := a.appLE U W inf_le_left
  let : Algebra R B := α.hom.toAlgebra
  let : Algebra R k := β.hom.toAlgebra
  let : Algebra k D := δ.hom.toAlgebra
  let : Algebra B D := j.hom.toAlgebra
  let : Algebra R D := (j.hom.comp α.hom).toAlgebra
  have hscalar : (algebraMap R D) = δ.hom.comp β.hom := by
    change (α ≫ j).hom = (β ≫ δ).hom
    dsimp only [α, β, δ, j]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply congrArg CommRingCat.Hom.hom
    have hc := Scheme.Hom.appLE_comp_appLE a f V U W eUV inf_le_left
    have hd := Scheme.Hom.appLE_comp_appLE t g V ⊤ W htop inf_le_right
    have hm : (a ≫ f).appLE V W
        (inf_le_left.trans ((TopologicalSpace.Opens.map a.base).map (homOfLE eUV)).le) =
        (t ≫ g).appLE V W
        (inf_le_right.trans ((TopologicalSpace.Opens.map t.base).map (homOfLE htop)).le) := by
      congr 1
      exact H.w
    exact hc.trans (hm.trans hd.symm)
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R k D := IsScalarTower.of_algebraMap_eq' hscalar
  have hp := (isIso_pushoutSection_iff H htop eUV (UY := W) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H htop eUV rfl hV (isAffineOpen_top _) hU)
  have hp' : IsPushout β α δ j := by
    refine hp.flip.of_iso (Iso.refl _) (Scheme.ΓSpecIso k)
      (Iso.refl _) (Iso.refl _) ?_ (by simp [α]) ?_ (by rfl)
    · simp [β]
    · simp [δ]
  have : Algebra.IsPushout R k B D := CommRingCat.isPushout_iff_isPushout.mp hp'
  let eT : (k ⊗[R] B) ≃ₐ[k] D := Algebra.IsPushout.equiv R k B D
  have hD : Algebra.IsGlobalCompleteIntersection k D :=
    globalCI_equiv eT (globalCI_relative_tensor rels hr E)
  have : Algebra.FiniteType R B :=
    Algebra.FiniteType.equiv inferInstance E.symm
  have : Algebra.FiniteType k D := Algebra.FiniteType.equiv inferInstance eT
  have hy : f.asFiber x ∈ W := by
    refine ⟨?_, trivial⟩
    change f.fiberι (f x) (f.asFiber x) ∈ U
    rwa [f.fiberι_asFiber]
  exact (ciAt_chart t W hW ⟨f.asFiber x, hy⟩).mpr
    (ciLocal_of_globalCI hD _)

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem fiberPoint_open {X S W : Scheme.{u}} (f : X ⟶ S)
    (i : W ⟶ X) [IsOpenImmersion i] (s : S) (y : (i ≫ f).fiber s) :
    (i ≫ f).IsCompleteIntersectionAtFiberPoint s y ↔
      i ((i ≫ f).fiberι s y) ∈ f.fiberCompleteIntersectionLocus := by
  let e := pullbackRightPullbackFstIso f (S.fromSpecResidueField s) i
  let a : (i ≫ f).fiber s ⟶ f.fiber s := e.inv ≫ pullback.snd i (f.fiberι s)
  have : IsOpenImmersion a := by dsimp [a]; infer_instance
  have ha : a ≫ f.fiberToSpecResidueField s = (i ≫ f).fiberToSpecResidueField s :=
    pullbackRightPullbackFstIso_inv_snd_snd f (S.fromSpecResidueField s) i
  have h := ciAt_comp (f.fiberToSpecResidueField s) a
    ((i ≫ f).fiberToSpecResidueField s) ha y
  have hs : f (i ((i ≫ f).fiberι s y)) = s := by
    have hpt := congrArg (fun q : (i ≫ f).fiber s ⟶ S ↦ q y) ((i ≫ f).fiber_fac s)
    simpa [Scheme.Hom.comp_apply] using hpt
  have hp : f.fiberι s (a y) = i ((i ≫ f).fiberι s y) := by
    change (a ≫ f.fiberι s) y = _
    exact congrArg (fun q : (i ≫ f).fiber s ⟶ X ↦ q y)
      (pullbackRightPullbackFstIso_inv_snd_fst f (S.fromSpecResidueField s) i)
  exact h.trans (fiberPoint_iff_locus f _ s hs _ hp)

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem fibers_open_iff {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) :
    (U.ι ≫ f).HasCompleteIntersectionFibres ↔
      (U : Set X) ⊆ f.fiberCompleteIntersectionLocus := by
  constructor
  · intro h x hx
    have hc := h ((U.ι ≫ f) ⟨x, hx⟩) ((U.ι ≫ f).asFiber ⟨x, hx⟩)
    have hi := (fiberPoint_open f U.ι _ _).mp hc
    have he := (U.ι ≫ f).fiberι_asFiber ⟨x, hx⟩
    exact (congrArg (fun z : U.toScheme ↦ U.ι z ∈ f.fiberCompleteIntersectionLocus) he).mp hi
  · intro h s y
    apply (fiberPoint_open f U.ι s y).mpr
    exact h ((U.ι ≫ f).fiberι s y).property

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem locus_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (T : Scheme.{u}) (g : T ⟶ S) :
    (pullback.snd f g).fiberCompleteIntersectionLocus =
      (pullback.fst f g) ⁻¹' f.fiberCompleteIntersectionLocus := by
  ext x
  let y := (pullback.snd f g) x
  let z := (pullback.fst f g) x
  let a := pullback.map (pullback.snd f g) (T.fromSpecResidueField y)
    f (S.fromSpecResidueField (g y)) (pullback.fst f g)
    (Spec.map (g.residueFieldMap y)) g pullback.condition.symm (by simp)
  have H := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y
  let : Algebra (S.residueField (g y)) (T.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g y))))
  have h := ciAt_fieldChange (k := (S.residueField (g y)))
    (K := (T.residueField y)) (f.fiberToSpecResidueField (g y))
    ((pullback.snd f g).fiberToSpecResidueField y) a H
    ((pullback.snd f g).asFiber x)
  have haz : f.fiberι (g y) (a ((pullback.snd f g).asFiber x)) = z := by
    change (a ≫ f.fiberι (g y)) ((pullback.snd f g).asFiber x) = z
    have ha : a ≫ f.fiberι (g y) =
        (pullback.snd f g).fiberι y ≫ pullback.fst f g := pullback.lift_fst _ _ _
    rw [ha, Scheme.Hom.comp_apply]
    exact congrArg (pullback.fst f g) ((pullback.snd f g).fiberι_asFiber x)
  have hbase : f z = g y := congrArg (fun q : pullback f g ⟶ S ↦ q x) pullback.condition
  exact h.trans (fiberPoint_iff_locus f z (g y) hbase _ haz)

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem locus_isOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] : IsOpen f.fiberCompleteIntersectionLocus := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := f x) (U := ⊤) (by trivial)
  obtain ⟨U₀, hU₀, hxU₀, he₀⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := f ⁻¹ᵁ V) hxV
  have hfp : ∃ (U₀ : X.Opens) (V₀ : S.Opens),
      IsAffineOpen U₀ ∧ IsAffineOpen V₀ ∧ x ∈ U₀ ∧
        ∃ e₀ : U₀ ≤ f ⁻¹ᵁ V₀, (f.appLE V₀ U₀ e₀).hom.FinitePresentation :=
    ⟨U₀, V, hU₀, hV, hxU₀, he₀, f.finitePresentation_appLE hV hU₀ he₀⟩
  let : Algebra (S.residueField (f x))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    (((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
      (f.fiberToSpecResidueField (f x)).appLE ⊤ ⊤ le_top ≫
      (f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) trivial).hom.toAlgebra)
  obtain ⟨U, hU, hxU, e, n, c, rels, hr, ⟨E⟩⟩ :=
    syntomic_pointwise_local_model f x V hV hxV hfp
      ((Flat.iff_flat_stalkMap f).mp inferInstance x) (ciLocal_to_presentation hx)
  exact Filter.mem_of_superset (U.isOpen.mem_nhds hxU)
    (ciAt_of_relative_chart f U V hU hV e n c rels hr E)

set_option backward.isDefEq.respectTransparency false in
/-- Formation of the fibrewise complete-intersection locus commutes with arbitrary base
change for locally finite type morphisms. If the morphism is also flat and locally of
finite presentation, this subset is an open, and is the largest source open on which the
restriction is flat, locally of finite presentation, and has complete-intersection fibres.

Source: Stacks Project, Morphisms, Tag 02V3 (lemma-set-points-where-fibres-lci),
including its last assertion, using Algebra Tag 00SI and Morphisms Tag 01UE
(blueprint: lem-trf-syntomic-locus-base-change).

Proof:
1. Around a point over `s`, choose finite-type affine charts `Spec B → Spec A` by
   def-weil-finite-type-morphism. The fibre chart is `Spec (B ⊗[A] κ(s))` by
   lem-weil-pbc-open-preimage-fibre-product and lem-weil-pbc-fibre-product-affine-spectra.
   The images of the finite algebra generators of `B` generate this fibre algebra.
2. For any base change, lem-weil-pbc-fibre-of-base-change identifies the new fibre with
   the old fibre extended from `κ(s)` to `κ(s')`. On the affine charts from step 1,
   lem-weil-pbc-affine-open-stalk-localization identifies the fibre local rings with
   localizations at corresponding primes. Apply lem-trf-lci-field-change-local to obtain
   pointwise equivalence of the local-ring conditions, hence equality of the two loci.
3. Now suppose flatness and local finite presentation. At a point of the locus,
   lem-trf-syntomic-pointwise-local-model gives an affine neighbourhood presented as a
   relative global complete intersection over an affine neighbourhood of the base point.
4. By lem-weil-pbc-relative-global-complete-intersection-base-change, scalar extension
   of the chart to a residue field is still a relative global complete intersection.
   Its fibre over the zero prime of that field identifies it as a global complete
   intersection by def-weil-pbc-complete-intersection-over-field. Principal localization
   preserves that condition by lem-weil-pbc-global-complete-intersection-principal-localization.
   Thus the single principal open `D(1)` makes it a local complete intersection, and
   lem-trf-lci-pointwise-criterion makes every fibre local ring a complete intersection.
   Open immersion stalks are unchanged, so the whole chart lies in the locus. These charts
   cover the locus, proving openness.
5. For a source open `H`, its fibres are the corresponding opens in the original fibres by
   lem-weil-pbc-open-preimage-fibre-product, with the same local rings. Hence its fibre
   condition holds exactly when `H` lies in the locus. Flatness restricts since the local
   maps are unchanged. Local finite presentation restricts by passing to principal affine
   neighbourhoods: localizing `B = A[t]/(h)` at `b` adds one generator and the relation
   `bu - 1`. Apply these facts to the locus itself, and then to any competing source open,
   obtaining its three properties and largestness. Empty fibres and the empty source have
   no local rings to test, so the same argument includes them.
-/
theorem syntomic_locus_base_change {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    (∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      (pullback.snd f g).fiberCompleteIntersectionLocus =
        (pullback.fst f g) ⁻¹' f.fiberCompleteIntersectionLocus) ∧
    (Flat f → LocallyOfFinitePresentation f →
      ∃ U : X.Opens, (U : Set X) = f.fiberCompleteIntersectionLocus ∧
        IsGreatest {V : X.Opens | Flat (V.ι ≫ f) ∧
          LocallyOfFinitePresentation (V.ι ≫ f) ∧
          (V.ι ≫ f).HasCompleteIntersectionFibres} U) := by
  refine ⟨locus_baseChange f, ?_⟩
  intro hf hfp
  let U : X.Opens := ⟨f.fiberCompleteIntersectionLocus, locus_isOpen f⟩
  refine ⟨U, rfl, ?_, ?_⟩
  · exact ⟨inferInstance, inferInstance, (fibers_open_iff f U).mpr (by rfl)⟩
  · intro V hV
    exact (fibers_open_iff f V).mp hV.2.2

end AlgebraicGeometry
