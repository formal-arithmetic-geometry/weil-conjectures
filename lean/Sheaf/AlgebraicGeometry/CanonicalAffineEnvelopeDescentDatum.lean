/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.QuasiAffineBaseChange

/-!
# The canonical affine envelope and descent

Source: Stacks Project, Descent, Tag 0247, proof of lemma-quasi-affine, second paragraph
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

The ring pushouts below are tensor products, with their canonical two inclusions.
All maps are constructed from global sections, the adjunction unit, and pullback maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

namespace CanonicalAffineEnvelope

/-- The canonical map from the affine envelope to its affine base (Stacks 0247)
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def map {V A : Scheme.{u}} [IsAffine A] (f : V ⟶ A) :
    Spec Γ(V, ⊤) ⟶ A :=
  Spec.map f.appTop ≫ A.isoSpec.inv

/-- The adjunction unit as a morphism over the affine base (Stacks 0247)
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def unit {V A : Scheme.{u}} [IsAffine A] (f : V ⟶ A) :
    Over.mk f ⟶ Over.mk (map f) :=
  Over.homMk V.toSpecΓ (by
    change V.toSpecΓ ≫ (Spec.map f.appTop ≫ A.isoSpec.inv) = f
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    simp [Scheme.isoSpec])

/-- The section-product comparison, using the tensor product's pushout presentation (Stacks
0247, flat-base-change display; Tag 02KH)
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def comparison {V A T : Scheme.{u}} (f : V ⟶ A) (q : T ⟶ A) :
    pushout f.appTop q.appTop ⟶ Γ(pullback f q, ⊤) :=
  pushout.desc (pullback.fst f q).appTop (pullback.snd f q).appTop (by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition])

/-- The affine tensor-product identification, with both projections fixed by the pushout
inclusions. Source: Stacks 0247, affine overlap; Tags 01I4/01JQ.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def affineTensorMap {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) (q : T ⟶ A) :
    Spec (pushout f.appTop q.appTop) ⟶ pullback (map f) q :=
  pullback.lift (Spec.map (pushout.inl f.appTop q.appTop))
    (Spec.map (pushout.inr f.appTop q.appTop) ≫ T.isoSpec.inv) (by
      dsimp [map]
      rw [← Category.assoc, ← Spec.map_comp, pushout.condition, Spec.map_comp,
        Category.assoc, Scheme.isoSpec_inv_naturality]
      exact (Category.assoc _ _ _).symm)

/-- The base change of the canonical open embedding (Stacks 0247)
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def unitBaseChange {V A T : Scheme.{u}} [IsAffine A]
    (f : V ⟶ A) (q : T ⟶ A) :
    pullback f q ⟶ pullback (map f) q :=
  ((Over.pullback q).map (unit f)).left

/-- The canonical map from the spectrum of the base-changed sections to the base-changed
spectrum. Its inverse is the comparison called alpha in Stacks 0247.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def spectrumComparison {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) (q : T ⟶ A) :
    Spec Γ(pullback f q, ⊤) ⟶ pullback (map f) q :=
  Spec.map (unitBaseChange f q).appTop ≫ (pullback (map f) q).isoSpec.inv

/-- The isomorphism of the two pullbacks represented by a transport datum, expressed as a
morphism over the common base. For the two projections of the double overlap this is phi.
Source: Stacks 023V, 0247 (blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def transition {A B T : Scheme.{u}} (p : A ⟶ B) (V : Over A)
    (D : Over.DescentDatum p V) (a b : T ⟶ A) (h : a ≫ p = b ≫ p) :
    (Over.pullback a).obj V ⟶ (Over.pullback b).obj V :=
  Over.homMk (pullback.lift
    (D.transport (pullback.fst V.hom a ≫ V.hom) (pullback.snd V.hom a ≫ b)
      ((congrArg (fun k : pullback V.hom a ⟶ A ↦ k ≫ p)
        (pullback.condition (f := V.hom) (g := a))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k : T ⟶ B ↦ pullback.snd V.hom a ≫ k) h).trans
            (Category.assoc _ _ _).symm)))
      (Over.homMk (pullback.fst V.hom a) rfl)).left
    (pullback.snd V.hom a)
    (Over.w (D.transport _ _ _ (Over.homMk (pullback.fst V.hom a) rfl))))

private theorem affineTensorMap_isIso {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) (q : T ⟶ A) : IsIso (affineTensorMap f q) := by
  have H : IsPullback (Spec.map (pushout.inl f.appTop q.appTop))
      (Spec.map (pushout.inr f.appTop q.appTop) ≫ T.isoSpec.inv) (map f) q :=
    (isPullback_SpecMap_pushout f.appTop q.appTop).of_iso
      (Iso.refl _) (Iso.refl _) T.isoSpec.symm A.isoSpec.symm
      (by simp) (by simp) (by simp [map]) (by simp [Scheme.isoSpec_inv_naturality])
  exact inferInstanceAs (IsIso H.isoPullback.hom)

private theorem spectrumComparison_fst {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) (q : T ⟶ A) :
    spectrumComparison f q ≫ pullback.fst (map f) q =
      Spec.map (pullback.fst f q).appTop := by
  unfold spectrumComparison
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
    ← Spec.map_comp, ← Scheme.Hom.comp_appTop]
  simp [unitBaseChange, unit, Scheme.toSpecΓ_appTop,
    Spec.map_comp, Scheme.isoSpec]

private theorem spectrumComparison_snd {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) (q : T ⟶ A) :
    spectrumComparison f q ≫ pullback.snd (map f) q =
      Spec.map (pullback.snd f q).appTop ≫ T.isoSpec.inv := by
  unfold spectrumComparison
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
    ← Spec.map_comp, ← Scheme.Hom.comp_appTop]
  simp [unitBaseChange]

private theorem spectrumComparison_factor {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) (q : T ⟶ A) :
    spectrumComparison f q = Spec.map (comparison f q) ≫ affineTensorMap f q := by
  apply pullback.hom_ext
  · rw [spectrumComparison_fst]
    simp [affineTensorMap, ← Spec.map_comp, comparison]
  · rw [spectrumComparison_snd]
    simp [affineTensorMap, ← Spec.map_comp_assoc, comparison]

/-- Canonical envelope and flat base change: the section-product comparison beta and its
spectrum comparison are isomorphisms. Source: Stacks 0247, second paragraph; Tag 02KH.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

Proof: the whole affine open of A makes V quasi-affine. By
lem-trf-quasi-affine-canonical-affine-embedding, V is qcqs and its adjunction unit is open.
Apply lem-weil-pbc-flat-base-change-global-sections-qcqs to f and q. The comparison is exactly
its section-product map, represented by the ring pushout. The affine fibre-product formula
lem-weil-pbc-fibre-product-affine-spectra identifies its spectrum map with spectrumComparison,
using the two projection identities for unitBaseChange. Hence that map is an isomorphism too.
No finite-presentation hypothesis is used. -/
theorem baseChange {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) [IsQuasiAffineHom f] (q : T ⟶ A) [Flat q] :
    IsIso (comparison f q) ∧ IsIso (spectrumComparison f q) := by
  have : V.IsQuasiAffine := .of_isQuasiAffineHom f
  have H := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f q) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    le_top le_top (by simp) (isAffineOpen_top _) (isAffineOpen_top _)
    isCompact_univ isQuasiSeparated_univ
  have happ {X Y : Scheme.{u}} (g : X ⟶ Y) (e) : g.appLE ⊤ ⊤ e = g.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hpo : IsPushout f.appTop q.appTop (pullback.fst f q).appTop
      (pullback.snd f q).appTop := by
    have H' := (isIso_pushoutSection_iff ..).mp H
    simpa only [happ] using H'
  have : IsIso (comparison f q) := inferInstanceAs (IsIso hpo.isoPushout.inv)
  refine ⟨this, ?_⟩
  rw [spectrumComparison_factor]
  have := affineTensorMap_isIso f q
  infer_instance

/-- The inverse spectrum comparison alpha of Stacks 0247, with its inverse fixed by the actual
section-product comparison, rather than a choice of isomorphism.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def alpha {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) [IsQuasiAffineHom f] (q : T ⟶ A) [Flat q] :
    pullback (map f) q ≅ Spec Γ(pullback f q, ⊤) :=
  letI : IsIso (spectrumComparison f q) := (baseChange f q).2
  (asIso (spectrumComparison f q)).symm

/-- Conjugation of the spectrum of the section map of phi by alpha. Source: Stacks 0247,
second paragraph (blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def extendedTransition {A B V T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (p : A ⟶ B) (f : V ⟶ A) [IsQuasiAffineHom f] (D : Over.DescentDatum p (Over.mk f))
    (a b : T ⟶ A) [Flat a] [Flat b] (h : a ≫ p = b ≫ p) :
    pullback (map f) a ⟶ pullback (map f) b :=
  (alpha f a).hom ≫ Spec.map (transition p (Over.mk f) D a b h).left.appTop ≫ (alpha f b).inv

/-- The section-product rule for beta; the product of the two pushout inclusions represents a
pure tensor. Source: Stacks 0247, flat-base-change display; Tag 02KH.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

Proof: comparison is the map of the pushout induced by the two projections. Its restrictions
to the two factors are the section pullbacks. Multiplicativity gives the displayed formula,
which is c tensor t mapping to the product of its two pullbacks. -/
theorem comparison_apply {V A T : Scheme.{u}} (f : V ⟶ A) (q : T ⟶ A)
    (c : Γ(V, ⊤)) (t : Γ(T, ⊤)) :
    comparison f q (pushout.inl f.appTop q.appTop c * pushout.inr f.appTop q.appTop t) =
      (pullback.fst f q).appTop c * (pullback.snd f q).appTop t := by
  simp only [comparison, map_mul, ← ConcreteCategory.comp_apply, pushout.inl_desc,
    pushout.inr_desc]

/-- Alpha identifies the pullback of the canonical embedding with the canonical adjunction
unit after base change, over the new affine base. Source: Stacks 0247, second paragraph.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

Proof: the projection identities give j_i sharp = beta_i, by their restrictions to both
factors of the tensor product. Therefore alpha_i j_i has section map beta_i beta_i inverse,
and is the adjunction unit by lem-weil-pbc-morphism-into-affine-scheme. The second projection
identity is preserved by the affine spectrum identification, so alpha is over T. -/
theorem alpha_properties {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) [IsQuasiAffineHom f] (q : T ⟶ A) [Flat q] :
    unitBaseChange f q ≫ (alpha f q).hom = (pullback f q).toSpecΓ ∧
      (alpha f q).inv ≫ pullback.snd (map f) q =
        Spec.map (pullback.snd f q).appTop ≫ T.isoSpec.inv := by
  have : IsIso (spectrumComparison f q) := (baseChange f q).2
  constructor
  · rw [← cancel_mono (spectrumComparison f q)]
    simp [alpha, spectrumComparison, ← Scheme.toSpecΓ_naturality_assoc]
  · exact spectrumComparison_snd f q

/-- The spectrum comparison is precisely Spec beta followed by the affine tensor-product
identification. Source: Stacks 0247, second paragraph; Tags 01I4/01JQ and 02KH.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

Proof: affineTensorMap is the affine fibre-product isomorphism by
lem-weil-pbc-fibre-product-affine-spectra. The two projection identities and the definition
of comparison show that both morphisms on the right have the section map of unitBaseChange.
The Hom bijection into an affine scheme then gives the equality. -/
theorem spectrumComparison_eq {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (f : V ⟶ A) (q : T ⟶ A) :
    IsIso (affineTensorMap f q) ∧
      spectrumComparison f q = Spec.map (comparison f q) ≫ affineTensorMap f q := by
  exact ⟨affineTensorMap_isIso f q, spectrumComparison_factor f q⟩

/-- The map on tensor products induced by a morphism over the base, fixing the second factor.
Source: Stacks 0247, naturality of flat base change.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum). -/
noncomputable def tensorMap {A T : Scheme.{u}} (V Z : Over A) (e : V ⟶ Z) (q : T ⟶ A) :
    pushout Z.hom.appTop q.appTop ⟶ pushout V.hom.appTop q.appTop :=
  pushout.desc (e.left.appTop ≫ pushout.inl V.hom.appTop q.appTop)
    (pushout.inr V.hom.appTop q.appTop) (by
      rw [← Category.assoc, ← Scheme.Hom.comp_appTop, Over.w e, pushout.condition])

/-- Naturality of beta, in particular for the pullbacks of phi on the triple overlap.
Source: Stacks 0247, second paragraph, cocycle assertion.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

Proof: restrict both ring maps to each pushout inclusion. On the first factor the equality
is functoriality of the first projection's section pullback. On the second it is the identity
on sections pulled back from T. The pushout universal property gives equality on all tensors.
For e a pullback of phi this reads theta' lambda_1 = lambda_0 (theta tensor 1), as in the
node's proof Step 6. No flatness is needed for this equality of canonical maps. -/
theorem comparison_naturality {A T : Scheme.{u}} (V Z : Over A) (e : V ⟶ Z) (q : T ⟶ A) :
    tensorMap V Z e q ≫ comparison V.hom q =
      comparison Z.hom q ≫ ((Over.pullback q).map e).left.appTop := by
  apply pushout.hom_ext
  · simp only [tensorMap, comparison, pushout.inl_desc_assoc, pushout.inl_desc,
      Category.assoc]
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    congr 1
    simp
  · simp only [tensorMap, comparison, pushout.inr_desc_assoc, pushout.inr_desc]
    rw [← Scheme.Hom.comp_appTop]
    congr 1
    simp

/-- The comparisons on a successive flat affine base change are isomorphisms and agree with
direct base change. The displayed generator is (c tensor s) tensor t.
Source: Stacks 0247, second paragraph, naturality and cocycle; Tag 02KH.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

Proof: lem-trf-quasi-affine-base-change makes the first pullback quasi-affine. The target of
that morphism is affine, so it is qcqs by lem-trf-quasi-affine-canonical-affine-embedding.
Apply lem-weil-pbc-flat-base-change-global-sections-qcqs to r for the isomorphism clause.
For the equality, both sides pull c, s, t back to the triple fibre product and multiply them.
The canonical pasting isomorphism respects both projections, so the equality follows from
functoriality of sections and associativity of multiplication. The pushout inclusions generate
the iterated tensor product, so this generator identity is the full comparison compatibility.
In particular the intermediate section algebra is independent of the chosen pair of the
three overlap coordinates. -/
theorem comparison_successive {V A T U : Scheme.{u}} [IsAffine A] [IsAffine T] [IsAffine U]
    (f : V ⟶ A) [IsQuasiAffineHom f] (q : T ⟶ A) [Flat q] (r : U ⟶ T) [Flat r] :
    IsIso (comparison (pullback.snd f q) r) ∧
      ∀ (c : Γ(V, ⊤)) (s : Γ(T, ⊤)) (t : Γ(U, ⊤)),
        comparison (pullback.snd f q) r
          (pushout.inl (pullback.snd f q).appTop r.appTop
            (comparison f q
              (pushout.inl f.appTop q.appTop c * pushout.inr f.appTop q.appTop s)) *
            pushout.inr (pullback.snd f q).appTop r.appTop t) =
          (pullbackLeftPullbackSndIso f q r).hom.appTop
            (comparison f (r ≫ q)
              (pushout.inl f.appTop (r ≫ q).appTop c *
                pushout.inr f.appTop (r ≫ q).appTop (r.appTop s * t))) := by
  have : IsQuasiAffineHom (pullback.snd f q) :=
    isQuasiAffineHom_baseChange f q inferInstance
  refine ⟨(baseChange (pullback.snd f q) r).1, ?_⟩
  intro c s t
  rw [comparison_apply, comparison_apply, comparison_apply]
  simp only [map_mul]
  have hf : (pullback.fst (pullback.snd f q) r).appTop ((pullback.fst f q).appTop c) =
      (pullbackLeftPullbackSndIso f q r).hom.appTop ((pullback.fst f (r ≫ q)).appTop c) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      pullbackLeftPullbackSndIso_hom_fst]
  have hs : (pullback.fst (pullback.snd f q) r).appTop ((pullback.snd f q).appTop s) =
      (pullbackLeftPullbackSndIso f q r).hom.appTop
        ((pullback.snd f (r ≫ q)).appTop (r.appTop s)) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
      pullbackLeftPullbackSndIso_hom_snd, pullback.condition]
  have ht : (pullback.snd (pullback.snd f q) r).appTop t =
      (pullbackLeftPullbackSndIso f q r).hom.appTop ((pullback.snd f (r ≫ q)).appTop t) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      pullbackLeftPullbackSndIso_hom_snd]
  rw [hf, hs, ht, mul_assoc]

private theorem cancel_into_affine {U X Y : Scheme.{u}} [IsAffine Y]
    (i : U ⟶ X) [IsIso i.appTop] {g h : X ⟶ Y} (e : i ≫ g = i ≫ h) : g = h := by
  apply ext_of_isAffine
  apply (cancel_mono i.appTop).mp
  simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop e

private noncomputable def extend {U X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (i : U ⟶ X) [IsIso i.appTop] (g : U ⟶ Y) : X ⟶ Y :=
  X.isoSpec.hom ≫ Spec.map (g.appTop ≫ inv i.appTop) ≫ Y.isoSpec.inv

private theorem extend_fac {U X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (i : U ⟶ X) [IsIso i.appTop] (g : U ⟶ Y) : i ≫ extend i g = g := by
  change i ≫ (X.toSpecΓ ≫ Spec.map (g.appTop ≫ inv i.appTop) ≫ Y.isoSpec.inv) = g
  rw [← Category.assoc i, Scheme.toSpecΓ_naturality]
  simp only [Category.assoc, Spec.map_comp]
  rw [← Spec.map_comp_assoc, IsIso.inv_hom_id, Spec.map_id, Category.id_comp,
    ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

private theorem comparison_isIso {V A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    [CompactSpace V] [QuasiSeparatedSpace V] (f : V ⟶ A) (q : T ⟶ A) [Flat q] :
    IsIso (comparison f q) := by
  have H := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f q) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    le_top le_top (by simp) (isAffineOpen_top _) (isAffineOpen_top _)
    isCompact_univ isQuasiSeparated_univ
  have happ {X Y : Scheme.{u}} (g : X ⟶ Y) (e) : g.appLE ⊤ ⊤ e = g.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hpo : IsPushout f.appTop q.appTop (pullback.fst f q).appTop
      (pullback.snd f q).appTop := by
    have H' := (isIso_pushoutSection_iff ..).mp H
    simpa only [happ] using H'
  exact inferInstanceAs (IsIso hpo.isoPushout.inv)

private theorem pullback_appTop_isIso {A T : Scheme.{u}} [IsAffine A] [IsAffine T]
    (V Z : Over A) [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    (e : V ⟶ Z) [IsIso e.left.appTop] (q : T ⟶ A) [Flat q] :
    IsIso ((Over.pullback q).map e).left.appTop := by
  have : IsIso (tensorMap V Z e q) := by
    change IsIso (pushout.map Z.hom.appTop q.appTop V.hom.appTop q.appTop
      e.left.appTop (𝟙 _) (𝟙 _) (by simp [← Scheme.Hom.comp_appTop]) (by simp))
    infer_instance
  have := comparison_isIso V.hom q
  have := comparison_isIso Z.hom q
  have H := comparison_naturality V Z e q
  have : IsIso (comparison Z.hom q ≫ ((Over.pullback q).map e).left.appTop) := by
    rw [← H]
    infer_instance
  exact IsIso.of_isIso_comp_left (comparison Z.hom q) _

/-- The canonical affine envelope with its induced descent datum. The formula holds on every
flat affine overlap, in particular on A times_B A and its three pullbacks to A cubed_B.
Source: Stacks 0247, proof of lemma-quasi-affine, second paragraph.
(blueprint: lem-trf-canonical-affine-envelope-descent-datum).

Proof:
1. Apply lem-trf-quasi-affine-canonical-affine-embedding over the affine base A: V is qcqs,
   j is open, and unit is over A by lem-weil-pbc-morphism-into-affine-scheme. Both spectra
   are affine, so lem-weil-pbc-morphism-affine-schemes-affine applies to map f.
2. The projections of A times_B A are flat by lem-weil-pbc-flat-morphism-base-change and
   their source is affine by lem-weil-pbc-fibre-product-affine-spectra. Apply baseChange.
3. The section map of j_i is beta_i, by the pullback projection identities; alpha_properties
   identifies j_i with the canonical map into the spectrum of its own sections.
4. Conjugate Spec of phi sharp by alpha. Its ring map is beta_0 inverse phi sharp beta_1.
   It is linear over the overlap ring. The equality beta_0 delta = phi sharp beta_1 and
   lem-weil-pbc-morphism-into-affine-scheme give equivariance of j.
5. The maps A cubed_B to A times_B A are flat base changes of p, and affine. By
   lem-trf-quasi-affine-base-change their V pullbacks are quasi-affine; apply baseChange again.
6. On a pure tensor, functoriality of the pullback square gives
   phi' sharp (lambda_1(c tensor t)) = lambda_0(phi sharp c tensor t).
7. Successive base change sends (c tensor s) tensor t to the product of the three sections;
   tensor associativity therefore identifies the direct and successive comparisons.
8. Taking sections reverses the cocycle of phi. Contravariance of Spec reverses it again,
   giving psi_02 = psi_12 composed with psi_01. The resulting datum is natural on points
   and intertwines j, as asserted. No finite-presentation assumption enters. -/
theorem exists_descentDatum {A B V : Scheme.{u}} [IsAffine A] [IsAffine B]
    (p : A ⟶ B) [Flat p] [Surjective p] (f : V ⟶ A) [IsQuasiAffineHom f]
    (D : Over.DescentDatum p (Over.mk f)) :
    CompactSpace V ∧ QuasiSeparatedSpace V ∧ IsAffineHom (map f) ∧
      IsOpenImmersion V.toSpecΓ ∧
      ∃ E : Over.DescentDatum p (Over.mk (map f)),
        (∀ (T : Scheme.{u}) (a b : T ⟶ A) (h : a ≫ p = b ≫ p)
          (x : Over.mk a ⟶ Over.mk f),
          (E.transport a b h (x ≫ unit f)).left = (D.transport a b h x).left ≫ V.toSpecΓ) ∧
        (∀ (T : Scheme.{u}) [IsAffine T] (a b : T ⟶ A) [Flat a] [Flat b]
          (h : a ≫ p = b ≫ p),
          (transition p (Over.mk (map f)) E a b h).left = extendedTransition p f D a b h) := by
  have hunit : V.toSpecΓ ≫ map f = f := by
    unfold map
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have hV : V.IsQuasiAffine := .of_isQuasiAffineHom f
  have : IsAffine (Over.mk (map f)).left :=
    (inferInstance : IsAffine (Spec Γ(V, ⊤)))
  have : CompactSpace (Over.mk f).left := (inferInstance : CompactSpace V)
  have : QuasiSeparatedSpace (Over.mk f).left := (inferInstance : QuasiSeparatedSpace V)
  have : CompactSpace (Over.mk (map f)).left := inferInstance
  have : QuasiSeparatedSpace (Over.mk (map f)).left := inferInstance
  have hf : QuasiCompact f := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr
    (inferInstance : CompactSpace V)
  let v := f ≫ p
  let w := map f ≫ p
  have hv : IsQuasiAffineHom v := inferInstance
  let i : Over.mk v ⟶ Over.mk w := Over.homMk V.toSpecΓ (by
    dsimp [v, w]
    rw [← Category.assoc]
    exact congrArg (fun k ↦ k ≫ p) hunit)
  have hi : IsIso i.left.appTop := by
    change IsIso V.toSpecΓ.appTop
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have : CompactSpace (Over.mk v).left := (inferInstance : CompactSpace V)
  have : QuasiSeparatedSpace (Over.mk v).left := (inferInstance : QuasiSeparatedSpace V)
  have : IsAffine (Over.mk w).left := (inferInstance : IsAffine (Spec Γ(V, ⊤)))
  have : CompactSpace (Over.mk w).left := inferInstance
  have : QuasiSeparatedSpace (Over.mk w).left := inferInstance
  let j : pullback v p ⟶ pullback w p :=
    pullback.lift (pullback.fst v p ≫ V.toSpecΓ) (pullback.snd v p) (by
      rw [Category.assoc, show V.toSpecΓ ≫ w = v from Over.w i, pullback.condition])
  have hj : IsIso j.appTop := pullback_appTop_isIso _ _ i p
  have : IsIso V.toSpecΓ.appTop := hi
  have : IsAffine (pullback w p) := inferInstance
  let t : pullback w p ⟶ Spec Γ(V, ⊤) := extend j (D.toHom ≫ V.toSpecΓ)
  have hjt : j ≫ t = D.toHom ≫ V.toSpecΓ := extend_fac j (D.toHom ≫ V.toSpecΓ)
  have ht : t ≫ map f = pullback.snd w p := by
    apply cancel_into_affine j
    rw [← Category.assoc, hjt]
    rw [Category.assoc]
    rw [show V.toSpecΓ ≫ map f = f from hunit]
    change D.toHom ≫ f = j ≫ pullback.snd _ _
    rw [show j ≫ pullback.snd w p = pullback.snd v p from pullback.lift_snd _ _ _]
    exact Over.w (D.transport _ _ _ _)
  let τ {T : Scheme.{u}} (a b : T ⟶ A) (h : a ≫ p = b ≫ p)
      (x : Over.mk a ⟶ Over.mk (map f)) : Over.mk b ⟶ Over.mk (map f) :=
    Over.homMk (pullback.lift x.left b (by
      change x.left ≫ (map f ≫ p) = b ≫ p
      rw [← Category.assoc, show x.left ≫ map f = a from Over.w x]
      exact h) ≫ t) (by simp [ht])
  have hn {T T' : Scheme.{u}} (g : T' ⟶ T) (a b : T ⟶ A)
      (h : a ≫ p = b ≫ p) (x : Over.mk a ⟶ Over.mk (map f)) :
      τ (g ≫ a) (g ≫ b) (by simp [h]) ((Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
        (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b) ≫ τ a b h x := by
    apply Over.OverMorphism.ext
    simp only [τ, Over.homMk_left, Over.comp_left]
    apply Eq.trans (congrArg (fun z ↦ z ≫ t) ?_) (Category.assoc g _ t)
    apply pullback.hom_ext <;> simp
  have hn' {T U : Scheme.{u}} (g : U ⟶ T) (a b : T ⟶ A)
      (h : a ≫ p = b ≫ p) (x : Over.mk a ⟶ Over.mk (map f))
      (a' b' : U ⟶ A) (h' : a' ≫ p = b' ≫ p)
      (y : Over.mk a' ⟶ Over.mk (map f))
      (hy : y.left = g ≫ x.left) (hb : b' = g ≫ b) :
      (τ a' b' h' y).left = g ≫ (τ a b h x).left := by
    change pullback.lift y.left b' _ ≫ t = g ≫ (pullback.lift x.left b _ ≫ t)
    apply Eq.trans (congrArg (fun z ↦ z ≫ t) ?_) (Category.assoc g _ t)
    apply pullback.hom_ext <;> simp [hy, hb]
  have he {T : Scheme.{u}} (a b : T ⟶ A) (h : a ≫ p = b ≫ p)
      (x : Over.mk a ⟶ Over.mk f) :
      (τ a b h (x ≫ unit f)).left = (D.transport a b h x).left ≫ V.toSpecΓ := by
    rw [D.transport_left_eq_lift_toHom, Category.assoc]
    change pullback.lift (x.left ≫ V.toSpecΓ) b _ ≫ t =
      pullback.lift x.left b _ ≫ (D.toHom ≫ V.toSpecΓ)
    apply Eq.trans (congrArg (fun z ↦ z ≫ t) ?_)
      ((Category.assoc _ j t).trans (congrArg (fun z ↦ _ ≫ z) hjt))
    apply pullback.hom_ext <;> simp [j, v, w]
  have heval {T U : Scheme.{u}} (g : U ⟶ T) (a b : T ⟶ A)
      (h : a ≫ p = b ≫ p) (x : Over.mk a ⟶ Over.mk (map f))
      (a' b' : U ⟶ A) (h' : a' ≫ p = b' ≫ p) (y : Over.mk a' ⟶ Over.mk f)
      (hy : g ≫ x.left = y.left ≫ V.toSpecΓ) (hb : g ≫ b = b') :
      g ≫ (τ a b h x).left = (D.transport a' b' h' y).left ≫ V.toSpecΓ := by
    rw [D.transport_left_eq_lift_toHom, Category.assoc, ← hjt]
    change g ≫ (pullback.lift x.left b _ ≫ t) =
      pullback.lift y.left b' _ ≫ (j ≫ t)
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [j, hy, hb]
  have hs : ∀ {T : Scheme.{u}} (a : T ⟶ A)
      (x : Over.mk a ⟶ Over.mk (map f)), τ a a rfl x = x := by
    have hU : τ (map f) (map f) rfl (𝟙 _) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      apply cancel_into_affine V.toSpecΓ
      have H := hn' V.toSpecΓ (map f) (map f) rfl (𝟙 _) f f rfl
        (unit f) (by simp [unit]) hunit.symm
      have e := he f f rfl (𝟙 _)
      rw [D.transport_self] at e
      simpa using H.symm.trans e
    intro T a x
    apply Over.OverMorphism.ext
    have H := hn' x.left (map f) (map f) rfl (𝟙 _) a a rfl x
      (by simp) (Over.w x).symm
    simpa [hU] using H
  have hc : ∀ {T : Scheme.{u}} (a b c : T ⟶ A)
      (hab : a ≫ p = b ≫ p) (hbc : b ≫ p = c ≫ p)
      (x : Over.mk a ⟶ Over.mk (map f)),
      τ b c hbc (τ a b hab x) = τ a c (hab.trans hbc) x := by
    let P : Scheme.{u} := pullback (pullback.snd w p ≫ p) p
    let U : Scheme.{u} := pullback (pullback.snd v p ≫ p) p
    let j' : Over.mk (pullback.snd v p ≫ p) ⟶
        Over.mk (pullback.snd w p ≫ p) := Over.homMk j (by simp [j])
    have hvp : IsQuasiAffineHom (pullback.snd v p) :=
      isQuasiAffineHom_baseChange v p hv
    have : (pullback v p).IsQuasiAffine :=
      .of_isQuasiAffineHom (pullback.snd v p)
    have : CompactSpace (Over.mk (pullback.snd v p ≫ p)).left :=
      (inferInstance : CompactSpace (pullback v p : Scheme.{u}))
    have : QuasiSeparatedSpace (Over.mk (pullback.snd v p ≫ p)).left :=
      (inferInstance : QuasiSeparatedSpace (pullback v p : Scheme.{u}))
    have : IsAffine (Over.mk (pullback.snd w p ≫ p)).left :=
      (inferInstance : IsAffine (pullback w p))
    have : CompactSpace (Over.mk (pullback.snd w p ≫ p)).left := inferInstance
    have : QuasiSeparatedSpace (Over.mk (pullback.snd w p ≫ p)).left := inferInstance
    have : IsIso j'.left.appTop := hj
    let k : U ⟶ P := ((Over.pullback p).map j').left
    have hk : IsIso k.appTop := pullback_appTop_isIso _ _ j' p
    let a₀ : P ⟶ A := pullback.fst _ _ ≫ pullback.fst w p ≫ map f
    let b₀ : P ⟶ A := pullback.fst _ _ ≫ pullback.snd w p
    let c₀ : P ⟶ A := pullback.snd _ _
    have h₀₁ : a₀ ≫ p = b₀ ≫ p := by simp [a₀, b₀, w, pullback.condition]
    have h₁₂ : b₀ ≫ p = c₀ ≫ p := by simp [b₀, c₀, pullback.condition]
    let x₀ : Over.mk a₀ ⟶ Over.mk (map f) :=
      Over.homMk (pullback.fst _ _ ≫ pullback.fst w p) rfl
    have hU : τ b₀ c₀ h₁₂ (τ a₀ b₀ h₀₁ x₀) =
        τ a₀ c₀ (h₀₁.trans h₁₂) x₀ := by
      apply Over.OverMorphism.ext
      apply cancel_into_affine k
      let a₁ : U ⟶ A := pullback.fst _ _ ≫ pullback.fst v p ≫ f
      let b₁ : U ⟶ A := pullback.fst _ _ ≫ pullback.snd v p
      let c₁ : U ⟶ A := pullback.snd _ _
      have h₁ : a₁ ≫ p = b₁ ≫ p := by simp [a₁, b₁, v, pullback.condition]
      have h₂ : b₁ ≫ p = c₁ ≫ p := by simp [b₁, c₁, pullback.condition]
      let y : Over.mk a₁ ⟶ Over.mk f :=
        Over.homMk (pullback.fst _ _ ≫ pullback.fst v p) rfl
      have hy : k ≫ x₀.left = y.left ≫ V.toSpecΓ := by simp [k, j', j, x₀, y]
      have hb : k ≫ b₀ = b₁ := by simp [k, j', j, b₀, b₁]
      have hc : k ≫ c₀ = c₁ := by simp [k, c₀, c₁]
      have e₁ := heval k a₀ b₀ h₀₁ x₀ a₁ b₁ h₁ y hy hb
      rw [heval k b₀ c₀ h₁₂ (τ a₀ b₀ h₀₁ x₀) b₁ c₁ h₂
        (D.transport a₁ b₁ h₁ y) e₁ hc,
        heval k a₀ c₀ (h₀₁.trans h₁₂) x₀ a₁ c₁ (h₁.trans h₂) y hy hc,
        D.transport_transport]
    intro T a b c hab hbc x
    let l₁ : T ⟶ pullback w p := pullback.lift x.left b (by
      dsimp [w]
      rw [← Category.assoc, show x.left ≫ map f = a from Over.w x]
      exact hab)
    let l : T ⟶ P := pullback.lift l₁ c (by simpa [l₁] using hbc)
    have H := congrArg (fun z ↦ l ≫ z.left) hU
    have n₁ := hn' l a₀ b₀ h₀₁ x₀ a b hab x
      (by simp [l, l₁, x₀]) (by simp [l, l₁, b₀])
    have n₂ := hn' l b₀ c₀ h₁₂ (τ a₀ b₀ h₀₁ x₀) b c hbc
      (τ a b hab x) n₁ (by simp [l, c₀])
    have n₃ := hn' l a₀ c₀ (h₀₁.trans h₁₂) x₀ a c (hab.trans hbc) x
      (by simp [l, l₁, x₀]) (by simp [l, c₀])
    apply Over.OverMorphism.ext
    rw [n₂, n₃]
    exact H
  let E : Over.DescentDatum p (Over.mk (map f)) :=
    { transport := τ
      transport_homMk_comp := hn
      transport_self := hs
      transport_transport := hc }
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, E, ?_, ?_⟩
  · intro T a b h x
    exact he a b h x
  · intro T hT a b ha hb h
    have : IsIso (unit f).left.appTop := (inferInstance : IsIso V.toSpecΓ.appTop)
    have : IsAffine ((Over.pullback b).obj (Over.mk (map f))).left :=
      (inferInstance : IsAffine (pullback (map f) b))
    have hj' : IsIso (unitBaseChange f a).appTop :=
      pullback_appTop_isIso _ _ (unit f) a
    apply cancel_into_affine (unitBaseChange f a)
    unfold extendedTransition
    rw [← Category.assoc, ← Category.assoc, (alpha_properties f a).1]
    rw [← Scheme.toSpecΓ_naturality, Category.assoc]
    change unitBaseChange f a ≫
      (transition p (Over.mk (map f)) E a b h).left =
      (transition p (Over.mk f) D a b h).left ≫
        (pullback f b).toSpecΓ ≫ (alpha f b).inv
    rw [← (alpha_properties f b).1]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [Category.assoc, transition, Over.homMk_left, pullback.lift_fst]
      conv_rhs =>
        simp only [unitBaseChange, Over.pullback_map_left, pullback.lift_fst]
      have hW : (pullback.fst (map f) a ≫ map f) ≫ p =
          (pullback.snd (map f) a ≫ b) ≫ p := by
        rw [pullback.condition]
        simpa only [Category.assoc] using congrArg
          (fun z ↦ pullback.snd (map f) a ≫ z) h
      have hV' : (pullback.fst f a ≫ f) ≫ p =
          (pullback.snd f a ≫ b) ≫ p := by
        rw [pullback.condition]
        simpa only [Category.assoc] using congrArg (fun z ↦ pullback.snd f a ≫ z) h
      simpa [E, unit] using heval (unitBaseChange f a)
        (pullback.fst (map f) a ≫ map f) (pullback.snd (map f) a ≫ b) hW
        (Over.homMk (pullback.fst (map f) a) rfl)
        (pullback.fst f a ≫ f) (pullback.snd f a ≫ b) hV'
        (Over.homMk (pullback.fst f a) rfl)
        (by simp [unitBaseChange, unit])
        (by simp [unitBaseChange])
    · simp only [Category.assoc, transition, Over.homMk_left, pullback.lift_snd]
      simp only [unitBaseChange, Over.pullback_map_left, pullback.lift_snd]


end CanonicalAffineEnvelope

end AlgebraicGeometry
