/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module
public import Sheaf.Paper.PurityFrameClass
/-! # Boundary products on a fixed closed support

Source: the support-identification and restriction steps of frame independence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

/-- Transport of a concrete boundary product to a specified isomorphic closed support.
Source: frame-independence support identification
(blueprint: lem-pur-frame-product-support). -/
def frameSingleTransport {C : Type v} [Category.{w} C] {D : Type*} [Category D]
    (S : C ⥤ D) {L M : C} (q : L ≅ M) {N : D} (α : S.obj L ⟶ N) : S.obj M ⟶ N :=
  S.map q.inv ≫ α

/-- Transport composes with a class equality over a composable coefficient isomorphism.
Source: frame-independence finite-chain assembly
(blueprint: lem-pur-frame-product-support).
Proof: expand the inverse of the composite isomorphism and cancel the adjacent
image of the inverse and the image of the forward isomorphism. -/
theorem frameSingleTransport_comp {C : Type v} [Category.{w} C]
    {D : Type*} [Category D] (S : C ⥤ D) {L M N : C}
    (e : L ≅ M) (d : M ≅ N) (q : L ≅ N) (hq : e ≪≫ d = q)
    {T : D} (α : S.obj M ⟶ T) (β : S.obj L ⟶ T)
    (h : β = S.map e.hom ≫ α) :
    frameSingleTransport S d α = frameSingleTransport S q β := by
  subst q
  rw [h]
  simp only [frameSingleTransport, Iso.trans_inv, Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id_assoc]

/-- Cancel transport through a coefficient isomorphism in an equality of classes.
Source: the shear endpoint comparison in frame independence
(blueprint: lem-pur-frame-product-support).
Proof: precompose the equality with the functor image of the forward isomorphism
and cancel its composite with the inverse. -/
theorem frameSingleTransport_cancel {C : Type v} [Category.{w} C]
    {D : Type*} [Category D] (S : C ⥤ D) {L M : C} (q : L ≅ M)
    {T : D} (α : S.obj M ⟶ T) (β : S.obj L ⟶ T)
    (h : frameSingleTransport S q β = α) : β = S.map q.hom ≫ α := by
  rw [← h]
  simp only [frameSingleTransport, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Forward transport relations compose through a functor.
Source: frame-independence finite-chain assembly
(blueprint: lem-pur-frame-product-support).
Proof: substitute the two given equalities, use functoriality on the composite,
and use associativity. -/
theorem frameForwardTransport_trans {C : Type v} [Category.{w} C]
    {D : Type*} [Category D] (S : C ⥤ D) {L M N : C}
    (e : L ⟶ M) (d : M ⟶ N) {T : D}
    (α : S.obj N ⟶ T) (β : S.obj M ⟶ T) (γ : S.obj L ⟶ T)
    (hβ : β = S.map d ≫ α) (hγ : γ = S.map e ≫ β) :
    γ = S.map (e ≫ d) ≫ α := by
  rw [hγ, hβ, Functor.map_comp, Category.assoc]

/-- Uniqueness of the normalized forward map after an epic restriction.
Source: constant-restriction normalization in frame independence
(blueprint: lem-pur-frame-product-support).
Proof: cancel the epic restriction, reassociate and use its two normalizations. -/
theorem frameNormalized_comp {C : Type v} [Category.{w} C]
    {A B D E : C} (r : A ⟶ B) [Epi r]
    (s : A ⟶ D) (t : A ⟶ E) (f : B ⟶ D) (g : D ⟶ E) (h : B ⟶ E)
    (hf : r ≫ f = s) (hg : s ≫ g = t) (hh : r ≫ h = t) : f ≫ g = h := by
  apply (cancel_epi r).mp
  rw [← Category.assoc, hf, hg, hh]

/-- An endomorphism normalized to the identity after an epic restriction is the identity.
Source: constant-restriction normalization in frame independence
(blueprint: lem-pur-frame-product-support).
Proof: cancel the restriction and use its normalization. -/
theorem frameNormalized_id {C : Type v} [Category.{w} C]
    {A B : C} (r : A ⟶ B) [Epi r] (f : B ⟶ B) (h : r ≫ f = r) : f = 𝟙 _ := by
  apply (cancel_epi r).mp
  exact h.trans (Category.comp_id _).symm

/-- Cancel a coefficient identification in a unit-normalization equation.
Source: constant-restriction normalization in frame independence
(blueprint: lem-pur-frame-product-support).
Proof: postcompose with the coefficient identification, use the given equation,
and cancel the resulting isomorphism. -/
theorem frameRestriction_normalized {C : Type v} [Category.{w} C]
    {D : Type*} [Category D] (G : C ⥤ D) {M U : C} {N V : D}
    (c : M ≅ U) (d : N ≅ V) (r : V ⟶ G.obj U) (q : G.obj M ⟶ N)
    (h : r ≫ G.map c.inv ≫ q ≫ d.hom = 𝟙 V) :
    (d.hom ≫ r ≫ G.map c.inv) ≫ q = 𝟙 N := by
  apply (cancel_mono d.hom).mp
  simp only [Category.assoc, h, Category.comp_id, Category.id_comp]

/-- A normalized restriction survives direct-image composition and a chosen comparison.
Source: constant-restriction normalization in frame independence
(blueprint: lem-pur-frame-product-support).
Proof: reassociate, use the first normalization, cancel the comparison, and apply
functoriality to the inverse restriction. -/
theorem frameRestriction_comp {C : Type v} [Category.{w} C]
    {D : Type*} [Category D] (G : C ⥤ D) {A B T : D} {L M : C}
    (r : A ⟶ B) (k : B ⟶ T) (s : A ⟶ G.obj M) (d : G.obj L ≅ T)
    (p : M ⟶ L) (q : L ⟶ M)
    (hr : r ≫ k = s ≫ G.map p ≫ d.hom) (hp : p ≫ q = 𝟙 M) :
    r ≫ (k ≫ d.inv ≫ G.map q) = s := by
  rw [← Category.assoc, ← Category.assoc, hr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp, hp,
    G.map_id, Category.comp_id]

/-- Normalize the exact composite of coefficient isomorphisms used for a closed support.
Source: constant-restriction normalization in frame independence
(blueprint: lem-pur-frame-product-support).
Proof: expand the composite isomorphism and apply frameRestriction_comp. -/
theorem frameRestriction_iso {C : Type v} [Category.{w} C]
    {D : Type*} [Category D] (G : C ⥤ D) {A B T : D} {L M : C}
    (r : A ⟶ B) (k : B ≅ T) (s : A ⟶ G.obj M) (d : G.obj L ≅ T)
    (p : M ⟶ L) (q : L ≅ M)
    (hr : r ≫ k.hom = s ≫ G.map p ≫ d.hom) (hp : p ≫ q.hom = 𝟙 M) :
    r ≫ (k ≪≫ d.symm ≪≫ G.mapIso q).hom = s := by
  exact frameRestriction_comp G r k.hom s d p q.hom hr hp

/-- The actual ordered boundary product, transported only at its closed source.
Source: frame-independence support identification
(blueprint: lem-pur-frame-product-support). -/
def frameProductOnSupport (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) (a : X ⟶ Spec (.of P.field.k)) (c : ℕ) (f : Fin c → Γ(X, ⊤))
    (e : X.zeroLocusSubscheme (Set.range f) ≅ Z)
    (he : e.hom ≫ i = X.zeroLocusSubschemeι (Set.range f)) :
    cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)) :=
  frameSingleTransport (cupSingle P X) (P.frameClosedCoefficientIso _ i e he)
    (P.frameBoundaryProduct X a c f)

/-- A presentation of a closed support remains a presentation after base change.
Source: the restriction step of frame independence
(blueprint: lem-pur-frame-product-support).
Proof: base change the zero subscheme of the tuple, then paste with the square
of its specified isomorphism to the closed support. -/
theorem framePresentationPullback {Z X Y : Scheme.{u}} (i : Z ⟶ X)
    (q : Y ⟶ X) (c : ℕ) (f : Fin c → Γ(X, ⊤))
    (e : X.zeroLocusSubscheme (Set.range f) ≅ Z)
    (he : e.hom ≫ i = X.zeroLocusSubschemeι (Set.range f)) :
    IsPullback
      (q.zeroLocusSubschemeMap (Set.range f) (Set.range (fun k ↦ q.appTop (f k)))
        (by exact (Set.range_comp _ _).symm) ≫ e.hom)
      (Y.zeroLocusSubschemeι (Set.range (fun k ↦ q.appTop (f k)))) i q := by
  have h := Scheme.isPullback_zeroLocusSubschemeι q (Set.range f)
    (Set.range (fun k ↦ q.appTop (f k))) (by exact (Set.range_comp _ _).symm)
  have h' : IsPullback e.hom (X.zeroLocusSubschemeι (Set.range f)) i (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  simpa only [Category.comp_id] using h.paste_horiz h'

end WeilConjectures.PurityFiniteSetting
