/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateComp
public import WeilConjectures.TraceFormula.ProperCompatibilityExchange
public import WeilConjectures.TraceFormula.ShriekTrace

/-!

# Exchange of the support isomorphisms along a proper pushforward diagram

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

lemma NatTrans.naturality_comp_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ E} (α : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂) {X Y : C} (x : X ⟶ Y) {Z : E}
    (h : G₂.obj (F₂.obj Y) ⟶ Z) :
    G₁.map (F₁.map x) ≫ α.app Y ≫ h = α.app X ≫ G₂.map (F₂.map x) ≫ h := by
  simpa using α.naturality_assoc x h

@[reassoc]
lemma Functor.map_hom_app_comp_map_inv_app {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) {G H : C ⥤ D} (e : G ≅ H) (X : C) :
    F.map (e.hom.app X) ≫ F.map (e.inv.app X) = 𝟙 _ := by
  rw [← F.map_comp, Iso.hom_inv_id_app, F.map_id]

@[reassoc]
lemma Functor.map_map_hom_app_comp_map_map_inv_app {B C D E : Type*} [Category B] [Category C]
    [Category D] [Category E] (F : D ⥤ E) (G : C ⥤ D) {H H' : B ⥤ C} (e : H ≅ H') (X : B) :
    F.map (G.map (e.hom.app X)) ≫ F.map (G.map (e.inv.app X)) = 𝟙 _ := by
  rw [← F.map_comp, ← G.map_comp, Iso.hom_inv_id_app, G.map_id, F.map_id]

@[reassoc]
lemma Iso.hom_app_comp_map_comp_inv_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (φ : X ⟶ Y) : e.hom.app X ≫ G.map φ ≫ e.inv.app Y = F.map φ := by
  rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]

@[reassoc]
lemma Functor.map_hom_app_comp_map_map_comp_map_inv_app {C D E : Type*} [Category C] [Category D]
    [Category E] (K : D ⥤ E) {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (φ : X ⟶ Y) :
    K.map (e.hom.app X) ≫ K.map (G.map φ) ≫ K.map (e.inv.app Y) = K.map (F.map φ) := by
  rw [← K.map_comp, ← K.map_comp, Iso.hom_app_comp_map_comp_inv_app]

@[reassoc]
lemma NatTrans.app_comp_map_map {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (α : F ⟶ G ⋙ H) {X Y : C} (x : X ⟶ Y) :
    α.app X ≫ H.map (G.map x) = F.map x ≫ α.app Y :=
  (α.naturality x).symm

@[reassoc]
lemma NatTrans.map_map_comp_app {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (α : G ⋙ H ⟶ F) {X Y : C} (x : X ⟶ Y) :
    H.map (G.map x) ≫ α.app Y = α.app X ≫ F.map x :=
  α.naturality x

@[reassoc]
lemma Functor.map_app_comp_map_map {B C D : Type*} [Category B] [Category C] [Category D]
    (K : C ⥤ D) {F G : B ⥤ C} (α : F ⟶ G) {X Y : B} (x : X ⟶ Y) :
    K.map (α.app X) ≫ K.map (G.map x) = K.map (F.map x) ≫ K.map (α.app Y) := by
  rw [← K.map_comp, ← K.map_comp, α.naturality]

@[reassoc]
lemma Iso.hom_app_comp_map₃_comp_inv_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y Z W : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) :
    e.hom.app X ≫ G.map a ≫ G.map b ≫ G.map c ≫ e.inv.app W = F.map a ≫ F.map b ≫ F.map c := by
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, Iso.hom_app_comp_map_comp_inv_app, F.map_comp,
    F.map_comp, Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.FixedLocus

variable {c : Correspondence ℓ K} (F : c.FixedLocus)

/-- The inclusion of the fixed locus is a closed immersion: it is the base change of the
diagonal. -/
instance isClosedImmersion_ι : IsClosedImmersion F.ι.left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (F.isPullback.map (Over.forget _)).flip (inferInstanceAs (IsClosedImmersion (diag X).left))

set_option maxHeartbeats 1000000 in
-- the pullbacks and shrieks of bounded constructible complexes are unfolded in defeq checks
/-- **The exceptional adjoint of the support isomorphism** (blueprint
`def-trf-kernel-pushforward-maps`, item 8, last assertion): the `Rc_! ⊣ Rc^!`-adjoint of
`ζ_c : Rι_* ω_Fix(c) ⟶ Rc^! RΔ_* ω_X` is
`Rc_! Rι_* ω ≅ Rc_! Rι_! ω ≅ RΔ_! Rd_! ω ⟶ RΔ_! ω_X ≅ RΔ_* ω_X`, the composition law of the
fixed square followed by the trace `t_d`. -/
theorem homEquiv_symm_supportIso_hom :
    ((boundedConstructibleUpperShriekAdjunction _ ℓ c.support).homEquiv _ _).symm
        F.supportIso.hom =
      (boundedConstructibleLowerShriek _ ℓ c.support).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).inv.app
            (dualizingComplex' ℓ F.F)) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support).hom.app
          (dualizingComplex' ℓ F.F) ≫
        (boundedConstructibleLowerShriek _ ℓ (diag X)).map
          (lowerShriekDualizingComplexTrace ℓ F.d) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X)).hom.app
          (dualizingComplex' ℓ X) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback
  have hK := Adjunction.homEquiv_symm_conjugateIsoEquiv_inv_app
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ F.ι)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X))
    (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ F.isPullback)
    (dualizingComplex' ℓ X)
  have n₁ := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).inv.naturality
    (dualizingComplexComp ℓ F.d).inv
  have n₂ := (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support).hom.naturality
    (dualizingComplexComp ℓ F.d).inv
  simp only [Functor.comp_map] at n₂
  simp only [supportIso, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Adjunction.homEquiv_naturality_left_symm, upperShriekLowerStarIso,
    lowerShriekBaseChangeIso, hK, lowerShriekDualizingComplexTrace,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, n₁, Functor.map_comp_assoc]
  congr 1
  rw [← Category.assoc, n₂, Category.assoc]

end Correspondence.FixedLocus

section Exchange

variable (ℓ) {Fc Cc Xc Pc Fb Cb Yb Pb : Over (Spec (.of k))}
  [LocallyOfFiniteType Fc.hom] [QuasiCompact Fc.hom] [IsSeparated Fc.hom]
  [LocallyOfFiniteType Cc.hom] [QuasiCompact Cc.hom] [IsSeparated Cc.hom]
  [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom] [IsSeparated Xc.hom]
  [LocallyOfFiniteType Pc.hom] [QuasiCompact Pc.hom] [IsSeparated Pc.hom]
  [LocallyOfFiniteType Fb.hom] [QuasiCompact Fb.hom] [IsSeparated Fb.hom]
  [LocallyOfFiniteType Cb.hom] [QuasiCompact Cb.hom] [IsSeparated Cb.hom]
  [LocallyOfFiniteType Yb.hom] [QuasiCompact Yb.hom] [IsSeparated Yb.hom]
  [LocallyOfFiniteType Pb.hom] [QuasiCompact Pb.hom] [IsSeparated Pb.hom]
  {ιc : Fc ⟶ Cc} {c : Cc ⟶ Pc} {dc : Fc ⟶ Xc} {Δc : Xc ⟶ Pc}
  {ιb : Fb ⟶ Cb} {b : Cb ⟶ Pb} {db : Fb ⟶ Yb} {Δb : Yb ⟶ Pb}
  {g : Cc ⟶ Cb} {q : Pc ⟶ Pb} {f : Xc ⟶ Yb} {h : Fc ⟶ Fb}
  [IsProper ιc.left] [IsProper Δc.left] [IsProper ιb.left] [IsProper Δb.left] [IsProper g.left]
  [IsProper q.left] [IsProper f.left] [IsProper h.left] [IsProper (ιc ≫ g).left]
  [IsProper (h ≫ ιb).left] [IsProper (Δc ≫ q).left] [IsProper (f ≫ Δb).left]

lemma lowerStarDualizingComplexTrace_eq (a : Xc ⟶ Yb) [IsProper a.left] :
    lowerStarDualizingComplexTrace ℓ a =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).inv.app _ ≫
        lowerShriekDualizingComplexTrace ℓ a := by
  rw [lowerStarDualizingComplexTrace, lowerShriekDualizingComplexTrace]

set_option maxHeartbeats 2000000 in
-- the direct images of bounded constructible complexes are unfolded in the defeq checks
/-- The exchange of the support isomorphisms along a map of squares, in terms of the
exceptional adjoints of the support isomorphisms (blueprint `lem-trf-trace-map-exchange`, (2),
proof): the two maps `Rb_! Rg_* Rιc_* ω ⟶ RΔb_* ω` agree. -/
theorem lowerStar_square_trace_exchange (wc : ιc ≫ c = dc ≫ Δc) (wb : ιb ≫ b = db ≫ Δb)
    (wgb : g ≫ b = c ≫ q) (wq : Δc ≫ q = f ≫ Δb) (wh : ιc ≫ g = h ≫ ιb)
    (whd : dc ≫ f = h ≫ db) :
    (lowerStarLowerShriekCompIso ℓ wgb).hom.app
        ((boundedConstructibleLowerStar _ ℓ ιc).obj (dualizingComplex' ℓ Fc)) ≫
      (boundedConstructibleLowerStar _ ℓ q).map
        ((boundedConstructibleLowerShriek _ ℓ c).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ιc).inv.app
              (dualizingComplex' ℓ Fc)) ≫
          (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wc).hom.app
            (dualizingComplex' ℓ Fc) ≫
          (boundedConstructibleLowerShriek _ ℓ Δc).map (lowerShriekDualizingComplexTrace ℓ dc) ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δc).hom.app
            (dualizingComplex' ℓ Xc)) ≫
      (boundedConstructibleLowerStarComp _ ℓ Δc q).hom.app (dualizingComplex' ℓ Xc) ≫
      eqToHom (by rw [wq]) ≫
      (boundedConstructibleLowerStarComp _ ℓ f Δb).inv.app (dualizingComplex' ℓ Xc) ≫
      (boundedConstructibleLowerStar _ ℓ Δb).map (lowerStarDualizingComplexTrace ℓ f) =
    (boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerStarComp _ ℓ ιc g).hom.app (dualizingComplex' ℓ Fc) ≫
          eqToHom (by rw [wh]) ≫
          (boundedConstructibleLowerStarComp _ ℓ h ιb).inv.app (dualizingComplex' ℓ Fc) ≫
          (boundedConstructibleLowerStar _ ℓ ιb).map (lowerStarDualizingComplexTrace ℓ h)) ≫
      (boundedConstructibleLowerShriek _ ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ιb).inv.app
          (dualizingComplex' ℓ Fb)) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wb).hom.app (dualizingComplex' ℓ Fb) ≫
      (boundedConstructibleLowerShriek _ ℓ Δb).map (lowerShriekDualizingComplexTrace ℓ db) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δb).hom.app
        (dualizingComplex' ℓ Yb) := by
  simp only [lowerStarLowerShriekCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app, lowerStarComp_hom_app_eq,
    lowerStarComp_inv_app_eq, lowerStarDualizingComplexTrace_eq, Functor.map_comp,
    Category.assoc]
  rw [Functor.map_hom_app_comp_map_inv_app_assoc (boundedConstructibleLowerStar _ ℓ q)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δc),
    Functor.map_hom_app_comp_map_inv_app_assoc (boundedConstructibleLowerStar _ ℓ Δb)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f),
    Functor.map_map_hom_app_comp_map_map_inv_app_assoc (boundedConstructibleLowerShriek _ ℓ b)
      (boundedConstructibleLowerStar _ ℓ ιb) (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h),
    lowerShriekIsoLowerStar_hom_app_comp_eqToHom_assoc ℓ wq, Iso.hom_inv_id_app_assoc,
    ← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δb).hom.naturality
      (lowerShriekDualizingComplexTrace ℓ f)]
  rw [Iso.hom_app_comp_map₃_comp_inv_app_assoc
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ q),
    Functor.map_hom_app_comp_map_map_comp_map_inv_app_assoc (boundedConstructibleLowerShriek _ ℓ b)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ιb),
    ← Functor.map_comp_assoc (boundedConstructibleLowerShriek _ ℓ b)
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (ιc ≫ g)).hom.app _),
    lowerShriekIsoLowerStar_hom_app_comp_eqToHom ℓ wh, Functor.map_comp_assoc,
    Functor.map_hom_app_comp_map_inv_app_assoc (boundedConstructibleLowerShriek _ ℓ b)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (h ≫ ιb)),
    NatTrans.app_comp_map_map_assoc (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom,
    ← lowerShriek_map_comp_eqToHom_assoc ℓ wgb,
    ← NatTrans.map_map_comp_app_assoc (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv,
    Functor.map_app_comp_map_map_assoc (boundedConstructibleLowerShriek _ ℓ b)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv,
    lowerShriekSquareIso_trace_exchange_assoc ℓ wc wb wgb wq wh whd]
  simp only [Functor.map_comp, Category.assoc]

end Exchange

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)
  (Fc : c.FixedLocus) (Fb : P.pushforward.FixedLocus)

set_option maxHeartbeats 2000000 in
-- the direct images of bounded constructible complexes are unfolded in the defeq checks
/-- **Exchange of the support isomorphisms** (blueprint `lem-trf-trace-map-exchange`, (2)):
`Rb^!(RΔ_{Y*} τ_f) ∘ E ∘ Rg_* ζ_c = ζ_b ∘ Ri_{b*} τ_h`, read through `g ∘ i_c = i_b ∘ h`. -/
theorem lowerStar_map_supportIso_comp_exchange :
    (boundedConstructibleLowerStar _ ℓ P.g).map Fc.supportIso.hom ≫
        (lowerStarUpperShriekExchange ℓ P.g_comp_support).app
          ((boundedConstructibleLowerStar _ ℓ (diag X)).obj (dualizingComplex' ℓ X)) ≫
        (boundedConstructibleUpperShriek _ ℓ P.pushforward.support).map
          ((boundedConstructibleLowerStarComp _ ℓ (diag X) (prod.map P.f P.f)).hom.app
              (dualizingComplex' ℓ X) ≫
            eqToHom (by rw [P.diag_comp_prodMap]) ≫
            (boundedConstructibleLowerStarComp _ ℓ P.f (diag Y)).inv.app
              (dualizingComplex' ℓ X) ≫
            (boundedConstructibleLowerStar _ ℓ (diag Y)).map
              (lowerStarDualizingComplexTrace ℓ P.f)) =
      (boundedConstructibleLowerStarComp _ ℓ Fc.ι P.g).hom.app (dualizingComplex' ℓ Fc.F) ≫
        eqToHom (by rw [← P.fixMap_ι]) ≫
        (boundedConstructibleLowerStarComp _ ℓ (P.fixMap Fc Fb) Fb.ι).inv.app
          (dualizingComplex' ℓ Fc.F) ≫
        (boundedConstructibleLowerStar _ ℓ Fb.ι).map
          (lowerStarDualizingComplexTrace ℓ (P.fixMap Fc Fb)) ≫
        Fb.supportIso.hom := by
  have whd : Fc.d ≫ P.f = P.fixMap Fc Fb ≫ Fb.d := by
    rw [Correspondence.FixedLocus.d, Correspondence.FixedLocus.d, Category.assoc,
      P.fixMap_ι_b₁]
  have : IsProper (Fc.ι ≫ P.g).left := inferInstanceAs (IsProper (Fc.ι.left ≫ P.g.left))
  have : IsProper (P.fixMap Fc Fb ≫ Fb.ι).left :=
    inferInstanceAs (IsProper ((P.fixMap Fc Fb).left ≫ Fb.ι.left))
  have : IsProper (diag X ≫ prod.map P.f P.f).left :=
    inferInstanceAs (IsProper ((diag X).left ≫ (prod.map P.f P.f).left))
  have : IsProper (P.f ≫ diag Y).left := inferInstanceAs (IsProper (P.f.left ≫ (diag Y).left))
  apply ((boundedConstructibleUpperShriekAdjunction _ ℓ P.pushforward.support).homEquiv _
    _).symm.injective
  have hm := Adjunction.homEquiv_comp_mateEquiv
    (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ P.pushforward.support)
    (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom (𝟙 _) Fc.supportIso.hom
    ((boundedConstructibleLowerStarComp _ ℓ (diag X) (prod.map P.f P.f)).hom.app
        (dualizingComplex' ℓ X) ≫
      eqToHom (by rw [P.diag_comp_prodMap]) ≫
      (boundedConstructibleLowerStarComp _ ℓ P.f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
      (boundedConstructibleLowerStar _ ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ P.f))
  rw [Category.id_comp] at hm
  rw [lowerStarUpperShriekExchange, ← hm]
  rw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_naturality_left_symm]
  rw [Fc.homEquiv_symm_supportIso_hom, Fb.homEquiv_symm_supportIso_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have key := lowerStar_square_trace_exchange ℓ Fc.ι_support Fb.ι_support P.g_comp_support
    P.diag_comp_prodMap (P.fixMap_ι Fc Fb).symm whd
  simp only [Functor.map_comp, Category.assoc] at key ⊢
  exact key

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
