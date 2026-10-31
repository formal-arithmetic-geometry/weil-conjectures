/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemTensorMateArrows

import WeilConjectures.AlgebraicGeometry.SystemClopenAlphaTensorSquare

/-!
# Proper/open tensor-mate interchange on varying coefficient systems

Source: Stacks Project, Tag 0F7B (open case), Tag 0E8I and Tag 0B56;
agent-formulated simultaneous-system refinement
(blueprint: lem-pur-system-clopen-tensor-compatibility).

This is equality in the ordinary derived category of the ringed sequence site,
before evaluation or inverse limit. The operations are universal presentations
of the canonical geometric operations; their existence is supplied in the imported
arrows module. Neither the proper/open arrow nor the projection arrow is inverted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.SystemTensorMate

private theorem mate_tensor_interchange
    {A B C F : Type*} [Category A] [Category B] [Category C] [Category F]
    (Pr : C ⥤ A) (Rr : A ⥤ C) (Pp : F ⥤ B) (Rp : B ⥤ F)
    (ar : Pr ⊣ Rr) (ap : Pp ⊣ Rp) (Pi : F ⥤ C) (Pk : B ⥤ A)
    (J : C ⥤ F) (K : A ⥤ B)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C) (TF : F × F ⥤ F)
    (mr : TC ⋙ Pr ⟶ (Pr.prod Pr) ⋙ TA)
    (mp : TF ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB) (a : J ⋙ Pp ⟶ Pr ⋙ K)
    (di : ∀ G Q, TF.obj (J.obj G, Q) ⟶ J.obj (TC.obj (G, Pi.obj Q)))
    (dk : ∀ M N, TB.obj (K.obj M, N) ⟶ K.obj (TA.obj (M, Pk.obj N)))
    (c : ∀ Q, Pk.obj (Pp.obj Q) ⟶ Pr.obj (Pi.obj Q))
    (dn : ∀ {M M'} (f : M ⟶ M') N,
      TB.map (Prod.mkHom (K.map f) (𝟙 N)) ≫ dk M' N =
        dk M N ≫ K.map (TA.map (Prod.mkHom f (𝟙 (Pk.obj N)))))
    (sq : ∀ G Q,
      Pp.map (di G Q) ≫ a.app (TC.obj (G, Pi.obj Q)) ≫
          K.map (mr.app (G, Pi.obj Q)) =
        mp.app (J.obj G, Q) ≫
          TB.map (Prod.mkHom (a.app G) (𝟙 (Pp.obj Q))) ≫
          dk (Pr.obj G) (Pp.obj Q) ≫
          K.map (TA.map (Prod.mkHom (𝟙 (Pr.obj G)) (c Q))))
    (M : A) (Q : F) :
    di (Rr.obj M) Q ≫
        J.map (ar.homEquiv _ _ (mr.app (Rr.obj M, Pi.obj Q) ≫
          TA.map (Prod.mkHom (ar.counit.app M) (𝟙 _)))) ≫
        (mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).natTrans.app
          (TA.obj (M, Pr.obj (Pi.obj Q))) =
      TF.map (Prod.mkHom ((mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).natTrans.app M)
          (𝟙 Q)) ≫
        ap.homEquiv _ _ (mp.app (Rp.obj (K.obj M), Q) ≫
          TB.map (Prod.mkHom (ap.counit.app (K.obj M)) (𝟙 _))) ≫
        Rp.map (dk M (Pp.obj Q) ≫ K.map (TA.map (Prod.mkHom (𝟙 M) (c Q)))) := by
  let g := (mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).natTrans
  have gc (N : A) :
      Pp.map (g.app N) ≫ ap.counit.app (K.obj N) =
        a.app (Rr.obj N) ≫ K.map (ar.counit.app N) :=
    mateEquiv_counit ar ap (TwoSquare.mk J Pr Pp K a) N
  let pr : TC.obj (Rr.obj M, Pi.obj Q) ⟶
      Rr.obj (TA.obj (M, Pr.obj (Pi.obj Q))) := ar.homEquiv _ _ (mr.app (Rr.obj M, Pi.obj Q) ≫
    TA.map (Prod.mkHom (ar.counit.app M) (𝟙 _)))
  have an := a.naturality pr
  dsimp only [Functor.comp_map] at an
  have mn := mp.naturality (Prod.mkHom (g.app M) (𝟙 Q))
  change Pp.map (TF.map (Prod.mkHom (g.app M) (𝟙 Q))) ≫
    mp.app (Rp.obj (K.obj M), Q) = mp.app (J.obj (Rr.obj M), Q) ≫
      TB.map (Prod.mkHom (Pp.map (g.app M)) (Pp.map (𝟙 Q))) at mn
  let t := dk M (Pp.obj Q) ≫ K.map (TA.map (Prod.mkHom (𝟙 M) (c Q)))
  have cn := ap.counit.naturality t
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at cn
  simp only [t, Functor.map_comp, Category.assoc] at cn
  have pp := (ap.homEquiv _ _).symm_apply_apply
    (mp.app (Rp.obj (K.obj M), Q) ≫
      TB.map (Prod.mkHom (ap.counit.app (K.obj M)) (𝟙 (Pp.obj Q))))
  rw [Adjunction.homEquiv_counit] at pp
  have pc := (ar.homEquiv _ _).symm_apply_apply
    (mr.app (Rr.obj M, Pi.obj Q) ≫
      TA.map (Prod.mkHom (ar.counit.app M) (𝟙 (Pr.obj (Pi.obj Q)))))
  rw [Adjunction.homEquiv_counit] at pc
  change Pr.map pr ≫ ar.counit.app _ = _ at pc
  apply (ap.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change Pp.map (di (Rr.obj M) Q) ≫ Pp.map (J.map pr) ≫
    Pp.map (g.app _) ≫ ap.counit.app _ = _
  rw [gc]
  erw [reassoc_of% an, ← K.map_comp, pc, K.map_comp]
  erw [reassoc_of% (sq (Rr.obj M) Q)]
  rw [cn]
  erw [reassoc_of% pp]
  have mn' : Pp.map (TF.map (Prod.mkHom (g.app M) (𝟙 Q))) ≫
      mp.app (Rp.obj (K.obj M), Q) = mp.app (J.obj (Rr.obj M), Q) ≫
        TB.map (Prod.mkHom (Pp.map (g.app M)) (𝟙 (Pp.obj Q))) := by
    simpa using mn
  rw [reassoc_of% mn']
  have ht : TB.map (Prod.mkHom (Pp.map (g.app M)) (𝟙 (Pp.obj Q))) ≫
      TB.map (Prod.mkHom (ap.counit.app (K.obj M)) (𝟙 (Pp.obj Q))) =
      TB.map (Prod.mkHom (a.app (Rr.obj M)) (𝟙 (Pp.obj Q))) ≫
        TB.map (Prod.mkHom (K.map (ar.counit.app M)) (𝟙 (Pp.obj Q))) := by
    erw [← TB.map_comp, ← TB.map_comp]
    congr 1
    ext
    · exact gc M
    · simp
  erw [reassoc_of% ht]
  congr 2
  erw [reassoc_of% (dn (ar.counit.app M) (Pp.obj Q))]
  simp only [← K.map_comp, ← TA.map_comp, prod_comp,
    Category.id_comp, Category.comp_id]

private theorem delta_naturality_left
    {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (o : TensorOperations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {H H' : D l E U} (f : H ⟶ H') (N : D l E X) :
    (o.T X).map (Prod.mkHom ((o.J j).map f) (𝟙 N)) ≫ (o.delta j H' N).hom =
      (o.delta j H N).hom ≫
        (o.J j).map ((o.T U).map (Prod.mkHom f (𝟙 ((o.P j).obj N)))) := by
  have h :
      o.deltaInv j H N ≫ (o.T X).map (Prod.mkHom ((o.J j).map f) (𝟙 N)) =
        (o.J j).map ((o.T U).map (Prod.mkHom f (𝟙 ((o.P j).obj N)))) ≫
          o.deltaInv j H' N := by
    apply ((o.derivedOpenAdj j).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
    simp only [TensorOperations.deltaInv, Equiv.apply_symm_apply]
    have hn := (o.mu j).inv.naturality (Prod.mkHom ((o.J j).map f) (𝟙 N))
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj,
      Functor.prod_map] at hn
    rw [Category.assoc, ← hn]
    simp only [← Category.assoc, ← Functor.map_comp]
    congr 2
    apply Prod.hom_ext
    · exact ((o.derivedOpenAdj j).unit.naturality f).symm
    · simpa only [prod_comp_snd, Prod.mkHom, Category.id_comp,
        Category.comp_id] using (o.P j).map_id N
  haveI := o.deltaInv_isIso j H N
  haveI := o.deltaInv_isIso j H' N
  have h' := congrArg
    (fun z ↦ (o.delta j H N).hom ≫ z ≫ (o.delta j H' N).hom) h
  simpa only [TensorOperations.delta, Iso.symm_hom, asIso_inv,
    TensorOperations.deltaInv_isIso, Category.assoc, IsIso.inv_hom_id_assoc,
    IsIso.hom_inv_id, Category.comp_id] using h'

/-- Proper/open tensor-mate interchange for arbitrary unbounded varying-ring systems.

Source: Stacks 0F7B (open case), 0E8I and 0B56; the intrinsic strict-system clause of
lem-sf-proper-open-projection-mate (blueprint: lem-pur-system-clopen-tensor-compatibility).

Proof: (1) Identify the strict quotient-semilinear systems with those in
lem-coef-semilinear-derived-sections, using R=O_E and exponent n+1. Specialize the
system clause of lem-sf-proper-open-projection-mate to A,B,C,F and k,r,p,i. The
square need not be cartesian; the stated quasi-compact open and proper hypotheses
are precisely those needed for its clopen lift.
(2) The ordinary alpha in the arrows module is the open-base-change map followed
by the identity/zero clopen projector, as in lem-cbc-strict-tower-proper-open-calculus.
Its unique restriction characterization fixes the same composite, including the
refinement case. Localizing and taking the proper-adjunction mate therefore gives
exactly gamma, with eta_p, alpha R_r and k_! epsilon_r in that order.
(3) Projection is the transpose of mu followed by counit tensor identity. Delta
is the open-unit-normalized comparison of lem-sf-open-tensor-normalization; its
inverse has exactly that node's adjunct. The final square comparison is induced
by k followed by p equaling r followed by i, with the canonical pullback compositors.
(4) Apply the intrinsic system projection-mate identity to H,Q. Steps (1)--(3)
identify all of its arrows with the displayed composites. This proves equality
before evaluation, for arbitrary unbounded objects, with no Tor or normalization
condition and without inverting gamma or projection. -/
theorem system_clopen_tensor_compatibility
    (K : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ K.p)
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : TensorOperations l E)
    {A B C F : Scheme.{u}}
    [A.Over (Spec (.of K.k))] [B.Over (Spec (.of K.k))]
    [C.Over (Spec (.of K.k))] [F.Over (Spec (.of K.k))]
    [IsSeparated (A ↘ Spec (.of K.k))] [LocallyOfFiniteType (A ↘ Spec (.of K.k))]
    [QuasiCompact (A ↘ Spec (.of K.k))]
    [IsSeparated (B ↘ Spec (.of K.k))] [LocallyOfFiniteType (B ↘ Spec (.of K.k))]
    [QuasiCompact (B ↘ Spec (.of K.k))]
    [IsSeparated (C ↘ Spec (.of K.k))] [LocallyOfFiniteType (C ↘ Spec (.of K.k))]
    [QuasiCompact (C ↘ Spec (.of K.k))]
    [IsSeparated (F ↘ Spec (.of K.k))] [LocallyOfFiniteType (F ↘ Spec (.of K.k))]
    [QuasiCompact (F ↘ Spec (.of K.k))]
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ F) (i : C ⟶ F)
    [k.IsOver (Spec (.of K.k))] [r.IsOver (Spec (.of K.k))]
    [p.IsOver (Spec (.of K.k))] [i.IsOver (Spec (.of K.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (H : D l E A) (Q : D l E F) :
    (o.delta i ((pushDerived l E r).obj H) Q).hom ≫
        (o.J i).map (o.projection r H ((o.P i).obj Q)) ≫
        (o.gamma k r p i h).app
          ((o.T A).obj (H, (o.P r).obj ((o.P i).obj Q))) =
      (o.T F).map (CategoryTheory.Prod.mkHom ((o.gamma k r p i h).app H) (𝟙 Q)) ≫
        o.projection p ((o.J k).obj H) Q ≫
        (pushDerived l E p).map
          ((o.delta k H ((o.P p).obj Q)).hom ≫
            (o.J k).map ((o.T A).map
              (CategoryTheory.Prod.mkHom (𝟙 H) ((o.square k r p i h).hom.app Q)))) := by
  exact mate_tensor_interchange
    (o.P r) (pushDerived l E r) (o.P p) (pushDerived l E p)
    (o.derivedAdj r) (o.derivedAdj p) (o.P i) (o.P k) (o.J i) (o.J k)
    (o.T A) (o.T B) (o.T C) (o.T F) (o.mu r).hom (o.mu p).hom
    (o.alpha k r p i h)
    (fun G N ↦ (o.delta i G N).hom) (fun M N ↦ (o.delta k M N).hom)
    (fun N ↦ (o.square k r p i h).hom.app N)
    (fun f N ↦ delta_naturality_left o k f N)
    (system_clopen_alpha_tensor_square K l _hl E o k r p i h) H Q

end WeilConjectures.SystemTensorMate
