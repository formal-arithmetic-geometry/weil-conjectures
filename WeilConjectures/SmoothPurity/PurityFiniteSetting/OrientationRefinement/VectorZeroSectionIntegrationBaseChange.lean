/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleFiniteTypeFrames
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.VectorNormalizedTraceCartesian
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTatePullbackSquare

/-! # Zero-section restriction of integration and base change

Source: blueprint latest, sec-smooth-purity/sk-prop-an, the base-change equation
of vector-bundle purity, restricted to the zero section.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.OrientationRefinement

private theorem integration_mate_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (ex : L ⋙ H ≅ G ⋙ L') {W : C} {W' : C'} {U : D} {U' : D'}
    (a : G.obj W ⟶ W') (t : L.obj W ⟶ U) (t' : L'.obj W' ⟶ U')
    (c : H.obj U ⟶ U')
    (ht : ex.hom.app W ≫ L'.map a ≫ t' = H.map t ≫ c) :
    G.map (adj.homEquiv W U t) ≫ (mateEquiv adj adj' ex.inv).app U ≫ R'.map c =
      a ≫ adj'.homEquiv W' U' t' := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj'.counit.naturality c
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have ht' : L'.map (adj'.homEquiv W' U' t') ≫ adj'.counit.app U' = t' := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj'.homEquiv W' U').symm_apply_apply t'
  rw [ht']
  rw [reassoc_of% (mateEquiv_counit adj adj' ex.inv U)]
  have he := ex.inv.naturality (adj.homEquiv W U t)
  dsimp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [← H.map_comp_assoc]
  rw [← adj.homEquiv_counit, Equiv.symm_apply_apply]
  have h := congrArg (fun k ↦ ex.inv.app W ≫ k) ht
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h.symm

private theorem restrict_orientation_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (H : D ⥤ D') (G : C ⥤ C') (S : C ⥤ D) (S' : C' ⥤ D')
    (e : S ⋙ H ≅ G ⋙ S') {W V : C} {W' V' : C'} {U : D} {U' : D'}
    (cs : S.obj W ≅ U) (cs' : S'.obj W' ≅ U') (cb : H.obj U ≅ U')
    (cv : G.obj W ⟶ W') (ev : G.obj V ⟶ V') (a : W ⟶ V) (a' : W' ⟶ V')
    (ha : G.map a ≫ ev = cv ≫ a')
    (hc : H.map cs.inv ≫ e.hom.app W ≫ S'.map cv = cb.hom ≫ cs'.inv) :
    H.map (cs.inv ≫ S.map a) ≫ e.hom.app V ≫ S'.map ev =
      cb.hom ≫ cs'.inv ≫ S'.map a' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% e.hom.naturality a]
  change H.map cs.inv ≫ e.hom.app W ≫ S'.map (G.map a) ≫ S'.map ev = _
  rw [← S'.map_comp, ha, S'.map_comp]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ S'.map a') hc

/-- The integration adjunct restricted to zero commutes with the actual smooth exchange.
Source: blueprint latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, base-change paragraph.
(blueprint: lem-pur-vector-zero-section-integration-base-change).

Proof: transpose the compact-support base-change equation for integration under the
Brown adjunctions. The mate of inverse compact-support exchange is the specified
exceptional exchange. At the coefficient unit, the projection unit equation removes
the tensor unitors. To include arbitrary Cartesian presentations, factor the bundle
map through the canonical pullback bundle and an isomorphism preserving zero. The
zero-section class is carried to the zero-section class and integrates to one. The
top trace source is a degree-zero rank-one sheaf, so this class fixes the normalized
trace under that isomorphism. Thus the trace equation holds without linearity.
Pull this equality along the new zero section, commute pullbacks
using the section square, and cancel the two Tate pullback comparisons. Their ordered
powers respect composition, so the remaining source comparison is precisely the Tate
comparison on the base. This also applies to an isomorphism between two bundle models,
without requiring a chosen linear trivialization. Rank zero uses the unit comparison;
the same equality applies to the empty base.
-/
theorem vector_zero_section_integration_baseChange (P : PurityFiniteSetting.{u})
    (B B' : Scheme.{u}) [IsNoetherian B] [IsNoetherian B'] (aB : B ⟶ Spec (.of P.field.k))
    (aB' : B' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType aB'] [QuasiCompact aB']
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    (b : B' ⟶ B)
    (v : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F)
    (sq : IsPullback v (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) b)
    (hz : VectorBundleZeroSection.zero B' d F' ≫ v =
      b ≫ VectorBundleZeroSection.zero B d F) :
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    letI := (Etale.vectorIntegration_geometry B' d F').1
    letI := (Etale.vectorIntegration_geometry B' d F').2.1
    letI := (VectorBundleZeroSection.finite_type_frames P.field.k B aB d F).choose_spec.2.2.2.2.2.1
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B' d F') aB'
    letI := Dnc.invertibleExponent P (VectorBundleZeroSection.π B d F ≫ aB)
    (Etale.ordinaryFinitePullback P.Coefficient b).map (vectorBetaInverse P B aB d F) ≫
        (Dnc.sectionBaseChange P.Coefficient d (VectorBundleZeroSection.π B d F) sq
          (VectorBundleZeroSection.zero B d F) (VectorBundleZeroSection.zero B' d F') hz).hom =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates
        (purityTwistTransport P.Coefficient P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
        b (P.diagonalExponent_isUnit aB) d).hom ≫ vectorBetaInverse P B' aB' d F' := by
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B' d F').1
  let := (Etale.vectorIntegration_geometry B' d F').2.1
  let := (VectorBundleZeroSection.finite_type_frames P.field.k B aB d F).choose_spec.2.2.2.2.2.1
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B' d F') aB'
  let := Dnc.invertibleExponent P (VectorBundleZeroSection.π B d F ≫ aB)
  let tw := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  let c (T S : Scheme.{u}) (f : T ⟶ S) (aS : S ⟶ Spec (.of P.field.k)) :=
    Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates tw f (P.diagonalExponent_isUnit aS) d
  let π := VectorBundleZeroSection.π B d F
  let π' := VectorBundleZeroSection.π B' d F'
  let z := VectorBundleZeroSection.zero B d F
  let z' := VectorBundleZeroSection.zero B' d F'
  let L := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) π
  let L' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) π'
  let adj := Etale.rightDerivedUpperShriekAdjunction P.Coefficient π
  let adj' := Etale.rightDerivedUpperShriekAdjunction P.Coefficient π'
  let τ := L.map (c _ _ π aB).inv ≫
    Etale.vectorBundleIntegration P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
  let τ' := L'.map (c _ _ π' aB').inv ≫
    Etale.vectorBundleIntegration P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates B' (P.diagonalExponent_isUnit aB') d F' ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B').hom
  let q := adj.homEquiv _ _ τ
  let q' := adj'.homEquiv _ _ τ'
  let G := Etale.ordinaryFinitePullback P.Coefficient v
  let H := Etale.ordinaryFinitePullback P.Coefficient b
  let S := Etale.ordinaryFinitePullback P.Coefficient z
  let S' := Etale.ordinaryFinitePullback P.Coefficient z'
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  let ex : L ⋙ H ≅ G ⋙ L' :=
    asIso (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq)
  have ht := vector_normalized_trace_cartesian P B B' aB aB' d F F' b v sq hz
  have hq := integration_mate_square adj adj' G H ex
    (c _ _ v (π ≫ aB)).hom τ τ'
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b).hom ht
  change G.map q ≫ Etale.dualizingComplexBaseChangeMap P.Coefficient sq =
    (c _ _ v (π ≫ aB)).hom ≫ q' at hq
  let e : S ⋙ H ≅ G ⋙ S' :=
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) b z).symm ≪≫
      Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        z' v (b ≫ z) hz.symm
  have hc := Etale.orderedTatePullbackSquare P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates tw z z' b v hz
    (P.diagonalExponent_isUnit (π ≫ aB)) (P.diagonalExponent_isUnit aB)
    (P.diagonalExponent_isUnit (π' ≫ aB')) d
  have hc' : H.map (c _ _ z (π ≫ aB)).inv ≫
      e.hom.app (Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates (VectorBundleZeroSection.scheme B d F) d) ≫
      S'.map (c _ _ v (π ≫ aB)).hom =
      (c _ _ b aB).hom ≫ (c _ _ z' (π' ≫ aB')).inv := by
    simpa only [e, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Category.assoc] using hc
  have hq_def : q = (c _ _ π aB).inv ≫ adj.homEquiv _ _
      (Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom) := by
    exact adj.homEquiv_naturality_left _ _
  have hq'_def : q' = (c _ _ π' aB').inv ≫ adj'.homEquiv _ _
      (Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates B' (P.diagonalExponent_isUnit aB') d F' ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B').hom) := by
    exact adj'.homEquiv_naturality_left _ _
  have hr := restrict_orientation_square H G S S' e
    (c _ _ z (π ≫ aB)) (c _ _ z' (π' ≫ aB')) (c _ _ b aB)
    (c _ _ v (π ≫ aB)).hom (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)
    q q' hq hc'
  simpa only [vectorBetaInverse, hq_def, hq'_def, c, tw, adj, adj',
    H, S, S', π, π', z, z',
    Dnc.sectionBaseChange, e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, asIso_hom, Functor.map_comp,
    Etale.sectionInvariant, Etale.ordinaryFinitePullback,
    Category.assoc] using hr

end WeilConjectures.PurityFiniteSetting.OrientationRefinement
