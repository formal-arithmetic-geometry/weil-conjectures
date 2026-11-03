/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedComparisonCoordinates

/-! # The locally closed comparison: a single assembly step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The counit-normalized gamma has the relative Hom formula after transport by
its inverse and the comparison unit. This is an equality of morphisms; invertibility
of the transport is a separate consequence of boundedness of the target.
Source: blueprint site-comparison proof, paragraph 2; parent locally closed proof,
Steps 7--11 (blueprint: lem-sf-locally-closed-relative-hom-identity).

Proof: first take K = C_S L and the identity origin witness. Full faithfulness of C_T
at the bounded-below target M gives the unique etale map h0 with Delta_L h = C_T(h0).
Write g0 for its transpose under the pasted etale adjunction. Naturality of Delta
at g0, followed by the assumed counit equation, shows that the pro-etale transpose
of h is C_S(g0) gamma_M. Cancel gamma_M against its inverse in the asserted formula.
The remaining expression is C_S(g0 r_M X(eta_M)), with r the specified normalized
right-adjoint identification and X the closure exceptional functor.
The normalization axiom of B identifies its Hom bijection with the comparison
adjunction followed by the closure etale adjunction. Naturality of the comparison
unit and the counit-compatible right-adjoint identification r give exactly the
same expression. For a general witness w, apply naturality in the source to w.inv
and w.hom; functoriality cancels the inverse pair. This proves the equation for every
w and every normalized B, without choosing either an origin or a comparison-class
adjunction. In particular scalar twists and empty-source cases obey the same equation.
The named compact-support comparison appears explicitly in the input map of B, so
this calculation does not require choosing another comparison with the same endpoints. -/
theorem locallyClosedRelativeHomIdentity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)]
    (adjoints : LocallyClosedComparisonAdjoints A c)
    (hb : ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
      _root_.DerivedCategory.TStructure.t.plus ((adjoints.etaleRight v).obj M.obj))
    (gamma :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ adjoints.etaleRight v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        adjoints.proetaleRight v
)
    (hc : ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
    (locallyClosedExtensionComparison A c v).hom.app
        ⟨(adjoints.etaleRight v).obj M.obj, hb M⟩ ≫
      (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
      (adjoints.proetalePasted v).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        ((adjoints.etalePasted v).counit.app M.obj)) :
      ∀ (B : FixedComparisonClassAdjunction A (c ≫ v)
        (locallyClosedImageCompactification (c ≫ v))
        (locallyClosedEtaleExceptional A (c ≫ v))
        (Adjunction.ofIsLeftAdjoint _)
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S)
        _root_.DerivedCategory.TStructure.t.plus)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S K)
      (M : Etale.BoundedConstructibleDerivedCategory A T)
      (hM : _root_.DerivedCategory.TStructure.t.plus
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj))
      (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (w : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj L.obj ≅ K)
      (h : (locallyClosedProEtaleExtension A c v).obj K ⟶
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj),
    ((adjoints.proetalePasted v).homEquiv _ _) h ≫ (gamma.inv.app M ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
          ((locallyClosedEtaleRightIso v adjoints).hom.app M.obj ≫
            (locallyClosedEtaleExceptional A (c ≫ v)).map
              ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M.obj))) =
      B.homEquiv (locallyClosedImageCompactification (c ≫ v)) K hK
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) hM
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
            (locallyClosedImageCompactification (c ≫ v))).map w.inv ≫
          (fixedCompactSupportComparisonIso A
            (locallyClosedImageCompactification (c ≫ v))).hom.app L ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
            ((locallyClosedEtaleSupportIso A c v).inv.app L.obj) ≫
          (locallyClosedExtensionComparison A c v).hom.app L ≫
          (locallyClosedProEtaleExtension A c v).map w.hom ≫ h)
 := by
  intro B K hK M hM L w h
  let CS := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
  let CT := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let U := (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor
  let Fe := locallyClosedEtaleExtension A c v
  let Fp := locallyClosedProEtaleExtension A c v
  let ae := adjoints.etalePasted v
  let ap := adjoints.proetalePasted v
  let q := locallyClosedEtaleSupportIso A c v
  let r := locallyClosedEtaleRightIso v adjoints
  let eta := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit
  let hl := Fp.map w.hom ≫ h
  obtain ⟨k, b, hkb, hz⟩ := M.property.2
  have hMb : _root_.DerivedCategory.TStructure.t.plus M.obj :=
    ⟨k, (_root_.DerivedCategory.isGE_iff M.obj k).2 (fun i hi ↦ hz i (.inl hi))⟩
  obtain ⟨h0, hh0⟩ :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map
      (Fe.obj L.obj) M.obj hMb).2
        ((locallyClosedExtensionComparison A c v).hom.app L ≫ hl)
  let g0 := ae.homEquiv L.obj M.obj h0
  have hg0 : Fe.map g0 ≫ ae.counit.app M.obj = h0 :=
    (ae.homEquiv L.obj M.obj).symm_apply_apply h0
  have hn := (locallyClosedExtensionComparison A c v).hom.naturality
    (show L ⟶ ⟨(adjoints.etaleRight v).obj M.obj, hb M⟩ from ObjectProperty.homMk g0)
  change CT.map (Fe.map g0) ≫ _ = _ ≫ Fp.map (CS.map g0) at hn
  have htranspose : ap.homEquiv _ _ hl = CS.map g0 ≫ gamma.hom.app M := by
    apply (ap.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Fp.map_comp]
    apply (cancel_epi ((locallyClosedExtensionComparison A c v).hom.app L)).1
    calc
      _ = CT.map h0 := hh0.symm
      _ = CT.map (Fe.map g0) ≫ CT.map (ae.counit.app M.obj) := by
        rw [← CT.map_comp, hg0]
      _ = _ := by
        rw [← hc M]
        simp only [Category.assoc]
        rw [← Category.assoc, hn]
        simp only [Category.assoc]
        rfl
  have hKr : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S (CS.obj L.obj) :=
    DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property
  let ac := Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (locallyClosedImageCompactification (c ≫ v)))
  let a0 := q.inv.app L.obj ≫ h0 ≫ eta.app M.obj
  have hcbase : ac.homEquiv L.obj M.obj (q.inv.app L.obj ≫ h0) =
      g0 ≫ r.hom.app M.obj := by
    erw [← ac.homEquiv_ofNatIsoLeft_apply q.symm]
    apply ((ac.ofNatIsoLeft q.symm).homEquiv L.obj M.obj).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    change h0 = Fe.map (g0 ≫ r.hom.app M.obj) ≫ _
    rw [Functor.map_comp, Category.assoc]
    erw [Adjunction.rightAdjointUniq_hom_app_counit]
    exact hg0.symm
  have hc0 : ac.homEquiv L.obj _ a0 =
      g0 ≫ r.hom.app M.obj ≫
        (locallyClosedEtaleExceptional A (c ≫ v)).map (eta.app M.obj) := by
    calc
      _ = ac.homEquiv L.obj M.obj (q.inv.app L.obj ≫ h0) ≫
          (locallyClosedEtaleExceptional A (c ≫ v)).map (eta.app M.obj) := by
        simpa only [a0, Category.assoc] using
          ac.homEquiv_naturality_right (q.inv.app L.obj ≫ h0) (eta.app M.obj)
      _ = _ := by rw [hcbase, Category.assoc]
  have hB := B.homEquiv_normalized L hKr (CT.obj M.obj) hM a0
  have ha0 :
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).symm a0 =
        CT.map (q.inv.app L.obj) ≫
          (locallyClosedExtensionComparison A c v).hom.app L ≫ hl := by
    apply ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    dsimp only [a0]
    rw [← hh0, ← CT.map_comp]
    simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
      eta.naturality (q.inv.app L.obj ≫ h0)
  erw [ha0, hc0, CS.map_comp, CS.map_comp] at hB
  have hBn := B.naturality_left (locallyClosedImageCompactification (c ≫ v)) K
    (CS.obj L.obj) hK hKr (CT.obj M.obj) hM w.inv
    ((fixedCompactSupportComparisonIso A
        (locallyClosedImageCompactification (c ≫ v))).hom.app L ≫
      CT.map (q.inv.app L.obj) ≫
        (locallyClosedExtensionComparison A c v).hom.app L ≫ hl)
  rw [hB] at hBn
  have hw : ap.homEquiv _ _ h = w.inv ≫ ap.homEquiv _ _ hl := by
    rw [← ap.homEquiv_naturality_left]
    congr 1
    change h = Fp.map w.inv ≫ Fp.map w.hom ≫ h
    rw [← Fp.map_comp_assoc, Iso.inv_hom_id, Fp.map_id, Category.id_comp]
  rw [hw, htranspose]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simpa only [hl, Fe, Fp, CS, CT, U, q, r, eta, Category.assoc,
    Functor.map_comp, g0, Adjunction.homEquiv_unit] using hBn.symm

end AlgebraicGeometry.ProEtale
