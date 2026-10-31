/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedModuleExtensionBinary
import WeilConjectures.AlgebraicGeometry.LocallyClosedModuleExtensionAssociativityPart
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
/-! Unit portion of locally closed model coherence. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- Coefficient unit equalities are mates of the sectionwise direct-image unit equalities.
private noncomputable abbrev ringAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleSheafAdjunction f CommRingCat.{u + 1}

private theorem ring_pull_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateIsoEquiv (ringAdj g) (ringAdj f)
      (eqToIso (congrArg (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1}) h)) =
      (eqToIso (congrArg
        (fun k ↦ proEtaleSheafDirectImage k CommRingCat.{u + 1}) h)).symm := by
  cases h
  ext : 1
  simp

private theorem ring_pull_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingInverseImageComp (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (proEtaleSheafInverseImage f CommRingCat.{u + 1})
        (proEtaleRingInverseImageId X) ≪≫ Functor.rightUnitor _ =
      eqToIso (congrArg
        (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1}) (Category.id_comp f)) := by
  let q := AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} (𝟙 X) f ≪≫
    eqToIso (congrArg
      (fun k ↦ proEtaleSheafDirectImage k CommRingCat.{u + 1}) (Category.id_comp f))
  have hq : q = Functor.isoWhiskerRight
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X)
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}) ≪≫ Functor.leftUnitor _ := by
    dsimp only [q]
    rw [AlgebraicGeometry.ProEtale.legacy_lowerStarComp_id_left]
    ext M T
    simp [AlgebraicGeometry.ProEtale.lowerStarCongr]
    rfl
  apply (conjugateIsoEquiv (ringAdj f) (ringAdj (𝟙 X ≫ f))).injective
  rw [conjugateIsoEquiv_trans _ ((ringAdj f).comp (ringAdj (𝟙 X))) _,
    conjugateIsoEquiv_trans _ ((ringAdj f).comp Adjunction.id) _,
    conjugateIsoEquiv_rightUnitor, conjugateIsoEquiv_isoWhiskerLeft,
    ring_pull_congr (Category.id_comp f)]
  simp only [proEtaleRingInverseImageComp, proEtaleRingInverseImageId,
    conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]
  change (Functor.isoWhiskerRight
    (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X)
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}) ≪≫ Functor.leftUnitor _).symm ≪≫
      AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} (𝟙 X) f = _
  rw [← hq]
  apply Iso.ext
  simp only [q, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem ring_pull_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingInverseImageComp f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (proEtaleRingInverseImageId Y)
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}) ≪≫ Functor.leftUnitor _ =
      eqToIso (congrArg
        (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1}) (Category.comp_id f)) := by
  let q := AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} f (𝟙 Y) ≪≫
    eqToIso (congrArg
      (fun k ↦ proEtaleSheafDirectImage k CommRingCat.{u + 1}) (Category.comp_id f))
  have hq : q = Functor.isoWhiskerLeft
      (proEtaleSheafDirectImage f CommRingCat.{u + 1})
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} Y) ≪≫
        Functor.rightUnitor _ := by
    dsimp only [q]
    rw [AlgebraicGeometry.ProEtale.lowerStarComp_id_right]
    ext M T
    simp [AlgebraicGeometry.ProEtale.lowerStarCongr]
    rfl
  apply (conjugateIsoEquiv (ringAdj f) (ringAdj (f ≫ 𝟙 Y))).injective
  rw [conjugateIsoEquiv_trans _ ((ringAdj (𝟙 Y)).comp (ringAdj f)) _,
    conjugateIsoEquiv_trans _ (Adjunction.id.comp (ringAdj f)) _,
    conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_isoWhiskerRight,
    ring_pull_congr (Category.comp_id f)]
  simp only [proEtaleRingInverseImageComp, proEtaleRingInverseImageId,
    conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]
  change (Functor.isoWhiskerLeft (proEtaleSheafDirectImage f CommRingCat.{u + 1})
    (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} Y) ≪≫
      Functor.rightUnitor _).symm ≪≫
        AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} f (𝟙 Y) = _
  rw [← hq]
  apply Iso.ext
  simp only [q, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem immersion_eq {S X : LocallyClosedCoefficients.{u}}
    {a b : LocallyClosedCoefficientImmersion S X} (h : a.hom = b.hom)
    (hc : (eqToIso (congrArg
      (fun f ↦ proEtaleSheafInverseImage f CommRingCat.{u + 1}) h)).app X.ring ≪≫
        b.coefficient = a.coefficient) : a = b := by
  rcases a with ⟨f, hf, c⟩
  rcases b with ⟨g, hg, d⟩
  dsimp only at h
  cases h
  have hc' : d = c := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.app_hom, eqToIso.hom, eqToHom_refl,
      NatTrans.id_app, Category.id_comp] using congrArg Iso.hom hc
  cases hc'
  rfl

private theorem immersion_comp_id {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :
    a.comp (.identity S) = a := by
  apply immersion_eq (a := a.comp (.identity S)) (b := a) (Category.id_comp a.hom)
  apply Iso.ext
  have hu := congrArg (fun e ↦ e.hom.app X.ring) (ring_pull_left_unit a.hom)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hu
  erw [Category.comp_id] at hu
  change _ = (proEtaleRingInverseImageComp (𝟙 S.scheme) a.hom).hom.app X.ring ≫
    (proEtaleSheafInverseImage (𝟙 S.scheme) CommRingCat.{u + 1}).map a.coefficient.hom ≫
      (proEtaleRingInverseImageId S.scheme).hom.app S.ring
  rw [(proEtaleRingInverseImageId S.scheme).hom.naturality a.coefficient.hom]
  dsimp only [Functor.id_map]
  rw [← Category.assoc, hu]
  rfl

private theorem immersion_id_comp {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :
    (LocallyClosedCoefficientImmersion.identity X).comp a = a := by
  apply immersion_eq (a := (LocallyClosedCoefficientImmersion.identity X).comp a)
    (b := a) (Category.comp_id a.hom)
  apply Iso.ext
  have hu := congrArg (fun e ↦ e.hom.app X.ring) (ring_pull_right_unit a.hom)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hu
  erw [Category.comp_id ((proEtaleSheafInverseImage a.hom CommRingCat.{u + 1}).map
    ((proEtaleRingInverseImageId X.scheme).hom.app X.ring))] at hu
  change _ = (proEtaleRingInverseImageComp a.hom (𝟙 X.scheme)).hom.app X.ring ≫
    (proEtaleSheafInverseImage a.hom CommRingCat.{u + 1}).map
      ((proEtaleRingInverseImageId X.scheme).hom.app X.ring) ≫ a.coefficient.hom
  rw [← Category.assoc, hu]
  rfl

-- Cancel the outer copy of a fully faithful idempotent endofunctor.
private noncomputable def idempotentUnit
    {C : Type*} [Category C] (I : C ⥤ C) [I.Full] [I.Faithful]
    (m : I ⋙ I ≅ I) : I ≅ 𝟭 C :=
  Functor.fullyFaithfulCancelRight I (m ≪≫ (Functor.leftUnitor I).symm)

private theorem idempotentUnit_map
    {C : Type*} [Category C] (I : C ⥤ C) [I.Full] [I.Faithful]
    (m : I ⋙ I ≅ I) (M : C) :
    I.map ((idempotentUnit I m).hom.app M) = m.hom.app M := by
  simp [idempotentUnit]

private theorem inner_of_associative
    {C D : Type*} [Category C] [Category D]
    (I : C ⥤ C) [I.Full] [I.Faithful] (F : C ⥤ D)
    (m : I ⋙ I ≅ I) (l : I ⋙ F ≅ F)
    (h : ∀ M, F.map (m.hom.app M) = l.hom.app (I.obj M)) :
    l = Functor.isoWhiskerRight (idempotentUnit I m) F ≪≫ Functor.leftUnitor F := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  change l.hom.app M = F.map ((idempotentUnit I m).hom.app M) ≫ 𝟙 _
  rw [Category.comp_id]
  apply (cancel_epi (F.map (m.hom.app M))).mp
  have hn := l.hom.naturality ((idempotentUnit I m).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [idempotentUnit_map, ← h M] at hn
  exact hn

private theorem outer_of_associative
    {C D : Type*} [Category C] [Category D]
    (I : D ⥤ D) [I.Full] [I.Faithful] (F : C ⥤ D)
    (m : I ⋙ I ≅ I) (r : F ⋙ I ≅ F)
    (h : ∀ M, I.map (r.hom.app M) = m.hom.app (F.obj M)) :
    r = Functor.isoWhiskerLeft F (idempotentUnit I m) ≪≫ Functor.rightUnitor F := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  change r.hom.app M = (idempotentUnit I m).hom.app (F.obj M) ≫ 𝟙 _
  rw [Category.comp_id]
  apply I.map_injective
  rw [h, idempotentUnit_map]

private theorem gamma_congr_inner (G : LocallyClosedModelComposition.{u})
    {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    {b b' : LocallyClosedCoefficientImmersion T S} (h : b = b') :
    Functor.isoWhiskerRight
        (eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h))
        a.modelExtension ≪≫ G.gamma a b' =
      G.gamma a b ≪≫ eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension
        (congrArg (fun k ↦ a.comp k) h)) := by
  cases h
  simp

private theorem gamma_congr_outer (G : LocallyClosedModelComposition.{u})
    {S X T : LocallyClosedCoefficients.{u}}
    {a a' : LocallyClosedCoefficientImmersion S X}
    (b : LocallyClosedCoefficientImmersion T S) (h : a = a') :
    Functor.isoWhiskerLeft b.modelExtension
        (eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h)) ≪≫
        G.gamma a' b =
      G.gamma a b ≪≫ eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension
        (congrArg (fun k ↦ k.comp b) h)) := by
  cases h
  simp

private noncomputable def innerComparison (G : LocallyClosedModelComposition.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  G.gamma a (.identity S) ≪≫
    eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension (immersion_comp_id a))

private noncomputable def outerComparison (G : LocallyClosedModelComposition.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  G.gamma (.identity X) a ≪≫
    eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension (immersion_id_comp a))

-- Associativity for (a, 1, 1), with the coefficient equalities transported explicitly.
private theorem inner_comparison_assoc (G : LocallyClosedModelComposition.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (M : proEtaleRingModules S.scheme S.ring) :
    a.modelExtension.map ((innerComparison G (.identity S)).hom.app M) =
      (innerComparison G a).hom.app
        ((LocallyClosedCoefficientImmersion.identity S).modelExtension.obj M) := by
  let i := LocallyClosedCoefficientImmersion.identity S
  obtain ⟨h, hh⟩ := locallyClosedModel_associativity_part G a i i
  let p : a.comp (i.comp i) = a :=
    (congrArg (fun b ↦ a.comp b) (immersion_comp_id i)).trans (immersion_comp_id a)
  have hl : G.gamma a (i.comp i) ≪≫
      eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension p) =
      Functor.isoWhiskerRight
        (eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension
          (immersion_comp_id i)))
        a.modelExtension ≪≫ innerComparison G a := by
    symm
    simpa only [innerComparison, Iso.trans_assoc, eqToIso_trans] using
      congrArg (fun e ↦ e ≪≫ eqToIso
        (congrArg LocallyClosedCoefficientImmersion.modelExtension (immersion_comp_id a)))
        (gamma_congr_inner G a (immersion_comp_id i))
  have hr : G.gamma (a.comp i) i ≪≫
      eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) ≪≫
      eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension p) =
        Functor.isoWhiskerLeft i.modelExtension
          (eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension
            (immersion_comp_id a))) ≪≫ innerComparison G a := by
    symm
    simpa only [innerComparison, Iso.trans_assoc, eqToIso_trans] using
      congrArg (fun e ↦ e ≪≫ eqToIso
        (congrArg LocallyClosedCoefficientImmersion.modelExtension (immersion_comp_id a)))
        (gamma_congr_outer G i (immersion_comp_id a))
  have he := congrArg (fun e ↦ e ≪≫
    eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension p)) hh
  simp only [Iso.trans_assoc] at he
  rw [hl, hr] at he
  have hm := congrArg (fun e ↦ e.hom.app M) he
  apply (cancel_mono ((innerComparison G a).hom.app M)).mp
  simpa only [innerComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.map_comp, Category.id_comp, Category.assoc] using hm

-- Associativity for (1, 1, a) gives the other unit law by faithful cancellation.
private theorem outer_comparison_assoc (G : LocallyClosedModelComposition.{u})
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    (M : proEtaleRingModules S.scheme S.ring) :
    (LocallyClosedCoefficientImmersion.identity X).modelExtension.map
        ((outerComparison G a).hom.app M) =
      (innerComparison G (.identity X)).hom.app (a.modelExtension.obj M) := by
  let i := LocallyClosedCoefficientImmersion.identity X
  obtain ⟨h, hh⟩ := locallyClosedModel_associativity_part G i i a
  let p : i.comp (i.comp a) = a :=
    (congrArg (fun b ↦ i.comp b) (immersion_id_comp a)).trans (immersion_id_comp a)
  have hl : G.gamma i (i.comp a) ≪≫
      eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension p) =
      Functor.isoWhiskerRight
        (eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension
          (immersion_id_comp a)))
        i.modelExtension ≪≫ outerComparison G a := by
    symm
    simpa only [outerComparison, Iso.trans_assoc, eqToIso_trans] using
      congrArg (fun e ↦ e ≪≫ eqToIso
        (congrArg LocallyClosedCoefficientImmersion.modelExtension (immersion_id_comp a)))
        (gamma_congr_inner G i (immersion_id_comp a))
  have hr : G.gamma (i.comp i) a ≪≫
      eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) ≪≫
      eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension p) =
        Functor.isoWhiskerLeft a.modelExtension
          (eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension
            (immersion_comp_id i))) ≪≫ outerComparison G a := by
    symm
    simpa only [outerComparison, Iso.trans_assoc, eqToIso_trans] using
      congrArg (fun e ↦ e ≪≫ eqToIso
        (congrArg LocallyClosedCoefficientImmersion.modelExtension (immersion_id_comp a)))
        (gamma_congr_outer G a (immersion_comp_id i))
  have he := congrArg (fun e ↦ e ≪≫
    eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension p)) hh
  simp only [Iso.trans_assoc] at he
  rw [hl, hr] at he
  have hm := congrArg (fun e ↦ e.hom.app M) he
  apply (cancel_mono ((outerComparison G a).hom.app M)).mp
  simpa only [outerComparison, innerComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.map_comp, Category.id_comp, Category.assoc] using hm

/-- The identity comparison and its two normalized unit laws.

Source: Stacks Project, Tag 02V0; the identity and unit portions of the locally closed
extension coherence argument.

Proof: the coefficient immersions satisfy `a ∘ 1 = a` and `1 ∘ a = a`, including their
coefficient isomorphisms, by conjugating the sectionwise direct-image unit laws of the
pro-etale pushforwards along the inverse-image adjunctions. Transporting `γ_{1,1}` along
`1 ∘ 1 = 1` gives `μ_X : I_X I_X ≅ I_X` for `I_X` the model extension of the identity;
since `I_X` is fully faithful, cancelling its outer copy defines `e_X : I_X ≅ 1` with
`I_X(e_X) = μ_X`. Associativity
(`locallyClosedModel_associativity_part`) for `(a, 1, 1)` gives
`F_a(μ_S) = γ_{a,1}(I_S)`, whence `γ_{a,1} = F_a e_S` by naturality and cancellation; for
`(1, 1, a)` it gives `I_X(γ_{1,a}) = μ_X(F_a) = I_X(e_X F_a)`, whence `γ_{1,a} = e_X F_a`
by faithfulness of `I_X`.
(blueprint: lem-sfb-locally-closed-module-extension-unit-part).
-/
theorem locallyClosedModel_unit_part (G : LocallyClosedModelComposition.{u}) :
    ∃ identity : ∀ X : LocallyClosedCoefficients.{u},
        (LocallyClosedCoefficientImmersion.identity X).modelExtension ≅
          𝟭 (proEtaleRingModules X.scheme X.ring),
      (∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
        ∃ h : a.comp (.identity S) = a,
          G.gamma a (.identity S) ≪≫
              eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) =
            Functor.isoWhiskerRight (identity S) a.modelExtension ≪≫
              Functor.leftUnitor a.modelExtension) ∧
      (∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
        ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
          G.gamma (.identity X) a ≪≫
              eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) =
            Functor.isoWhiskerLeft a.modelExtension (identity X) ≪≫
              Functor.rightUnitor a.modelExtension) := by
  classical
  refine ⟨fun X ↦ idempotentUnit _ (innerComparison G (.identity X)), ?_, ?_⟩
  · intro S X a
    refine ⟨immersion_comp_id a, ?_⟩
    rw [← innerComparison]
    exact inner_of_associative _ _ _ _ (inner_comparison_assoc G a)
  · intro S X a
    refine ⟨immersion_id_comp a, ?_⟩
    rw [← outerComparison]
    exact outer_of_associative _ _ _ _ (outer_comparison_assoc G a)
end AlgebraicGeometry.Scheme
