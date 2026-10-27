/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.CommonQuotientPullbackData
import Sheaf.Paper.OrdinaryCommonQuotientTower
import all Sheaf.Paper.RingedCoefficientPullbackComparison

/-! # Ordinary common-quotient scalar insertion

Source: Stacks Project, Tags 06YY, 0G7E, 03EK, 03EL.
(blueprint: lem-weil-pbc-common-quotient-ordinary-insertion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open WeilConjectures.SemilinearSections (Mod D)
open SheafOfModules.RingedCoefficientProjection
open SheafOfModules.SuccessiveDerivedQuotient (restriction sectionTensor)
namespace SheafOfModules.CommonQuotientPullback

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : SuccessiveDerivedQuotient.Normalization (J := J) pY)
  (nX : SuccessiveDerivedQuotient.Normalization (J := K) pX)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
  {B' : Sheaf K CommRingCat.{r}} (a : g.rings.obj B ⟶ B')


private def ordinary_model_iso {A S : Sheaf J CommRingCat.{r}}
    (p : Scalars.{c, v, r} J) (q : A ⟶ S) (F : DerivedChangeOfRingsCochainModel q) :
    (p q).ordinary ≅ F.E :=
  NatIso.ofComponents (fun M ↦ eqToIso ((p q).obj_eq M) ≪≫
    (eqToIso (F.obj_eq M)).symm) (by
      intro M N f
      change (p q).ordinary.map f ≫
          (eqToHom ((p q).obj_eq N) ≫ eqToHom (F.obj_eq N).symm) =
        (eqToHom ((p q).obj_eq M) ≫ eqToHom (F.obj_eq M).symm) ≫ F.E.map f
      rw [(p q).map_eq, F.map_eq]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc])

private theorem ordinary_model_iso_sections {A S : Sheaf J CommRingCat.{r}}
    (p : Scalars.{c, v, r} J) (q : A ⟶ S) (F : DerivedChangeOfRingsCochainModel q)
    (M : Mod J A) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((ordinary_model_iso p q F).hom.app M).val.app U (sectionTensor (p q) M U s x) =
      (eqToHom (F.obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
          (s ⊗ₜ[A.obj.obj U, (q.hom.app U).hom] x)) := by
  change ((eqToHom ((p q).obj_eq M) ≫ eqToHom (F.obj_eq M).symm).val.app U)
    ((eqToHom ((p q).obj_eq M).symm).val.app U _) = _
  change ((eqToHom ((p q).obj_eq M).symm ≫ eqToHom ((p q).obj_eq M) ≫
    eqToHom (F.obj_eq M).symm).val.app U) _ = _
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rfl

private theorem ordinary_quotient_iso (p : Scalars.{c, v, r} J)
    (D : CommonQuotientTowerPresentation φ) (n : ℕ) :
    ∃ e : restriction φ ⋙ (p (D.projection n)).ordinary ≅
        (p (D.extensionProjection n)).ordinary,
      ∀ (M : Mod J B) (U : Cᵒᵖ) (s : (D.S.obj (op n)).obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U
          (sectionTensor (p (D.projection n)) ((restriction φ).obj M) U s x) =
        sectionTensor (p (D.extensionProjection n)) M U s x := by
  classical
  let A (n : ℕ) := (nonempty_derivedChangeOfRingsCochainModel (D.projection n)).some
  let B (n : ℕ) :=
    (nonempty_derivedChangeOfRingsCochainModel (D.extensionProjection n)).some
  obtain ⟨O⟩ := nonempty_ordinaryCommonQuotientTower D A B
  let l := Functor.isoWhiskerLeft (restriction φ) (ordinary_model_iso p (D.projection n) (A n))
  let r := ordinary_model_iso p (D.extensionProjection n) (B n)
  refine ⟨l ≪≫ O.ordinary n ≪≫ r.symm, ?_⟩
  intro M U s x
  change (r.inv.app M).val.app U
    (((O.ordinary n).hom.app M).val.app U
      ((l.hom.app M).val.app U (sectionTensor _ _ U s x))) = _
  erw [ordinary_model_iso_sections p (D.projection n) (A n) ((restriction φ).obj M) U s x]
  erw [O.ordinary_sections n M U s x]
  change (r.inv.app M).val.app U
    ((eqToHom ((B n).obj_eq M).symm).val.app U
      ((toSheafify J (changeOfRingsPresheaf (D.extensionProjection n) M).presheaf).app U
        (s ⊗ₜ[_, ((D.extensionProjection n).hom.app U).hom] x))) = _
  erw [← ordinary_model_iso_sections p (D.extensionProjection n) (B n) M U s x]
  exact congrArg (fun f ↦ f.val.app U (sectionTensor _ M U s x)) (r.hom_inv_id_app M)

private theorem insertion_comp {A S T : Sheaf J CommRingCat.{r}}
    (p : Scalars.{c, v, r} J) (N : SuccessiveDerivedQuotient.Normalization p)
    (q : A ⟶ S) (t : S ⟶ T) (M : Mod J A) :
    insertion N q M ≫ insertion N t ((p q).ordinary.obj M) ≫
        (underlying T).map ((N.ordinary q t).hom.app M) = insertion N (q ≫ t) M := by
  ext U x
  change ((N.ordinary q t).hom.app M).val.app U
    (((N.ordinaryAdjunction t).unit.app _).val.app U
      (((N.ordinaryAdjunction q).unit.app M).val.app U x)) = _
  rw [N.ordinary_unit, N.ordinary_unit, N.ordinary_hom, map_one, one_mul]
  exact (N.ordinary_unit (q ≫ t) M U x).symm

private theorem insertion_congr {A S : Sheaf J CommRingCat.{r}}
    (p : Scalars.{c, v, r} J) (N : SuccessiveDerivedQuotient.Normalization p)
    (q t : A ⟶ S) (h : q = t) (M : Mod J A) :
    insertion N q M ≫ (underlying S).map
      ((eqToIso (congrArg (fun f ↦ (p f).ordinary) h)).hom.app M) =
        insertion N t M := by
  subst t
  simp

private theorem insertion_inverse_comparison [PreservesFiniteLimits uInv]
    (e : Comparisons g nY nX) {A S : Sheaf J CommRingCat.{r}} (q : A ⟶ S)
    (M : Mod J A) :
    insertion nX (g.rings.map q) ((g.inverse A).modules.obj M) ≫
        (underlying (g.rings.obj S)).map ((e.ordinary q).inv.app M) =
      (g.inverse A).moduleUnderlying.hom.app M ≫ uInv.map (insertion nY q M) ≫
        (g.inverse S).moduleUnderlying.inv.app ((pY q).ordinary.obj M) := by
  have h := congrArg (fun f ↦ (g.inverse A).moduleUnderlying.hom.app M ≫ f ≫
    (underlying (g.rings.obj S)).map ((e.ordinary q).inv.app M))
      (e.ordinary_insertion q M)
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc] at h
  erw [(underlying (g.rings.obj S)).map_id, Category.comp_id] at h
  exact h.symm

variable (Q : CommonQuotientTowerPresentation φ)
  (b : (Functor.const ℕᵒᵖ).obj B' ⟶ Q.S ⋙ g.rings)


private theorem quotient_locallySurjective [PreservesFiniteLimits uInv] (n : ℕ) :
    Presheaf.IsLocallySurjective K (quotient g φ Q n).hom := by
  let UJ := sheafCompose J (CategoryTheory.forget CommRingCat.{r})
  let UK := sheafCompose K (CategoryTheory.forget CommRingCat.{r})
  have hq : Sheaf.IsLocallySurjective (Q.projection n) := Q.q_surjective n
  have h0 : Sheaf.IsLocallySurjective (UJ.map (Q.projection n)) := inferInstance
  have : Epi (UJ.map (Q.projection n)) := Sheaf.epi_of_isLocallySurjective _
  let := adj.isLeftAdjoint
  have : Epi (uInv.map (UJ.map (Q.projection n))) := inferInstance
  have hn := g.rings_naturality (Q.projection n)
  have h : Epi ((g.inverse R).ringUnderlying.hom ≫ UK.map (quotient g φ Q n)) := by
    rw [← hn]
    infer_instance
  have : Epi (UK.map (quotient g φ Q n)) :=
    epi_of_epi (g.inverse R).ringUnderlying.hom _
  have : HasSheafify K (Type r) := hasSheafifyEssentiallySmallSite K (Type r)
  have hlocal : Sheaf.IsLocallySurjective (UK.map (quotient g φ Q n)) :=
    (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance
  exact (Presheaf.isLocallySurjective_iff_whisker_forget K
    (quotient g φ Q n).hom).mpr hlocal

set_option maxHeartbeats 400000 in
-- The two quotient adjunctions have independently normalized underlying presentations.
include nY nX in
/-- The ordinary scalar insertion becomes invertible after extension to a common
quotient. This is an assertion on module sheaves, with no derived or flatness assumptions.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
(blueprint: lem-weil-pbc-common-quotient-ordinary-insertion).

Proof: inverse image preserves epimorphisms of sheaves of sets, being a left
adjoint. The ring-underlying comparisons therefore transport local surjectivity
of the source quotient to its inverse image. Together with the given pushout
squares this constructs the target common-quotient tower. The existing ordinary
common-quotient comparison identifies restriction followed by scalar extension
with extension along the second quotient projection, preserving s tensor x.
Use it on both sites. Transport the source comparison through inverse image by
the normalized ordinary coefficient tensor comparison. Compose the target
comparison with ordinary scalar associativity along a and the second quotient
projection, then with the given equality of ring maps. This gives isomorphisms
from the reduced source and target to the same quotient-module functor. The
coefficient comparison insertion equation and naturality of moduleUnderlying
identify the source isomorphism on the scalar-extension unit. On the target,
the common-quotient section formula and normalized associativity identify twice
inserting 1 with the composite insertion. By adjunction and faithfulness of
underlying sheaves, extension of the specified insertion followed by the target
isomorphism equals the source isomorphism. Cancel the target isomorphism to prove
invertibility. This checks actual quotient-linear module morphisms, uses local
surjectivity rather than surjectivity on sections, and also covers the zero ring. -/
theorem ordinary_insertion_reduction_isIso [PreservesFiniteLimits uInv]
    (hquotient : ∀ n : ℕ, IsPushout (g.rings.map φ ≫ a)
      (quotient g φ Q n) (b.app (op n)) (𝟙 _))
    (hcompatible : ∀ n : ℕ, a ≫ b.app (op n) = g.rings.map (Q.extensionProjection n))
    (δ : ordinarySource g φ ⟶ ordinaryTarget g (pX := pX) φ a)
    (hδ : ∀ (M : Mod J B) (U : Xᵒᵖ)
      (x : ((g.inverse R).modules.obj ((restriction φ).obj M)).val.obj U),
      (δ.app M).val.app U x = sectionTensor (pX a) ((g.inverse B).modules.obj M) U 1
        (((g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
          (g.inverse B).moduleUnderlying.inv.app M).hom.app U x))
    (n : ℕ) : IsIso (Functor.whiskerRight δ (pX (quotient g φ Q n)).ordinary) := by
  classical
  obtain ⟨e⟩ := coefficientPullbackComparisons g nY nX
  let QX : CommonQuotientTowerPresentation (g.rings.map φ ≫ a) :=
    { S := Q.S ⋙ g.rings
      q :=
        { app := fun k ↦ g.rings.map (Q.q.app k)
          naturality := by
            intro j k f
            have h := congrArg g.rings.map (Q.q.naturality f)
            dsimp only [Functor.const_obj_map] at h
            erw [Functor.map_comp, g.rings.map_id] at h
            erw [Category.id_comp, g.rings.map_comp] at h
            change 𝟙 (g.rings.obj R) ≫ g.rings.map (Q.q.app k) =
              g.rings.map (Q.q.app j) ≫ g.rings.map (Q.S.map f)
            rw [Category.id_comp]
            exact h }
      b := b
      q_surjective := quotient_locallySurjective g φ Q
      pushout := hquotient }
  obtain ⟨νY, hνY⟩ := ordinary_quotient_iso φ pY Q n
  obtain ⟨νX, hνX⟩ := ordinary_quotient_iso (g.rings.map φ ≫ a) pX QX n
  let s : ordinarySource g φ ⋙ (pX (quotient g φ Q n)).ordinary ≅
      (g.inverse B).modules ⋙ (pX (g.rings.map (Q.extensionProjection n))).ordinary :=
    Functor.isoWhiskerLeft (restriction φ) (e.ordinary (Q.projection n)).symm ≪≫
      Functor.isoWhiskerRight νY (g.inverse (Q.S.obj (op n))).modules ≪≫
        e.ordinary (Q.extensionProjection n)
  let t : ordinaryTarget g (pX := pX) φ a ⋙ (pX (quotient g φ Q n)).ordinary ≅
      (g.inverse B).modules ⋙ (pX (g.rings.map (Q.extensionProjection n))).ordinary :=
    Functor.isoWhiskerLeft (ordinaryPullback g (pX := pX) a) νX ≪≫
      Functor.isoWhiskerLeft (g.inverse B).modules (nX.ordinary a (b.app (op n))) ≪≫
        Functor.isoWhiskerLeft (g.inverse B).modules
          (eqToIso (congrArg (fun q ↦ (pX q).ordinary) (hcompatible n)))
  have he : Functor.whiskerRight δ (pX (quotient g φ Q n)).ordinary ≫ t.hom = s.hom := by
    apply NatTrans.ext
    funext M
    apply ((nX.ordinaryAdjunction (quotient g φ Q n)).homEquiv _ _).injective
    apply (underlying (g.rings.obj R)).map_injective
    have hy : insertion nY (Q.projection n) ((restriction φ).obj M) ≫
        (underlying (Q.S.obj (op n))).map (νY.hom.app M) =
      insertion nY (Q.extensionProjection n) M := by
      ext U x
      change (νY.hom.app M).val.app U
        (((nY.ordinaryAdjunction (Q.projection n)).unit.app _).val.app U x) = _
      rw [nY.ordinary_unit, hνY]
      exact (nY.ordinary_unit (Q.extensionProjection n) M U x).symm
    have hx : insertion nX (quotient g φ Q n)
        ((ordinaryTarget g (pX := pX) φ a).obj M) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          (νX.hom.app ((ordinaryPullback g (pX := pX) a).obj M)) =
      insertion nX (b.app (op n)) ((ordinaryPullback g (pX := pX) a).obj M) := by
      ext U x
      change (νX.hom.app _).val.app U
        (((nX.ordinaryAdjunction (quotient g φ Q n)).unit.app _).val.app U x) = _
      rw [nX.ordinary_unit]
      erw [hνX]
      exact (nX.ordinary_unit (b.app (op n)) _ U x).symm
    have hs : insertion nX (quotient g φ Q n) ((ordinarySource g φ).obj M) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map (s.hom.app M) =
      (g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        (g.inverse B).moduleUnderlying.inv.app M ≫
          insertion nX (g.rings.map (Q.extensionProjection n)) ((g.inverse B).modules.obj M) := by
      change insertion nX (quotient g φ Q n) ((ordinarySource g φ).obj M) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          ((e.ordinary (Q.projection n)).inv.app ((restriction φ).obj M)) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          ((g.inverse (Q.S.obj (op n))).modules.map (νY.hom.app M)) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          ((e.ordinary (Q.extensionProjection n)).hom.app M) = _
      erw [reassoc_of% insertion_inverse_comparison g nY nX e
        (Q.projection n) ((restriction φ).obj M)]
      have hn := (g.inverse (Q.S.obj (op n))).moduleUnderlying.inv.naturality (νY.hom.app M)
      dsimp only [Functor.comp_map] at hn
      erw [← reassoc_of% hn]
      have hy' := congrArg uInv.map hy
      simp only [Functor.map_comp] at hy'
      erw [reassoc_of% hy']
      exact congrArg (fun f ↦ (g.inverse R).moduleUnderlying.hom.app
        ((restriction φ).obj M) ≫ f) (e.ordinary_insertion (Q.extensionProjection n) M)
    have ht : insertion nX (quotient g φ Q n)
        ((ordinaryTarget g (pX := pX) φ a).obj M) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map (t.hom.app M) =
      insertion nX (b.app (op n)) ((ordinaryPullback g (pX := pX) a).obj M) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          ((nX.ordinary a (b.app (op n))).hom.app ((g.inverse B).modules.obj M)) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          ((eqToIso (congrArg (fun q ↦ (pX q).ordinary) (hcompatible n))).hom.app
            ((g.inverse B).modules.obj M)) := by
      dsimp only [t, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
        Functor.whiskerLeft_app]
      rw [Functor.map_comp, Functor.map_comp, ← Category.assoc]
      erw [hx]
    have hd : (underlying (g.rings.obj R)).map (δ.app M) =
        (g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
          (g.inverse B).moduleUnderlying.inv.app M ≫
            insertion nX a ((g.inverse B).modules.obj M) := by
      ext U x
      exact (hδ M U x).trans
        (nX.ordinary_unit a ((g.inverse B).modules.obj M) U _).symm
    change insertion nX (quotient g φ Q n) ((ordinarySource g φ).obj M) ≫
      (underlying (g.rings.obj (Q.S.obj (op n)))).map
        ((pX (quotient g φ Q n)).ordinary.map (δ.app M) ≫ t.hom.app M) =
      insertion nX (quotient g φ Q n) ((ordinarySource g φ).obj M) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map (s.hom.app M)
    have hn := congrArg ((underlying (g.rings.obj R)).map)
      ((nX.ordinaryAdjunction (quotient g φ Q n)).unit.naturality (δ.app M)).symm
    simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hn
    change insertion nX (quotient g φ Q n) ((ordinarySource g φ).obj M) ≫
      (underlying (g.rings.obj (Q.S.obj (op n)))).map
        ((pX (quotient g φ Q n)).ordinary.map (δ.app M)) =
      (underlying (g.rings.obj R)).map (δ.app M) ≫
        insertion nX (quotient g φ Q n) ((ordinaryTarget g (pX := pX) φ a).obj M) at hn
    rw [Functor.map_comp, ← Category.assoc]
    refine (congrArg (fun f ↦ f ≫
      (underlying (g.rings.obj (Q.S.obj (op n)))).map (t.hom.app M)) hn).trans ?_
    rw [Category.assoc]
    refine (congrArg (fun f ↦ (underlying (g.rings.obj R)).map (δ.app M) ≫ f) ht).trans ?_
    have hc := congrArg (fun f ↦ f ≫
      (underlying (g.rings.obj (Q.S.obj (op n)))).map
        ((eqToIso (congrArg (fun q ↦ (pX q).ordinary) (hcompatible n))).hom.app
          ((g.inverse B).modules.obj M)))
      (insertion_comp pX nX a (b.app (op n)) ((g.inverse B).modules.obj M))
    have hc' := hc.trans (insertion_congr pX nX _ _ (hcompatible n)
      ((g.inverse B).modules.obj M))
    have hc'' := congrArg (fun f ↦
      (g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        (g.inverse B).moduleUnderlying.inv.app M ≫ f) hc'
    have hd' := congrArg (fun f ↦ f ≫
      (insertion nX (b.app (op n)) ((ordinaryPullback g (pX := pX) a).obj M) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          ((nX.ordinary a (b.app (op n))).hom.app ((g.inverse B).modules.obj M)) ≫
        (underlying (g.rings.obj (Q.S.obj (op n)))).map
          ((eqToIso (congrArg (fun q ↦ (pX q).ordinary) (hcompatible n))).hom.app
            ((g.inverse B).modules.obj M)))) hd
    refine hd'.trans ?_
    have hfinal := hc''.trans hs.symm
    simp only [Category.assoc] at hfinal ⊢
    convert hfinal using 1 <;> rfl
  have : IsIso (Functor.whiskerRight δ (pX (quotient g φ Q n)).ordinary ≫ t.hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (Functor.whiskerRight δ (pX (quotient g φ Q n)).ordinary) t.hom

end SheafOfModules.CommonQuotientPullback
