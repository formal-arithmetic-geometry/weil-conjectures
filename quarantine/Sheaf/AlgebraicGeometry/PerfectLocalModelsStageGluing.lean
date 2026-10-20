/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons
import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Geometric stage model from prescribed local pullback models

Source: Stacks Project, Tag 09RF, the construction of a, b and c before Tag 08DG.
(blueprint: lem-pc-perfect-local-models-stage-gluing).
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem isIso_schemeRestriction_of_isIso_localized
    (X : Scheme.{u}) (W : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    {L E : schemeDerivedCategory X} (a : L ⟶ E)
    (ha : IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) W).mapDerivedCategory.map a)) :
    IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map a) := by
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
  let e := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
    (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv W)
  have : e.Additive := Functor.additive_of_preserves_binary_products e
  have : IsIso (r.mapDerivedCategory.map a) := ha
  let q : (r ⋙ e).mapDerivedCategory ≅ r.mapDerivedCategory ⋙ e.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso r e
  change IsIso ((r ⋙ e).mapDerivedCategory.map a)
  apply (NatIso.isIso_map_iff q (X := L) (Y := E) a).2
  change IsIso (e.mapDerivedCategory.map (r.mapDerivedCategory.map a))
  infer_instance


private theorem model_witnesses_of_local_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (X Y : Scheme.{u}) (g : X ⟶ Y)
    (F : schemeDerivedCategory Y) (E : schemeDerivedCategory X)
    (U V : Y.Opens) (hUV : U ⊔ V = ⊤)
    (hU : U.toScheme.IsPerfect ((derivedPullback U.ι).obj F))
    (hV : V.toScheme.IsPerfect ((derivedPullback V.ι).obj F))
    (P Q : X.Opens) (hPQ : P ⊔ Q = ⊤)
    (pU : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P).mapDerivedCategory.obj
         ((derivedPullback g).obj F) ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P).mapDerivedCategory.obj
         E)
    (pV : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q).mapDerivedCategory.obj
         ((derivedPullback g).obj F) ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q).mapDerivedCategory.obj
         E)
    (hp : derivedOpenHomRestriction X.toRingedSpace
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))
        (E := (derivedPullback g).obj F) (F := E) pU.hom =
      derivedOpenHomRestriction X.toRingedSpace
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))
        (E := (derivedPullback g).obj F) (F := E) pV.hom) :
    ∃ a : (derivedPullback g).obj F ⟶ E,
      (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
        W.toScheme.IsPerfect ((derivedPullback W.ι).obj F)) ∧
      (∀ x : X, ∃ W : X.Opens, x ∈ W ∧
        IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map a)) := by
  obtain ⟨_, _, hex⟩ := derived_hom_mayer_vietoris.{u, w}
    X.toRingedSpace P Q hPQ ((derivedPullback g).obj F) E
  obtain ⟨a, ha⟩ := (hex (pU.hom, pV.hom)).mp (sub_eq_zero.mpr hp)
  have haP := congrArg Prod.fst ha
  have haQ := congrArg Prod.snd ha
  dsimp only at haP haQ
  refine ⟨a, ?_, ?_⟩
  · intro y
    have hy : y ∈ U ∨ y ∈ V := by
      change y ∈ U ⊔ V
      rw [hUV]
      trivial
    rcases hy with hy | hy
    · exact ⟨U, hy, hU⟩
    · exact ⟨V, hy, hV⟩
  · intro x
    have hx : x ∈ P ∨ x ∈ Q := by
      change x ∈ P ⊔ Q
      rw [hPQ]
      trivial
    rcases hx with hx | hx
    · refine ⟨P, hx, ?_⟩
      have hloc : IsIso ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) P).mapDerivedCategory.map a) := by
        rw [haP]
        exact pU.isIso_hom
      exact isIso_schemeRestriction_of_isIso_localized.{u, w} X P
        (L := (derivedPullback g).obj F) (E := E) a hloc
    · refine ⟨Q, hx, ?_⟩
      have hloc : IsIso ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) Q).mapDerivedCategory.map a) := by
        rw [haQ]
        exact pV.isIso_hom
      exact isIso_schemeRestriction_of_isIso_localized.{u, w} X Q
        (L := (derivedPullback g).obj F) (E := E) a hloc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Specializing the derived restriction and exactness functors needs this elaboration budget.
set_option synthInstance.maxHeartbeats 400000 in
-- Derived restriction functors require synthesis through the exact open-site equivalences.
/-- The geometric descent-and-gluing part of eventual local compatibility.
Source: Stacks Project, Tag 09RE and Tag 09RF, two-open induction using Tag 08DG.
(blueprint: lem-pc-perfect-local-models-stage-gluing).

Proof: Pass to the directed tail above j. On the overlap U intersection V,
restrict A and B. They are perfect by Tag 09UA. The overlap is compact since
Y_j is quasi-separated and U,V are compact, and its map to Spec R_j is finitely
presented. Restrict the given isomorphisms to the inverse-image overlap and
compose one with the inverse of the other, using the coherent pullback/restriction
comparisons. Apply Tag 09RE there to descend this isomorphism and its inverse,
and stabilize the inverse equations at a common later stage k. The resulting
stage isomorphism has exactly this prescribed limit pullback, not merely an
unspecified isomorphism between the objects. Pull A and B to the inverse-image
cover on Y_k. Tag 08DG glues these objects along that descended isomorphism to
an object F, with local identifications realizing its transition. The local restrictions
of F are perfect because pullback preserves perfectness; the covering opens
therefore give the displayed neighbourhood witnesses, without asserting global
perfectness.
The local identifications of Lg_k*F with E induced by the original comparisons
agree on the overlap by the prescribed-pullback equation. The derived Hom
Mayer-Vietoris surjectivity glues their morphisms to a global map Lg_k*F to E.
Its two restrictions are the given isomorphisms. The inverse-image cover
therefore gives the displayed local invertibility witnesses. Global detection of
perfectness and invertibility are left to the caller. No adjunction or
maps to Rg_k*E occur in this argument. Empty schemes, empty overlaps, equal
opens and non-strict preorders work by the same restrictions and directed tail.
The auxiliary object F is an existential theorem witness, never a definition
chosen from an unproved mere existence statement. -/
theorem perfect_local_models_stage_gluing
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (_hcover : U ⊔ V = ⊤)
      (_hU : IsCompact (U : Set Yj)) (_hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (_hA : U.toScheme.IsPerfect A) (_hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X)
      (_φU : (derivedPullback (gj ∣_ U)).obj A ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory.obj E)
      (_φV : (derivedPullback (gj ∣_ V)).obj B ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      ∃ (F : schemeDerivedCategory
          (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))))
        (a : (derivedPullback g).obj F ⟶ E),
        (∀ x : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk)))) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))).Opens,
            x ∈ W ∧ W.toScheme.IsPerfect ((derivedPullback W.ι).obj F)) ∧
        (∀ x : (pullback t (Spec.map (c.ι.app i)) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (c.ι.app i))).Opens, x ∈ W ∧
            IsIso ((schemeOpenRestriction _ W).mapDerivedCategory.map a)) := by
  rename_i hD hDO
  intro Yj X gj U V hcover hU hV A B hA hB E φU φV
  obtain ⟨k, hjk, F, U', V', hcover', hU', hV', pU, pV, hp⟩ :=
    @perfect_local_models_stage_comparisons.{u, w} I _ _ R c hc i Z t _ _ _
      hD hDO
      j hij U V hcover hU hV A B hA hB E φU φV
  let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
  let g : X ⟶ Yk := baseChangeMap t
    (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (T' := Over.mk (Spec.map (c.ι.app i)))
    (Over.homMk (Spec.map (c.ι.app k))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
  let P := gj ⁻¹ᵁ U
  let Q := gj ⁻¹ᵁ V
  have hPQ : P ⊔ Q = ⊤ := by
    change gj ⁻¹ᵁ U ⊔ gj ⁻¹ᵁ V = ⊤
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  refine ⟨k, hjk, F, ?_⟩
  exact @model_witnesses_of_local_comparisons.{u, w} hD hDO
    X Yk g F E U' V' hcover' hU' hV' P Q hPQ pU pV hp

end AlgebraicGeometry
