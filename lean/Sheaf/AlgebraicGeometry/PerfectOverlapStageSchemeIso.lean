/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import Mathlib.AlgebraicGeometry.Restrict

/-! # The overlap stage cartesian scheme isomorphism -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem eqToHom_comp_homOfLE (X : Scheme.{u})
    {A B : X.Opens} (e : A = B) (h : B ≤ A) :
    eqToHom (congrArg (fun W : X.Opens ↦ W.toScheme) e) ≫ X.homOfLE h = 𝟙 _ := by
  cases e
  simpa only [eqToHom_refl, Category.id_comp] using Scheme.homOfLE_rfl X A

/-- The cartesian overlap isomorphism with source exactly the intersection of
the two inverse-image opens. The explicit transport uses
`Scheme.Hom.preimage_inf`, so clients do not unfold an equality of dependent
open-scheme objects. Source: Stacks Project, Tag 08DW. -/
@[no_expose] noncomputable def perfectOverlapStageSchemeIso
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V : Y.Opens) :
    (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ≅
      pullback ((U ⊓ V).ι ≫ pY) q :=
  (eqToIso (congrArg (fun W : X.Opens ↦ W.toScheme)
    (Scheme.Hom.preimage_inf g)).symm) ≪≫
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback

/-- The explicit open transport is judgmentally the raw cartesian iso after
the preimage-intersection equality is applied. -/
theorem perfectOverlapStageSchemeIso_eq_raw
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V : Y.Opens) :
    perfectOverlapStageSchemeIso g pX pY q h U V =
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback := by
  unfold perfectOverlapStageSchemeIso
  simp only [Scheme.Hom.preimage_inf, eqToIso_refl,
    Iso.refl_trans]

/-- The transported cartesian scheme isomorphism has the expected first
projection after restriction to either larger open. -/
theorem perfectOverlapStageSchemeIso_inv_projection
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L :=
      fun x hx ↦ by
        have hh : x ∈ g ⁻¹ᵁ (U ⊓ V) := by
          rw [Scheme.Hom.preimage_inf]
          exact hx
        exact hWL hh
    (perfectOverlapStageSchemeIso g pX pY q h U V).inv ≫
        (X.homOfLE hW' ≫ (g ∣_ L)) =
      pullback.fst ((U ⊓ V).ι ≫ pY) q ≫ Y.homOfLE hWL := by
  intro hW'
  let hInf : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ (U ⊓ V) := by
    rw [Scheme.Hom.preimage_inf]
  have hres : X.homOfLE hW' ≫ (g ∣_ L) =
      (X.homOfLE hInf ≫ (g ∣_ (U ⊓ V))) ≫ Y.homOfLE hWL := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [← Category.assoc (X.homOfLE hW') (g ⁻¹ᵁ L).ι g,
      Scheme.homOfLE_ι]
    rw [← Category.assoc (X.homOfLE hInf)
      (g ⁻¹ᵁ (U ⊓ V)).ι g, Scheme.homOfLE_ι]
  have he : (perfectOverlapStageSchemeIso g pX pY q h U V).inv ≫
      X.homOfLE hInf =
        ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback.inv := by
    unfold perfectOverlapStageSchemeIso
    simp only [Iso.trans_inv, eqToIso.inv, Category.assoc]
    rw [eqToHom_comp_homOfLE X (Scheme.Hom.preimage_inf g) hInf]
    simp only [Category.comp_id]
  rw [hres]
  simp only [Category.assoc]
  rw [← Category.assoc (perfectOverlapStageSchemeIso g pX pY q h U V).inv
    (X.homOfLE hInf), he]
  rw [← Category.assoc
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback.inv
    (g ∣_ (U ⊓ V)),
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback_inv_fst]

end AlgebraicGeometry
