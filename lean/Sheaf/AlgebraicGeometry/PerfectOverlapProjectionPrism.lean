/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrism

/-! # The fixed pullback-composition prism over an overlap -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The first-open cartesian comparison is the fixed three-arrow pullback
composition prism. Source: Stacks Project, Tag 0D5S.

Proof: The overlap restriction square identifies the two maps to the first
open. Apply the general `perfectOverlapTransport_prism` to this equality and
the cartesian equation for the base-change map. -/
theorem perfectOverlapProjectionPrismU
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S) (l : Over.mk b ⟶ Over.mk q)
    (hgf : gk ≫ f = g) (hg : IsPullback g pX pY b)
    (hf : IsPullback f pK pY q) (U V : Y.Opens)
    (hR : g ⁻¹ᵁ (U ⊓ V) ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ (U ⊓ V)))
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫
          gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V)) hR =
        baseChangeMap ((U ⊓ V).ι ≫ pY) l ≫
          ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv)
    (A : schemeDerivedCategory U.toScheme) :
    let r := gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V)) hR
    let m := baseChangeMap ((U ⊓ V).ι ≫ pY) l
    let eY := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
    let eK := ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback
    let hKU : f ⁻¹ᵁ (U ⊓ V) ≤ f ⁻¹ᵁ U := fun _ hx ↦ hx.1
    let hXU : g ⁻¹ᵁ (U ⊓ V) ≤ g ⁻¹ᵁ U := fun _ hx ↦ hx.1
    let p := K.homOfLE
      hKU ≫ (f ∣_ U)
    let t := X.homOfLE hXU ≫ (g ∣_ U)
    let hr : r ≫ p = t := by
      apply (cancel_mono U.ι).1
      dsimp only [r, p, t]
      simp only [← Category.assoc]
      rw [Scheme.Hom.resLE_map]
      simp only [Category.assoc, morphismRestrict_ι]
      simp only [← Category.assoc]
      rw [Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι,
        Category.assoc, hgf]
    (derivedPullback eY.inv).mapIso ((compositionTo r p t hr).app A) ≪≫
        (compositionTo eY.inv t (eY.inv ≫ t) rfl).app A =
      (perfectOverlapDerivedPullbackTransport r eY eK m hmap).app
          ((derivedPullback p).obj A) ≪≫
        ((derivedPullback m).mapIso
            ((compositionTo eK.inv p (eK.inv ≫ p) rfl).app A) ≪≫
          (compositionTo m (eK.inv ≫ p) (eY.inv ≫ t)
            (by rw [← hr, ← Category.assoc, ← hmap, Category.assoc])).app A) := by
  intro r m eY eK hKU hXU p t hr
  exact perfectOverlapTransport_prism r eY eK m hmap p t hr A

/-- The second-open cartesian comparison is the same fixed prism, using the
right projection of the overlap. Source: Stacks Project, Tag 0D5S. -/
theorem perfectOverlapProjectionPrismV
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S) (l : Over.mk b ⟶ Over.mk q)
    (hgf : gk ≫ f = g) (hg : IsPullback g pX pY b)
    (hf : IsPullback f pK pY q) (U V : Y.Opens)
    (hR : g ⁻¹ᵁ (U ⊓ V) ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ (U ⊓ V)))
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫
          gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V)) hR =
        baseChangeMap ((U ⊓ V).ι ≫ pY) l ≫
          ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv)
    (B : schemeDerivedCategory V.toScheme) :
    let r := gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V)) hR
    let m := baseChangeMap ((U ⊓ V).ι ≫ pY) l
    let eY := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
    let eK := ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback
    let hKV : f ⁻¹ᵁ (U ⊓ V) ≤ f ⁻¹ᵁ V := fun _ hx ↦ hx.2
    let hXV : g ⁻¹ᵁ (U ⊓ V) ≤ g ⁻¹ᵁ V := fun _ hx ↦ hx.2
    let p := K.homOfLE hKV ≫ (f ∣_ V)
    let t := X.homOfLE hXV ≫ (g ∣_ V)
    let hr : r ≫ p = t := by
      apply (cancel_mono V.ι).1
      dsimp only [r, p, t]
      simp only [← Category.assoc]
      rw [Scheme.Hom.resLE_map]
      simp only [Category.assoc, morphismRestrict_ι]
      simp only [← Category.assoc]
      rw [Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι,
        Category.assoc, hgf]
    (derivedPullback eY.inv).mapIso ((compositionTo r p t hr).app B) ≪≫
        (compositionTo eY.inv t (eY.inv ≫ t) rfl).app B =
      (perfectOverlapDerivedPullbackTransport r eY eK m hmap).app
          ((derivedPullback p).obj B) ≪≫
        ((derivedPullback m).mapIso
            ((compositionTo eK.inv p (eK.inv ≫ p) rfl).app B) ≪≫
          (compositionTo m (eK.inv ≫ p) (eY.inv ≫ t)
            (by rw [← hr, ← Category.assoc, ← hmap, Category.assoc])).app B) := by
  intro r m eY eK hKV hXV p t hr
  exact perfectOverlapTransport_prism r eY eK m hmap p t hr B

end AlgebraicGeometry
