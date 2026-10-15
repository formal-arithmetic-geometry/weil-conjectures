/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle

/-! # The five-arrow cube for fixed derived-pullback comparisons -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem iso_cube_cancel {C : Type*} [Category C]
    {R S T U V W : C}
    (a : W ≅ U) (b : V ≅ U) (c : S ≅ V) (d : S ≅ T)
    (e : T ≅ U) (f : R ≅ T) (g : R ≅ W)
    (h1 : d ≪≫ e = c ≪≫ b) (h2 : f ≪≫ e = g ≪≫ a) :
    a ≪≫ b.symm ≪≫ c.symm ≪≫ d ≪≫ f.symm = g.symm := by
  apply Iso.ext
  apply (cancel_mono ((f ≪≫ e).hom)).1
  have h1' := congrArg Iso.hom h1
  have h2' := congrArg Iso.hom h2
  simp only [Iso.trans_hom] at h1' h2'
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp]
  rw [h1', h2']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp]
  rw [b.inv_hom_id, Category.comp_id]

/-- The two composites around a cube of scheme maps agree under the fixed
derived-pullback composition family. Source: Stacks Project, Tag 0D5S.

Proof: Apply `compositionTo_triangle` first to the top three arrows, then to
the two lower three-arrow paths. Both sides become the comparison for the
same full composite, conjugated by the comparison for the front square.
Cancel each isomorphism against its inverse. -/
theorem perfectOverlapCompositionCube
    {Q W U K X P : Scheme.{u}}
    (r : Q ⟶ W) (iK : W ⟶ U) (u : U ⟶ K) (w : W ⟶ K)
    (q : Q ⟶ X) (gk : X ⟶ K)
    (iX : Q ⟶ P) (p : P ⟶ X) (j : P ⟶ U)
    (hi : iK ≫ u = w) (hr : r ≫ w = q ≫ gk)
    (hq : iX ≫ p = q) (hj : j ≫ u = p ≫ gk)
    (hs : r ≫ iK = iX ≫ j)
    (F : schemeDerivedCategory K) :
    (derivedPullback r).mapIso ((compositionTo iK u w hi).app F) ≪≫
        (compositionTo r w (q ≫ gk) hr).app F ≪≫
          ((compositionTo q gk (q ≫ gk) rfl).app F).symm ≪≫
            ((compositionTo iX p q hq).app ((derivedPullback gk).obj F)).symm ≪≫
              (derivedPullback iX).mapIso
                (((compositionTo p gk (p ≫ gk) rfl).app F) ≪≫
                  ((compositionTo j u (p ≫ gk) hj).app F).symm) =
      (compositionTo r iK (iX ≫ j) hs).app ((derivedPullback u).obj F) ≪≫
        ((compositionTo iX j (iX ≫ j) rfl).app
          ((derivedPullback u).obj F)).symm := by
  have htop := compositionTo_triangle r iK u w (q ≫ gk) (iX ≫ j)
    hi hr hs F
  have hleft := compositionTo_triangle iX p gk (p ≫ gk) (q ≫ gk) q
    rfl (by rw [← hq, Category.assoc]) hq F
  have hright := compositionTo_triangle iX j u (p ≫ gk) (q ≫ gk)
    (iX ≫ j) hj (by rw [← hq, Category.assoc]) rfl F
  calc
    _ = (compositionTo r iK (iX ≫ j) hs).app ((derivedPullback u).obj F) ≪≫
          (compositionTo (iX ≫ j) u (q ≫ gk)
            (by rw [← hs, Category.assoc, hi, hr])).app F ≪≫
          ((compositionTo q gk (q ≫ gk) rfl).app F).symm ≪≫
            ((compositionTo iX p q hq).app ((derivedPullback gk).obj F)).symm ≪≫
              (derivedPullback iX).mapIso
                (((compositionTo p gk (p ≫ gk) rfl).app F) ≪≫
                  ((compositionTo j u (p ≫ gk) hj).app F).symm) := by
      simpa only [Iso.trans_assoc] using
        congrArg (fun z => z ≪≫
          ((compositionTo q gk (q ≫ gk) rfl).app F).symm ≪≫
            ((compositionTo iX p q hq).app ((derivedPullback gk).obj F)).symm ≪≫
              (derivedPullback iX).mapIso
                (((compositionTo p gk (p ≫ gk) rfl).app F) ≪≫
                  ((compositionTo j u (p ≫ gk) hj).app F).symm)) htop
    _ = _ := by
      simpa only [Functor.mapIso_trans, Functor.mapIso_symm,
        Iso.trans_assoc] using congrArg
        (fun z => (compositionTo r iK (iX ≫ j) hs).app
          ((derivedPullback u).obj F) ≪≫ z)
        (iso_cube_cancel
          ((compositionTo (iX ≫ j) u (q ≫ gk)
            (by rw [← hs, Category.assoc, hi, hr])).app F)
          ((compositionTo q gk (q ≫ gk) rfl).app F)
          ((compositionTo iX p q hq).app ((derivedPullback gk).obj F))
          ((derivedPullback iX).mapIso
            ((compositionTo p gk (p ≫ gk) rfl).app F))
          ((compositionTo iX (p ≫ gk) (q ≫ gk)
            (by rw [← hq, Category.assoc])).app F)
          ((derivedPullback iX).mapIso
            ((compositionTo j u (p ≫ gk) hj).app F))
          ((compositionTo iX j (iX ≫ j) rfl).app ((derivedPullback u).obj F))
          hleft hright)

end AlgebraicGeometry
