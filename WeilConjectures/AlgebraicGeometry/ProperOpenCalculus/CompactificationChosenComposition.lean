/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence

/-! # Composition for arbitrary chosen compactifications

Source: Stacks 0F7J--0F7K, independence of a common refining tower.
(blueprint: lem-sp-chosen-compactification-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProperOpenCalculus

variable {A : Scheme.{u} → Prop} (F : ProperOpenCalculus.{u, v, w} A) (G : Geometry A)

/-- The comparison is independent of the chosen common refinement by cofilteredness.
Source: Stacks 0F7J (blueprint: lem-sp-chosen-compactification-composition). -/
def comparison (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (hc : A c.Z) (hd : A d.Z) :
    F.H X Y c hc ≅ F.H X Y d hd := by
  classical
  let e := (G.common X Y f d c hd hc).choose
  let he := (G.common X Y f d c hd hc).choose_spec.1
  let r := (G.common X Y f d c hd hc).choose_spec.2.1.some
  let s := (G.common X Y f d c hd hc).choose_spec.2.2.some
  exact F.compare X Y hd hc he r s

/-- Computing the comparison on any supplied common refinement gives the same map.
Source: Stacks 0F7J (blueprint: lem-sp-chosen-compactification-composition). -/
theorem comparison_eq (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f) (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
    (r : e.Refinement d) (s : e.Refinement c) :
    comparison F G X Y f c d hc hd = F.compare X Y hd hc he r s := by
  exact (compactification_refinement_coherence F G).2.2.1 X Y f d c _ e hd hc _ he
    _ _ r s

@[simp] theorem comparison_refl (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z) :
    comparison F G X Y f c c hc hc = Iso.refl _ := by
  rw [comparison_eq F G X Y f c c c hc hc hc
    (Compactification.Refinement.id c) (Compactification.Refinement.id c)]
  exact Iso.self_symm_id _

@[simp] theorem comparison_trans (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f) (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    comparison F G X Y f c d hc hd ≪≫ comparison F G X Y f d e hd he =
      comparison F G X Y f c e hc he := by
  unfold comparison
  exact (compactification_refinement_coherence F G).2.2.2.1 X Y f e d c
    _ _ _ he hd hc _ _ _ _ _ _ _ _ _

section AssociativityTransfer
variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]

end AssociativityTransfer

end AlgebraicGeometry.ProperOpenCalculus
