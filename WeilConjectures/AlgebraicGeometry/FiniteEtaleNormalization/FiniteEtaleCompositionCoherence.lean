/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingCocycleSourceEtale

/-! # Equality transport for the finite exceptional compositor

Source: regular-immersion proof Step 4(i), comparing equal composite scheme maps.
(blueprint: lem-pur-finite-exceptional-equality-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y Z T : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
  [QuasiCompact (T ↘ Spec (.of P.field.k))]

/-- Equality transport agrees with the canonical exceptional congruence.
Proof: eliminate the equality; conjugation sends the identity to the identity.
Source: regular-immersion proof Step 4(i), equality of Cartesian composites
(blueprint: lem-pur-finite-exceptional-equality-coherence). -/
private theorem congr_eqToIso (f g : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (h : f = g) :
    congr P f g h = eqToIso (by cases h; rfl) := by
  cases h
  apply Iso.ext
  simp only [congr, Etale.unboundedEtaleLowerShriekCongr,
    conjugateIsoEquiv_apply_hom, Iso.refl_hom, conjugateEquiv_id, eqToIso_refl]

/-- Exceptional composition is natural in equality of its first scheme map.
Proof: eliminate the equality and use the preceding identity computation.
Source: regular-immersion proof Step 4(i), transporting the first composite factor
(blueprint: lem-pur-finite-exceptional-equality-coherence). -/
private theorem comp_congr_left (f f' : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : f = f') (K : Etale.DerivedCategoryModule P.Coefficient Z) :
    (congr P (f ≫ g) (f' ≫ g) (congrArg (fun q ↦ q ≫ g) e)).hom.app K ≫
        (comp P f' g).hom.app K =
      (comp P f g).hom.app K ≫
        (congr P f f' e).hom.app ((exceptional P g).obj K) := by
  cases e
  simp [congr_eqToIso]

/-- Exceptional composition is natural in equality of its second scheme map.
Proof: eliminate the equality and use the identity computation.
Source: regular-immersion proof Step 4(i), transporting the second composite factor
(blueprint: lem-pur-finite-exceptional-equality-coherence). -/
private theorem comp_congr_right (f : X ⟶ Y) (g g' : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [g'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (e : g = g') (K : Etale.DerivedCategoryModule P.Coefficient Z) :
    (congr P (f ≫ g) (f ≫ g') (congrArg (fun q ↦ f ≫ q) e)).hom.app K ≫
        (comp P f g').hom.app K =
      (comp P f g).hom.app K ≫ (exceptional P f).map
        ((congr P g g' e).hom.app K) := by
  cases e
  simp [congr_eqToIso]

/-- The finite exceptional compositor has the normalized associativity law.
Proof: specialize the adjunction-conjugated compact-support associativity theorem.
Source: regular-immersion proof Step 4(i), associativity of exceptional composition
(blueprint: lem-pur-finite-exceptional-equality-coherence). -/
theorem comp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K : Etale.DerivedCategoryModule P.Coefficient T) :
    (comp P (f ≫ g) h).hom.app K ≫
        (comp P f g).hom.app ((exceptional P h).obj K) =
      (congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).hom.app K ≫
        (comp P f (g ≫ h)).hom.app K ≫
        (exceptional P f).map ((comp P g h).hom.app K) := by
  exact AlgebraicGeometry.ProEtale.DualizingLocality.comp_assoc P f g h K

/-- Inverse form of compositor associativity, with the equality transport retained.
Proof: cancel the two isomorphisms in the positive associativity equation.
Source: regular-immersion proof Step 4(i), pasting the comparison words
(blueprint: lem-pur-finite-exceptional-equality-coherence). -/
private theorem comp_assoc_rotate (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K : Etale.DerivedCategoryModule P.Coefficient T) :
    (comp P f g).inv.app ((exceptional P h).obj K) ≫
        (comp P (f ≫ g) h).inv.app K ≫
        (congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).hom.app K =
      (exceptional P f).map ((comp P g h).inv.app K) ≫
        (comp P f (g ≫ h)).inv.app K := by
  have h := congrArg (fun q ↦
    (comp P f g).inv.app ((exceptional P h).obj K) ≫
      (comp P (f ≫ g) h).inv.app K ≫ q ≫
      (exceptional P f).map ((comp P g h).inv.app K) ≫
      (comp P f (g ≫ h)).inv.app K) (comp_assoc P f g h K)
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at h
  simpa only [(exceptional P f).map_id, Category.id_comp, Iso.hom_inv_id_app,
    Category.comp_id] using h.symm

/-- Move the second compositor to the other side of the associativity equation.
Proof: precompose with the inverse outer compositor and postcompose with the
functorial image of the inverse inner compositor, then cancel adjacent inverses.
Source: regular-immersion proof Step 4(i), pasting comparison words
(blueprint: lem-pur-finite-exceptional-equality-coherence). -/
private theorem comp_assoc_middle (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K : Etale.DerivedCategoryModule P.Coefficient T) :
    (comp P f g).hom.app ((exceptional P h).obj K) ≫
        (exceptional P f).map ((comp P g h).inv.app K) =
      (comp P (f ≫ g) h).inv.app K ≫
        (congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)).hom.app K ≫
        (comp P f (g ≫ h)).hom.app K := by
  have hc := congrArg (fun q ↦ (comp P (f ≫ g) h).inv.app K ≫ q ≫
    (exceptional P f).map ((comp P g h).inv.app K)) (comp_assoc P f g h K)
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app] at hc
  simp only [(exceptional P f).map_id] at hc
  erw [Category.comp_id] at hc
  exact hc

/-- Equality naturality with the outer compositor inverted.
Proof: precompose and postcompose the positive naturality equation with its
outer compositor inverses and cancel them.
Source: regular-immersion proof Step 4(i), equality of Cartesian composites
(blueprint: lem-pur-finite-exceptional-equality-coherence). -/
private theorem comp_congr_left_inv (f f' : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : f = f') (K : Etale.DerivedCategoryModule P.Coefficient Z) :
    (congr P f f' e).hom.app ((exceptional P g).obj K) ≫
        (comp P f' g).inv.app K =
      (comp P f g).inv.app K ≫
        (congr P (f ≫ g) (f' ≫ g) (congrArg (fun q ↦ q ≫ g) e)).hom.app K := by
  have hc := congrArg (fun q ↦ (comp P f g).inv.app K ≫ q ≫
    (comp P f' g).inv.app K) (comp_congr_left P f f' g e K)
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id] using hc.symm

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
