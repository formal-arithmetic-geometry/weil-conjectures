/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Compatible affine self-Tor comparison maps

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-n1-self-tor-compatible-affine-maps). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- An affine coordinate square for a local comparison, before duality.
The coordinate maps themselves need not be invertible comparisons; only the changes
of coordinates are isomorphisms. No regularity hypothesis is imposed.
Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-n1-self-tor-compatible-affine-maps). -/
def IsAffineSelfTorChartMap {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) (n : ℕ) (E Q : Z.Modules)
    (φ : E.over (i ⁻¹ᵁ U.1) ⟶ Q.over (i ⁻¹ᵁ U.1)) : Prop :=
  let T := tilde.functor Γ(Y, U.1) ⋙
    Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
    Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
  let c := selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
  ∃ (s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj _).over (i ⁻¹ᵁ U.1))
    (t : (T.obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1)),
    φ = s.hom ≫ (T.map c).over (i ⁻¹ᵁ U.1) ≫ t.hom

/-- Affine normalized comparisons exist locally and agree on overlaps.

Source: Stacks Project, Tag 09PQ (resolution-independent Tor products),
Tag 01R3 (conormal classes), and Tag 06YH (K-flat derived tensor).
(blueprint: new-n1-self-tor-compatible-affine-maps).

Proof: For each affine U=Spec A, sheafify a projective resolution of A/I.
The affine quotient resolution comparison identifies its augmentation with
(i_*O_Z)|_U. Its tensor with A/I computes the restriction of the fixed derived
self tensor, by K-flat resolution comparison; the quotient scalar action identifies
its pullback with the same Tor sheaf on i^{-1}U. Identify the pulled-back kernel
with I/I² using affineOpen_kernel_conormal_sections. Exterior powers commute with
associated sheaves and localization, giving the source coordinate isomorphism.
Conjugate the sheafified selfTorConormalComparison by these two coordinate
isomorphisms to obtain φ_U. On a basic open overlap, quotient resolutions localize,
the conormal identification sends the same ideal classes to the same unit sections,
and normalized Tor products localize. The uniqueness in
existsUnique_selfTor_conormal_comparison therefore identifies the maps on each
basic open. Such opens cover every overlap, so separatedness identifies the maps
on every open W mapping into two charts. This proves the displayed component
compatibility. Empty charts have unique component maps; the same construction
covers n=0, the zero ideal, the zero quotient, and nonregular ideals. Only local
maps are asserted here: no global morphism and no dual coordinate square is used. -/
theorem exists_compatible_affine_selfTor_maps
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let E := Scheme.Modules.exteriorSheaf
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n
    ∃ φ : ∀ U : Y.affineOpens, E.over (i ⁻¹ᵁ U.1) ⟶ Q.over (i ⁻¹ᵁ U.1),
      (∀ U, IsAffineSelfTorChartMap i U n E Q (φ U)) ∧
      ∀ (U U' : Y.affineOpens) (W : Z.Opens)
        (a : W ⟶ i ⁻¹ᵁ U.1) (b : W ⟶ i ⁻¹ᵁ U'.1),
        (φ U).val.app (op (Over.mk a)) =
          (φ U').val.app (op (Over.mk b)) := by sorry

end AlgebraicGeometry
