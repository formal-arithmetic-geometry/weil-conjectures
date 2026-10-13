/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne
import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties

/-! # Unital comparisons on K-flat representatives for translation by one

Source: Stacks Project, Tag 08EU, proof, and Cohomology, equation (20.54.2.1).
(blueprint: lem-sc-derived-monoidal-pullback-unital-shift-kflat-one).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Simultaneously chosen exact shift structures with their comparison squares only
on K-flat representatives and only for translation by one.
Source: Stacks Project, Tags 08EU, 0A9U and 0A9S,
equation-compare-with-pullback; the representative calculation in steps 1 and 2 of
lem-sc-derived-monoidal-pullback-unital-shift.
(blueprint: lem-sc-derived-monoidal-pullback-unital-shift-kflat-one).

Proof. Total tensor products of K-flat resolutions compute the recorded derived
monoidal structure. The Koszul comparison for translation of the first factor is
natural in the second factor and identifies the tensor of a mapping-cone triangle
with the mapping-cone triangle of the tensor map. Its zero and addition identities
descend through K-flat localization to coherent shifts on each tensorRight functor.
Termwise tensor pullback of K-flat resolutions likewise preserves mapping cones.
Choose its shift comparison jointly with the tensor comparisons for the supplied
strong monoidal structure: express translation as tensor with the translated unit
and use its inverse tensorator and unit isomorphism. Tensorator associativity gives
addition coherence and the unit equations give zero coherence. The representative
cone comparisons give the exactness clauses. For translation by one, naturality of
the Koszul comparison gives the tensor-morphism squares on both schemes;
tensorator associativity gives the inverse-tensorator square. The complex right
unitor identifies the translation comparison for tensor with the unit with
translation itself, giving the final square. These calculations are equalities
of localized maps at K-flat representatives. No extension to arbitrary derived
objects or to any other nonzero shift is asserted. That extension uses naturality,
K-flat replacement isomorphisms, and coherent integer-shift addition separately.
Zero factors give zero maps; empty schemes give the zero category; translation by
zero follows from the unit equations, with no cancellation of a noninvertible map. -/
theorem derivedMonoidalPullback_unitalShift_kFlat_one
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sF
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Y} (b : M ⟶ N)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((curriedTensor (schemeDerivedCategory Y)).flip.map b)
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K ≫ (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((tensorRight N).commShiftIso (1 : ℤ)).hom.app K) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Z.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((curriedTensor (schemeDerivedCategory Z)).flip.map b)
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K ≫ (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((tensorRight N).commShiftIso (1 : ℤ)).hom.app K) ∧
      (∀ (M : schemeDerivedCategory Y)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M)
        ((tensorRight M ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫
            ((derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M)).commShiftIso
              (1 : ℤ)).hom.app K) ∧
      (∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := (rightUnitorNatIso (schemeDerivedCategory Y)).hom
        ((tensorRight (𝟙_ (schemeDerivedCategory Y))).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((𝟭 (schemeDerivedCategory Y)).commShiftIso
            (1 : ℤ)).hom.app K) := by
  let := schemeCanonicalTensorShift Y
  let := schemeCanonicalTensorShift Z
  let sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
    fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
  let sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ :=
    fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
  obtain ⟨sF, hF, hδ⟩ := derivedPullback_canonicalTensorShift_one f
  let := sF
  have hY := schemeCanonicalTensorShift_properties Y
  have hZ := schemeCanonicalTensorShift_properties Z
  refine ⟨sF, sY, sZ, hF, hZ.1, ?_, ?_, hδ, hY.2⟩
  · intro M N b P _
    have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Y)).flip.map b) ℤ :=
      Functor.CommShift₂.commShift_flip_map (h := .int) b
    exact NatTrans.shift_app_comm _ (1 : ℤ) (DerivedCategory.Q.obj P)
  · intro M N b P _
    have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Z)).flip.map b) ℤ :=
      Functor.CommShift₂.commShift_flip_map (h := .int) b
    exact NatTrans.shift_app_comm _ (1 : ℤ) (DerivedCategory.Q.obj P)



end AlgebraicGeometry
