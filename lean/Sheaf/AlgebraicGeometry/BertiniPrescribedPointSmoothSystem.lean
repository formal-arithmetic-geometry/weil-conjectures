/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData
import Sheaf.AlgebraicGeometry.PrescribedPointEventualJetSystem
import Sheaf.AlgebraicGeometry.PrescribedPointSmoothMember

/-!
# High-degree systems through prescribed points with smooth members

Source: blueprint main-20261015, proof of lem-zl-bertini-finite-cover-curve, paragraph 2;
Stacks Project, Varieties, Tags 0FD5 and 0FD6; Coherent, Tag 0B5T.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system).

The kernel is presented by a finite basis: every section vanishing on the reduced finite
set has a unique coefficient tuple. Thus its affine parameter space is literally the affine
space in these coordinates. First-order values use the canonical model
`(m / m²) ⊗[O_x] L_x`. Since `m` annihilates `m / m²`, this is canonically
`(m / m²) ⊗[κ(x)] (L_x ⊗[O_x] κ(x))`, and at a closed point over the algebraically
closed field it is the tensor product over `k` displayed in the source.
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

private theorem cachedSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := by
  infer_instance

private theorem cachedWEquals (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{u} := by
  infer_instance

attribute [local instance] cachedSheafify cachedWEquals

attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

attribute [local irreducible] tensorPullback tensorPullbackObj
  ProjectiveSpace.homOfGeneratingSections tensorSectionsUnit

attribute [local irreducible] prescribedPointJet prescribedPointRestrictedFamily
  prescribedPointCombination prescribedPointMember prescribedPointVanishes

private theorem combination_zero {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) : prescribedPointCombination f M s (0 : I → k) = 0 := by
  classical
  simp only [prescribedPointCombination, Pi.zero_apply, map_zero, zero_smul,
    Finset.sum_const_zero]

private theorem combination_sub {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (a b : I → k) :
    prescribedPointCombination f M s (a - b) =
      prescribedPointCombination f M s a - prescribedPointCombination f M s b := by
  classical
  simp only [prescribedPointCombination, Pi.sub_apply, map_sub, sub_smul,
    Finset.sum_sub_distrib]

set_option maxHeartbeats 800000 in
-- The unchanged dependent signature and its section-type conversions need this budget.
/-- High-degree prescribed-point systems generate and immerse off the base points,
separate simultaneous first-order values, and have a nonempty open of smooth members.

Source: blueprint main-20261015, finite-cover-curve proof, paragraph 2;
Stacks Project, Tags 0FD5, 0FD6 and 0B5T.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system).

Proof: Apply the eventual interpolation theorem, which supplies the bound, the
complement of the finite set, and a kernel basis whose system generates, immerses
and separates simultaneous jets. Fix a degree beyond the bound. The coefficient
combination is additive and sends zero to zero. Uniqueness of the representation
of zero in the kernel makes this combination injective: subtract two coefficient
tuples with the same section and use uniqueness for zero. Consequently every
coefficient tuple represents a section of the kernel. The fixed-system Bertini
smooth-member theorem applies to this vanishing family and its generation,
immersion and jet-surjectivity properties. It supplies the coefficient open and
all the stated geometric properties. The interpolation bound works for every
larger degree, giving the required uniform conclusion.
-/
theorem exists_eventual_prescribedPoint_smoothSystem
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (N : ℕ) (Y : Scheme.{u}) [IsReduced Y]
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) [IsClosedImmersion c]
    (j : X ⟶ Y) [IsOpenImmersion j] (hdense : DenseRange j)
    (hchart : Set.range j = c ⁻¹' (ProjectiveSpace.standardOpen
      (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ⟨0⟩ : Set _))
    (hover : j ≫ c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)) =
      X ↘ Spec (.of k)) :
    ∃ (n₀ : ℕ) (U : X.Opens),
      (∀ x : X, x ∈ U ↔ x ∉ S) ∧
      ∀ n : ℕ, n₀ ≤ n →
        ∃ (I : Type u) (_ : Fintype I) (s : I → Γ(prescribedPointTwist c n, ⊤)),
          (∀ v : Γ(prescribedPointTwist c n, ⊤),
            prescribedPointVanishes ((tensorPullback j).obj (prescribedPointTwist c n)) S
                (tensorSectionsUnit j (prescribedPointTwist c n) v) ↔
              ∃! a : I → k, prescribedPointCombination
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                (prescribedPointTwist c n) s a = v) ∧
          (∃ ht : Epi ((((tensorPullback (U.ι ≫ j)).obj
              (prescribedPointTwist c n)).freeHomEquiv).symm
                (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s)),
            IsImmersion (@ProjectiveSpace.homOfGeneratingSections I inferInstance
              U.toScheme (Spec (.of k)) (U.ι ≫ (X ↘ Spec (.of k)))
              ((tensorPullback (U.ι ≫ j)).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor (U.ι ≫ j)).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s) ht)) ∧
          Function.Surjective (fun a : I → k ↦ fun x : S ↦
            @prescribedPointJet X ((tensorPullback j).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor j).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              x.val
              (tensorSectionsUnit j (prescribedPointTwist c n)
                (prescribedPointCombination
                  (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                  (prescribedPointTwist c n) s a))) ∧
          ∃ O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
            (O : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
            ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
              Smooth ((prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).subschemeι ≫ (X ↘ Spec (.of k))) ∧
              IsAffine (prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).subscheme ∧
              (prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).subscheme.IsPureDimension (d - 1) ∧
              (∀ x ∈ S, x ∈ (prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).support) ∧
              ∀ x ∈ S, @prescribedPointJet X
                ((tensorPullback j).obj (prescribedPointTwist c n))
                ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor j).1) (prescribedPointTwist c n)
                  ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2 x
                (tensorSectionsUnit j (prescribedPointTwist c n)
                  (prescribedPointCombination
                    (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                    (prescribedPointTwist c n) s a)) ≠ 0 := by
  classical
  have hbase := exists_eventual_prescribedPoint_jetSystem
    (k := k) X S hS hclosed N Y c j hdense hchart hover
  obtain ⟨n₀, U, hU, hsystem⟩ := hbase
  refine ⟨n₀, U, hU, ?_⟩
  intro n hn
  obtain ⟨I, hI, s, hkernel, hgen, hjet⟩ := hsystem n hn
  let _ : Fintype I := hI
  let M := prescribedPointTwist c n
  let f := c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k))
  let _ : M.IsInvertible :=
    ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2
  let _ : ((tensorPullback j).obj M).IsInvertible :=
    ((invertible_pullback_tensor j).1 M).2
  have hzero := combination_zero f M s
  have hsub := combination_sub f M s
  obtain ⟨a₀, _, ha₀⟩ := (hkernel 0).mp (by
    unfold prescribedPointVanishes
    intro x hx
    simp only [map_zero]
    exact Submodule.zero_mem _)
  have hinj : Function.Injective (prescribedPointCombination f M s) := by
    intro a b hab
    have hab₀ : prescribedPointCombination f M s (a - b) = 0 := by
      rw [hsub, hab, sub_self]
    exact sub_eq_zero.mp ((ha₀ _ hab₀).trans (ha₀ _ hzero).symm)
  have hvan (a : I → k) : prescribedPointVanishes ((tensorPullback j).obj M) S
      (tensorSectionsUnit j M (prescribedPointCombination f M s a)) := by
    apply (hkernel _).mpr
    exact ⟨a, rfl, fun b hb ↦ hinj hb⟩
  have hhover : j ≫ f = X ↘ Spec (.of k) := by
    simpa only [f, Category.assoc] using hover
  have hmember := exists_open_smooth_prescribedPoint_member
    X d hd hdim S hS hclosed f j hhover M U hU s
  have hmember := hmember hvan
  have hmember := hmember hgen
  have hmember := hmember hjet
  obtain ⟨O, hO, hmembers⟩ := hmember
  exact ⟨I, hI, s, hkernel, hgen, hjet, O, hO, hmembers⟩

end

end AlgebraicGeometry
