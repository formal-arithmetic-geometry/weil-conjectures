/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S6
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData
import Sheaf.AlgebraicGeometry.PrescribedPointBertiniOpen
import Sheaf.AlgebraicGeometry.EffectiveCartierPureDimension
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Bertini for a linear system with finite prescribed base locus

Source: Stacks Project, Tag 0FD6, and blueprint main-20261015,
finite-cover-curve proof, paragraph 2, first derivative conditions.
(blueprint: lem-zl-prescribed-point-smooth-member).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry TensorProduct

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
  prescribedPointJet prescribedPointRestrictedFamily prescribedPointCombination
  prescribedPointMember prescribedPointVanishes

private theorem prescribedPointJet_zero {X : Scheme.{u}} (M : X.Modules)
    [M.IsInvertible] (x : X) : prescribedPointJet M x 0 = 0 := by
  classical
  unfold prescribedPointJet
  simp only [map_zero, dif_pos (Submodule.zero_mem _)]
  change (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent 0 ⊗ₜ[_] _ = 0
  rw [map_zero, TensorProduct.zero_tmul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An arbitrary finite linear system that immerses the complement of its prescribed
base locus and separates all jets has general smooth members of the expected dimension.
There is no ampleness, degree, basis or projective compactification assumption.

Source: Stacks Project, Tag 0FD6; blueprint main-20261015, finite-cover-curve proof,
paragraph 2, intersection of the smoothness and derivative open conditions.
(blueprint: lem-zl-prescribed-point-smooth-member).

Proof: The prescribed-point Bertini-open theorem supplies smoothness and nonzero
jets. Smooth connected X is regular and locally Noetherian, hence integral. At a
point of the nonempty S, a nonzero jet implies that the section is nonzero. Its
associated morphism from the structure module is therefore nonzero, so its zero
scheme is an effective Cartier divisor on this integral scheme. Componentwise
Cartier purity gives dimension d-1, and the member is affine because it is closed
in affine X. Finally the existing nonvanishing-locus/zero-support comparison
turns residue-fibre vanishing into containment of every prescribed point.
-/
theorem exists_open_smooth_prescribedPoint_member
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y)
    (hover : j ≫ f = X ↘ Spec (.of k))
    (M : Y.Modules) [M.IsInvertible] [((tensorPullback j).obj M).IsInvertible]
    (U : X.Opens) (hU : ∀ x : X, x ∈ U ↔ x ∉ S)
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤))
    (hvan : ∀ a : I → k, prescribedPointVanishes ((tensorPullback j).obj M) S
      (tensorSectionsUnit j M (prescribedPointCombination f M s a)))
    (hgen : ∃ ht : Epi ((((tensorPullback (U.ι ≫ j)).obj M).freeHomEquiv).symm
        (prescribedPointRestrictedFamily M j U s)),
      @IsImmersion U.toScheme _
        (@ProjectiveSpace.homOfGeneratingSections I inferInstance U.toScheme
          (Spec (.of k)) (U.ι ≫ (X ↘ Spec (.of k)))
          ((tensorPullback (U.ι ≫ j)).obj M)
          ((invertible_pullback_tensor (U.ι ≫ j)).1 M).2
          (prescribedPointRestrictedFamily M j U s) ht))
    (hjet : Function.Surjective (fun a : I → k ↦ fun x : S ↦
      prescribedPointJet ((tensorPullback j).obj M) x.val
        (tensorSectionsUnit j M (prescribedPointCombination f M s a)))) :
    ∃ O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
      (O : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
      ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
        Smooth ((prescribedPointMember f j M s a).subschemeι ≫ (X ↘ Spec (.of k))) ∧
        IsAffine (prescribedPointMember f j M s a).subscheme ∧
        (prescribedPointMember f j M s a).subscheme.IsPureDimension (d - 1) ∧
        (∀ x ∈ S, x ∈ (prescribedPointMember f j M s a).support) ∧
        ∀ x ∈ S, prescribedPointJet ((tensorPullback j).obj M) x
          (tensorSectionsUnit j M (prescribedPointCombination f M s a)) ≠ 0 := by
  classical
  obtain ⟨O, hO, hmembers⟩ := exists_open_prescribedPoint_bertini
    X d hd hdim S hS hclosed f j hover M U hU s hvan hgen hjet
  refine ⟨O, hO, ?_⟩
  intro a ha
  obtain ⟨hsm, hj⟩ := hmembers a ha
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := IsRegular.isIntegral X
  let L := (tensorPullback j).obj M
  let v := tensorSectionsUnit j M (prescribedPointCombination f M s a)
  have hv : v ≠ 0 := by
    obtain ⟨x, hx⟩ := hS
    intro hv
    exact hj x hx (by
      change prescribedPointJet L x v = 0
      rw [hv]
      exact prescribedPointJet_zero L x)
  have hφ : homOfGlobalSection L v ≠ 0 := by
    intro hφ
    have h := congrArg (fun φ : Scheme.Modules.unit X ⟶ L ↦
      φ.app ⊤ (1 : Γ(X, ⊤))) hφ
    apply hv
    rw [homOfGlobalSection_app_one, Scheme.Modules.presheaf_map_id_apply] at h
    exact h
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} (Scheme.Modules.unit X) :=
    inferInstanceAs (SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf))
  have hcart : (prescribedPointMember f j M s a).IsInvertible := by
    unfold prescribedPointMember
    change (homOfGlobalSection L v).zeroLocus.IsInvertible
    exact Hom.isInvertible_zeroLocus hφ
  have hdimH := (prescribedPointMember f j M s a).isPureDimension_of_isInvertible
    (X ↘ Spec (.of k)) d (by omega) hdim hcart
  have haff : IsAffine (prescribedPointMember f j M s a).subscheme := by
    exact isAffine_of_isAffineHom (prescribedPointMember f j M s a).subschemeι
  refine ⟨hsm, haff, hdimH, ?_, hj⟩
  intro x hx
  have hnot : x ∉ nonvanishingLocus L v := by
    have hvS := hvan a
    unfold prescribedPointVanishes at hvS
    exact not_not_intro (hvS x hx)
  rw [nonvanishingLocus_eq_compl_support_zeroLocus X L v] at hnot
  unfold prescribedPointMember
  change x ∈ (homOfGlobalSection L v).zeroLocus.support
  exact not_not.mp hnot

end

end AlgebraicGeometry
