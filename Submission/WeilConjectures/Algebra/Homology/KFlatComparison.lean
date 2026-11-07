/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.Algebra.Homology.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Complete.NormalizedTower
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Comparison of the notions of flatness and K-flatness for sheaves of modules

Let `R` be a sheaf of commutative rings on a site, with the tensor product
`SheafOfModules.monoidalCategory R` and its symmetry `SheafOfModules.symmetricCategory R`.

## Main statements

- `CochainComplex.isKFlatTensor_iff_kFlat`: a complex `K` of `R`-modules is K-flat in the sense
  of `CochainComplex.IsKFlatTensor` (tensoring an acyclic complex with `K` gives an acyclic
  complex) if and only if it is K-flat for the class of quasi-isomorphisms,
  `(HomologicalComplex.quasiIso _ _).kFlat K` (tensoring with `K` on either side preserves
  quasi-isomorphisms).
- `CochainComplex.isKFlatTensor_iff_isKFlat`: the same with `CochainComplex.IsKFlat`.
- `SheafOfModules.isFlat_iff_flat`: a sheaf of modules is flat in the sense of
  `SheafOfModules.IsFlat` (`G ↦ G ⊗ F` is exact) if and only if it satisfies
  `ObjectProperty.flat` (`F ⊗ -` and `- ⊗ F` are exact).

Source: Stacks Project, Cohomology on Sites, Definition `sites-cohomology-definition-K-flat`
(Tag 06YN) and Lemma 06YD; Modules on Sites, Definition 03ER, item (3).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝒜" =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

noncomputable local instance : MonoidalCategory 𝒜 := SheafOfModules.monoidalCategory R

noncomputable local instance : SymmetricCategory 𝒜 := SheafOfModules.symmetricCategory R

variable [HasColimitsOfSize.{0, 0} 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜]

set_option synthInstance.maxSize 256 in
/-- A complex `K` of sheaves of `R`-modules is K-flat in the sense of
`CochainComplex.IsKFlatTensor` (`Tot(F ⊗ K)` is acyclic for every acyclic `F`) if and only if it
is K-flat with respect to quasi-isomorphisms: tensoring with `K` on either side preserves
quasi-isomorphisms. By the symmetry of the tensor product, the two one-sided conditions on
acyclic complexes agree (Stacks, Tags 06YN and 06YD). -/
theorem isKFlatTensor_iff_kFlat (K : CochainComplex 𝒜 ℤ) :
    K.IsKFlatTensor ↔ (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro hK Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (mapBifunctor Z K (curriedTensor _))).2 (hK Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩
  · intro hK F hF
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (hK _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).2 hF)).2


end CochainComplex

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝒜" =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

noncomputable local instance : MonoidalCategory 𝒜 := SheafOfModules.monoidalCategory R

noncomputable local instance : SymmetricCategory 𝒜 := SheafOfModules.symmetricCategory R


end SheafOfModules
