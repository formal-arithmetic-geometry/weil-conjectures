/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedKoszulSystem

/-! # Normalized principal Koszul Roos presentation comparison

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E;
sites-cohomology.tex, Tag 0941.
(blueprint: lem-pur-principal-koszul-roos-presentation-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})

-- Choose the standard degreewise product directly, avoiding recursive limit search.
local instance (priority := 1100)
    (H : ℕ → CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) : HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete ℕ) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{u} (D := Discrete ℕ)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).has_limit
        (Discrete.functor H)


/-- The zero-coordinate Roos lift of a strict augmentation of a tower of complexes.
This factors the construction through abstract tower data to avoid unfolding a concrete
Koszul tensor tower while checking its compatibility proof.
Source: Stacks Tag 0941
(blueprint: lem-pur-principal-koszul-roos-presentation-comparison). -/
def principalTowerRoosUnit
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    P ⟶ roosF.obj (koszulTowerComplex R T) :=
  roosAugment (X := koszulTowerComplex R T) (fun n ↦ γ.app (op n))
    (fun n ↦ (γ.naturality (homOfLE (Nat.le_succ n)).op).symm.trans
      (Category.id_comp _))

/-- The strict degree-zero unit into the principal Koszul Roos complex.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-principal-koszul-roos-presentation-comparison). -/
def principalKoszulRoosUnit
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    P ⟶ roosF.obj (koszulTowerComplex R (koszulTensorTower R P a)) :=
  principalTowerRoosUnit R P (koszulTensorTower R P a) (koszulStrictAugmentation R P a)

/-- The negative principal cone and the dual singleton Koszul system give the same
normalized strict derived completion, for every presentation of the latter.

Source: Stacks Project, algebraization.tex, proof of Tag 0A0E;
sites-cohomology.tex, Tag 0941
(blueprint: lem-pur-principal-koszul-roos-presentation-comparison).

Proof: evaluate the dual positive two-term Koszul complex at one in each of its two
nonzero degrees. The signed Hom differential identifies it with the negative cone of
multiplication by a^(n+1). The inverse dual transitions have components (a,1), and the
dual projection is the degree-zero cone inclusion. Tensor symmetry therefore gives an
augmentation-compatible strict tower isomorphism. The normalized strict Roos comparison
identifies its cone with total derived inverse limit. The uniqueness of the right-derived
functor compares that inverse limit with D.inverseLimit, respecting the comparison units;
D.tensorFactors identifies the descended tower on the representative P. Naturality at the
specified localization representative gives D.unit at Q(P), hence the displayed equality.
Finite free Koszul factors preserve quasi-isomorphisms, so P need not be K-flat. Zero
complexes, a zero section, and an invertible section obey the same chain calculations.
-/
theorem principalKoszulRoos_presentation_comparison
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ ⟨a.val, a.property⟩)) :
    ∃ e : DerivedCategory.Q.{w}.obj
        (roosF.obj (koszulTowerComplex R (koszulTensorTower R P a))) ≅
          D.completion.obj (DerivedCategory.Q.{w}.obj P),
      DerivedCategory.Q.{w}.map (principalKoszulRoosUnit R P a) ≫ e.hom =
        D.unit (DerivedCategory.Q.{w}.obj P) := by
  sorry

end CategoryTheory
