/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Koszul reconstruction of a derived-complete reduction tower

Source: Stacks Project, algebraization.tex Tag 0A0E and sites-cohomology.tex Tag 0941
(blueprint: lem-pur-derived-complete-koszul-reconstruction).

The strict towers and quotient maps are the canonical constructions of
`def-pur-principal-koszul-quotient-towers`. Total right derived inverse limit is
provided by the recorded strict-tower homotopy-limit dependency.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
variable {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "𝓞" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{r} 𝓞

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance] SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

variable [HasDerivedCategory.{w} 𝒜]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ 𝒜)]

/-- Total right derived inverse limit supplied by the strict-tower dependency. The defining
universal property determines this functor up to unique natural isomorphism.
Source: Stacks Tag 0941 (blueprint: lem-pur-derived-complete-koszul-reconstruction). -/
noncomputable def koszulRlim : DerivedCategory.{w} (ℕᵒᵖ ⥤ 𝒜) ⥤ DerivedCategory.{w} 𝒜 :=
  Classical.choose (ringedStrictTowerHomotopyLimitIndependentCoefficients J 𝓞
    (fun U a b ↦ @mul_comm (R.obj.obj U) _ a b))

/-- The derived strict Koszul completion, using the total right derived inverse limit.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-derived-complete-koszul-reconstruction). -/
noncomputable def koszulCompletion (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) : DerivedCategory.{w} 𝒜 :=
  (koszulRlim R).obj (DerivedCategory.Q.obj
    (koszulTowerComplex R (koszulTensorTower R P t)))

/-- Koszul reconstruction of the derived-complete quotient tower.

Source: Stacks Tag 0A0E, lemma-derived-completion-koszul; Tag 0941,
lemma-derived-limit-is-ok (blueprint: lem-pur-derived-complete-koszul-reconstruction).

Proof: (1) Since `t` is monic, every positive power is monic. The principal cone has
zero cohomology in degree `-1` and quotient cohomology in degree zero, hence its quotient
augmentation is a quasi-isomorphism. The `t/id` and quotient transitions commute strictly.
(2) K-flatness of `P` tensors the acyclic cone of this augmentation to an acyclic complex.
Our tensor order is `Q_m ⊗ P`, exactly the recorded K-flat convention; symmetry identifies
it with the source's `P ⊗ Q_m`. Thus the strict tensor map is levelwise a quasi-isomorphism.
(3) Exact level evaluations identify this with a quasi-isomorphism in the tower category.
The total right derived limit functor of the strict-tower dependency inverts it and
preserves the equality of the strict augmentation composites.
(4) The dependency supplies a Roos triangle on that actual derived limit. In any given
quotient Roos triangle whose first map has the canonical quotient components through `e`,
the product of the level comparisons is invertible. TR3 on rotated triangles with its
inverse on both products gives `φ`; two-out-of-three makes `φ` invertible. The first
triangle equation gives all projection equations, and the third gives the displayed
shifted connecting equation for this very same `φ`.
-/
theorem derivedComplete_koszul_reconstruction
    (t : (SheafOfModules.unit 𝓞).sections)
    (hreg : Mono (globalSectionMultiplication R t))
    (P : CochainComplex 𝒜 ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P) :
    let V := koszulTensorTower R P t
    let U := reductionTensorTower R P t
    let a := koszulTensorTowerComparison R P t
    let aC := koszulTowerComplexMap R a
    let VD := fun m : ℕ ↦ DerivedCategory.Q.{w}.obj (V.obj (op m))
    let UD := fun m : ℕ ↦ DerivedCategory.Q.{w}.obj (U.obj (op m))
    let aD := fun m : ℕ ↦ DerivedCategory.Q.{w}.map (a.app (op m))
    let v := fun m : ℕ ↦ DerivedCategory.Q.{w}.map
      (V.map (homOfLE (Nat.le_succ m)).op)
    let u := fun m : ℕ ↦ DerivedCategory.Q.{w}.map
      (U.map (homOfLE (Nat.le_succ m)).op)
    (∀ m : ℕ, QuasiIso (a.app (op m))) ∧ QuasiIso aC ∧
      IsIso (DerivedCategory.Q.{w}.map aC) ∧
      IsIso ((koszulRlim R).map (DerivedCategory.Q.{w}.map aC)) ∧
      ((koszulRlim R).map (DerivedCategory.Q.{w}.map
          (koszulTowerComplexMap R (koszulStrictAugmentation R P t))) ≫
        (koszulRlim R).map (DerivedCategory.Q.{w}.map aC) =
        (koszulRlim R).map (DerivedCategory.Q.{w}.map
          (koszulTowerComplexMap R (koszulStrictAugmentation R P t ≫ a)))) ∧
      ∃ (_hV : HasProduct VD) (_hU : HasProduct UD)
        (pV : koszulCompletion R P t ⟶ ∏ᶜ VD)
        (δV : ∏ᶜ VD ⟶ (koszulCompletion R P t)⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle v (koszulCompletion R P t) pV δV ∧
        IsIso (Limits.Pi.map aD) ∧
        ∀ (K : DerivedCategory.{w} 𝒜) (e : DerivedCategory.Q.{w}.obj P ≅ K)
          (pU : K ⟶ ∏ᶜ UD) (δU : ∏ᶜ UD ⟶ K⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle u K pU δU →
          (∀ m : ℕ, pU ≫ Limits.Pi.π UD m =
            e.inv ≫ DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P t m)) →
          ∃ φ : K ≅ koszulCompletion R P t,
            (∀ m : ℕ, φ.hom ≫ pV ≫ Limits.Pi.π VD m ≫ aD m =
              e.inv ≫ DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P t m)) ∧
            φ.hom ≫ pV ≫ Limits.Pi.map aD = pU ∧
            Limits.Pi.map aD ≫ δU = δV ≫ φ.inv⟦(1 : ℤ)⟧' := by
  sorry

end CategoryTheory
