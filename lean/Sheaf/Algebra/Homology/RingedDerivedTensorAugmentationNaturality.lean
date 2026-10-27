/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DiagramKFlatReplacements

/-! # Naturality of the derived-to-ordinary tensor augmentation

Source: Stacks Project, sites-cohomology.tex, Tag 0FPH,
lemma-tensor-pull-compatibility, the horizontal arrows in its resolution diagram;
Tags 06YS and 06YU for the unbounded K-flat construction.
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality).

The source and target are functors on pairs of actual complexes. The ordinary
localized total tensor is not asserted to descend to the derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)]

/-- The published derived tensor, precomposed with localization in both complex variables.
Source: Stacks, Tags 06YU and 0FPH
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality). -/
abbrev ringedTensorAugmentationSource :
    CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
      DerivedCategory (Modules R) :=
  ((DerivedCategory.Q : CochainComplex (Modules R) ℤ ⥤ DerivedCategory (Modules R)).prod
    DerivedCategory.Q) ⋙ Functor.uncurry.obj (derivedTensor R)

/-- Localization after the existing signed direct-sum total tensor on complexes.
Source: Stacks, Tags 06YM and 0FPH
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality). -/
abbrev ringedTensorAugmentationTarget :
    CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
      DerivedCategory (Modules R) :=
  Functor.uncurry.obj (totalTensor R) ⋙ DerivedCategory.Q

/-- There is a unique natural augmentation from derived tensor to localized ordinary tensor,
with the specified inverse representative comparison on flat-term K-flat pairs and the
normalization for every pair of flat-term K-flat resolutions. Naturality for arbitrary maps
`a` and `b` is the naturality equation of `ρ` at `Prod.mkHom a b`. No boundedness or flatness
is required of the target complexes. Uniqueness expresses independence of resolution choices.

Source: Stacks Project, Tag 0FPH, lemma-tensor-pull-compatibility, horizontal resolution
arrows; Tags 06YS and 06YU for resolutions and their tensor comparisons.
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality).

Proof plan:
1. For resolutions p : P → A and q : N → B (lem-pc-kflat-resolution), write D(p,q)
   for tensor(Qp,Qq) and c for representativeIso. Localization inverts D(p,q).
   Define r(p,q) = D(p,q)⁻¹ ≫ c⁻¹ ≫ Q(total(p,q)). No inverse of the last map is used.
2. If the resolutions are refined by quasi-isomorphisms between flat-term K-flat
   complexes, naturality of c (lem-weil-pbc-site-derived-tensor-descent) and functoriality
   cancel their invertible D-images, proving that r is unchanged.
3. For two arbitrary resolutions, apply strict-diagram K-flat replacement to their
   finite cospans (lem-weil-pbc-diagram-kflat-replacements). The comparison maps to the
   common resolved target are quasi-isomorphisms by two-out-of-three. Step 2 identifies
   both values with the common value. Define ρ by this independent value.
4. For arbitrary maps a and b, replace their walking-arrow diagrams strictly by the same
   diagram theorem. The resulting squares commute on complexes. Functoriality of total
   tensor and naturality of c give Q(total(a,b)) ∘ ρ = ρ ∘ tensor(Qa,Qb). These comparison
   maps need not be quasi-isomorphisms; only the resolution augmentations are inverted.
5. Identity resolutions give ρ(P,N) = c⁻¹. Multiplying the defining formula by D(p,q)
   gives the stated normalization for every choice. Conversely that equation determines
   every component since D(p,q) is invertible, proving uniqueness. All resolutions used
   are available for unbounded complexes, so no extra hypotheses on A or B are needed.
-/
theorem exists_unique_ringedTensorAugmentation :
    ∃! ρ : ringedTensorAugmentationSource R ⟶ ringedTensorAugmentationTarget R,
      ∀ (P N : CochainComplex (Modules R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients P)
        (hN : CochainComplex.IsKFlatIndependentCoefficients N)
        (hPf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
        (hNf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (N.X n)),
        ρ.app (P, N) = (representativeIso R P N hP hN hPf hNf).inv ∧
        ∀ (A B : CochainComplex (Modules R) ℤ) (p : P ⟶ A) (q : N ⟶ B),
          QuasiIso p → QuasiIso q →
            (ringedTensorAugmentationSource R).map (Prod.mkHom p q) ≫ ρ.app (A, B) =
              ρ.app (P, N) ≫ (ringedTensorAugmentationTarget R).map (Prod.mkHom p q) := by
  sorry

/-- The canonical augmentation selected from its unique characterization. The theorem
fixes every component, so this choice does not choose unspecified mathematical data.
Source: Stacks, Tag 0FPH, horizontal arrows in the resolution diagram
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality). -/
def ringedTensorAugmentation :
    ringedTensorAugmentationSource R ⟶ ringedTensorAugmentationTarget R :=
  (exists_unique_ringedTensorAugmentation R).exists.choose

end SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SheafOfModules

/-- Derived tensor of localized complexes in the given representative presentation.
Source: Stacks, Tags 06YU and 0FPH
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality). -/
abbrev modelTensorAugmentationSource (X : RingedTensorCorner.{u, w}) :=
  ((DerivedCategory.Q : CochainComplex X.mateModules ℤ ⥤ X.mateDerived).prod
    DerivedCategory.Q) ⋙ X.tensor

/-- Localization of ordinary signed direct-sum total tensor, without deriving its target.
Source: Stacks, Tags 06YM and 0FPH
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality). -/
abbrev modelTensorAugmentationTarget (X : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj (KFlatFixedTensor.totalTensor X.ring) ⋙ DerivedCategory.Q

/-- The natural tensor augmentation is uniquely determined in every representative model.
Its naturality applies to arbitrary cochain maps; the normalization applies to every
flat-term K-flat resolution, including identity resolutions of flat-term K-flat objects.
Source: Stacks, Tag 0FPH, horizontal resolution arrows, and Tags 06YS, 06YU
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality).

Proof: for resolutions p:P→A and q:Q→B, let D(p,q) be their derived tensor.
Define the component as D(p,q) inverse, followed by the inverse representative
comparison, followed by localization of Tot(p tensor q). Naturality of the
representative comparison cancels refinements between flat K-flat resolutions.
For arbitrary choices, resolve their finite cospans using the strict diagram
replacement theorem; two-out-of-three makes the refinement maps quasi-isomorphisms,
so both formulas agree. Resolving walking-arrow diagrams in both variables proves
naturality for arbitrary maps. Identity resolutions give the inverse representative
comparison. Multiplication by D(p,q) gives the displayed normalization for every
resolution. Since D(p,q) is invertible this equation also gives uniqueness. This
is the existing augmentation transported through the tensor descent equivalence;
no inverse of the ordinary tensor augmentation is used. -/
theorem modelTensorAugmentation_existsUnique (X : RingedTensorCorner.{u, w})
    (a : RingedTensorModel X) :
    ∃! ρ : modelTensorAugmentationSource X ⟶ modelTensorAugmentationTarget X,
      ∀ (P Q : CochainComplex X.mateModules ℤ) (hP : X.mateFlat P) (hQ : X.mateFlat Q),
        ρ.app (P, Q) = a.mateRepresentative.inv.app (⟨P, hP⟩, ⟨Q, hQ⟩) ∧
        ∀ (A B : CochainComplex X.mateModules ℤ) (p : P ⟶ A) (q : Q ⟶ B),
          QuasiIso p → QuasiIso q →
            (modelTensorAugmentationSource X).map (Prod.mkHom p q) ≫ ρ.app (A, B) =
              ρ.app (P, Q) ≫ (modelTensorAugmentationTarget X).map (Prod.mkHom p q) := by
  sorry

/-- The existing canonical augmentation expressed in the given tensor presentation.
Source: Stacks, Tag 0FPH; uniquely determined by all resolution augmentations
(blueprint: lem-sfb-ringed-derived-tensor-augmentation-naturality). -/
def modelTensorAugmentation (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X) :
    modelTensorAugmentationSource X ⟶ modelTensorAugmentationTarget X :=
  Classical.choose (modelTensorAugmentation_existsUnique X a)

end SheafOfModules
