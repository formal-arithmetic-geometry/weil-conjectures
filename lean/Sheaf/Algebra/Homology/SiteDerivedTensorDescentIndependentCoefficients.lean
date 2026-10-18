/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
import Sheaf.Algebra.Homology.KFlatResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic


public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
-- r4: side KFlat instances (global there), as local instances of the live theorems
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-!
# Derived tensor descent on a ringed site

Site object, morphism, and coefficient universes are independent. The site is essentially
small relative to the coefficient universe, as required by the source. The statement retains
every localization, representative-comparison, and transformation-extension clause.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0G7D, 06YT and 06YU;
Categories, Tags 04VI, 04VJ and 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent).

## Main statements

- `site_derived_tensor_descent_independentCoefficients`: localization, representative comparison,
  and unique extension of arbitrary natural transformations.
-/

@[expose] public section

universe u v r w e z

open CategoryTheory

namespace SheafOfModules

set_option autoImplicit false
set_option synthInstance.maxSize 4096
/-- K-flat complexes with flat terms present the derived category and its tensor bifunctor.
The existential predicate `P` specifies the full subcategory by its precise membership
condition; `B` is total tensor on homotopy categories, specified by a natural comparison
with total tensor on complexes. The comparison for `T` is natural in both homotopy variables.
Naturality also gives the inverse-denominator equations by multiplying the naturality square
by the inverses of the denominator images. The final bijection includes arbitrary natural
transformations, without an invertibility assumption.

Source: Stacks Project, Tags 06YS, 0G7D, 06YT, 06YU and Categories 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent).

Proof plan:
The recorded site flatness predicate is exactness of sheafified sectionwise tensor,
which is the canonical monoidal sheaf tensor used in the comparisons below.
1. Resolve the vertex of each Ore square and cancellation witness by a K-flat flat-term
   resolution (`lem-pc-kflat-resolution`). The right calculus of fractions for the ambient
   homotopy category (`lem-pc-quasi-isomorphisms-multiplicative-system`) restricts to `P`.
2. The localization universal property induces the comparison functor. Refine every roof
   by a K-flat flat-term resolution to prove fullness (`lem-pc-right-fraction-representation`).
   Resolve common refinement vertices to prove faithfulness
   (`lem-pc-right-fraction-common-refinement`). Resolutions give essential surjectivity.
3. Total tensor descends through homotopy: a homotopy in the first variable is `h ⊗ 1`;
   in the second variable its component in bidegree `(p,q)` is `(-1)^p 1 ⊗ k`.
   The cross differential terms cancel, giving the natural comparison defining `B`.
4. Tensoring a quasi-isomorphism with a K-flat complex preserves quasi-isomorphisms:
   its cone is acyclic (`lem-pur-quasi-iso-cone-acyclic`), tensor preserves its acyclicity
   (`def-pc-kflat-complex`), and total tensor commutes with the cone differential.
   The symmetry with sign `(-1)^(pq)` gives the other variable.
5. Localize the tensor bifunctor twice (`lem-weil-pbc-localization-universal-property`),
   first into a functor category, then in the other variable. This gives `T` and its natural
   representative comparison. Inverting the naturality equations gives compatibility with
   inverse denominators.
6. Extend a transformation uniquely in the first variable by the same localization property.
   Uniqueness implies naturality in the second variable. Localize that variable to get the
   extension on the product derived category. Two applications of uniqueness prove bijectivity.
-/
theorem site_derived_tensor_descent_independentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ P : ObjectProperty (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)),
      (∀ X, P X ↔ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) X.as ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n)) ∧
      (∃ F : ((HomotopyCategory.quasiIso (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Localization ⥤ (DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
        F.IsEquivalence ∧ Nonempty (((HomotopyCategory.quasiIso (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Q ⋙ F ≅ (P.ι ⋙ DerivedCategory.Qh))) ∧
      (∃ B : (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)) ×
          (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)) ⥤
          (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)),
        Nonempty (((HomotopyCategory.quotient (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)).prod
          (HomotopyCategory.quotient (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ))) ⋙ B ≅
          Functor.uncurry.obj
            ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) _
          (SheafOfModules.monoidalCategory.{v, u, r} R)).map₂HomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
                (HomotopyCategory.quotient (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ))) ∧
        ∃ T : (DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ×
          (DerivedCategory
          (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⥤
          (DerivedCategory
          (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
          Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
            ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ T)) ∧
      (∀ (E : Type e) (_ : Category.{z} E)
        (U V : (DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ×
          (DerivedCategory
          (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⥤ E),
        Function.Bijective (fun τ : U ⟶ V ↦
          Functor.whiskerLeft ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ)) := by
  sorry

/-- The derived tensor supplied by the resolving-class localization, in independent universes.
The natural representative comparison and unique-extension property of
`site_derived_tensor_descent_independentCoefficients` determine this functor up to the
unique compatible natural isomorphism. No functorial resolutions are chosen.
Source: Stacks, Tags 06YS, 0G7D, 06YT, 06YU
(blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
noncomputable def siteDerivedTensorIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ×
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.2.choose

end SheafOfModules
