/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-!
# Change of rings preserves K-flat complexes with flat terms

Source: Stacks Project, Cohomology on Sites, Lemma 21.18.1, Tag 0G7E,
identity-topos coefficient-change case (blueprint: lem-pur-kflat-change-of-rings-independent).
-/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

open CategoryTheory.Limits in
private theorem restrictScalars_exact_kflat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B) :
    PreservesFiniteLimits (restrictScalars.{r} α) ∧
      PreservesFiniteColimits (restrictScalars.{r} α) := by
  let U := restrictScalars.{r} α
  have : PreservesFiniteLimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf B))
  have : PreservesFiniteColimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves U (toSheaf A)⟩

open CategoryTheory.Limits in
open CategoryTheory.Limits in
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (K : CochainComplex (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)

end SheafOfModules
