/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
/-! # Canonical principal Koszul and quotient towers

Source: Stacks Project, algebraization.tex Tag 0A0E and sites-cohomology.tex Tag 0941
(auxiliary; not a blueprint node).

The principal Koszul complexes are represented by mapping cones of multiplication on the
single complex. The transitions are the strict `t/id` and quotient maps,
with their tensor augmentations.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r ux vx

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}

/-- Iterated composite of an endomorphism.

Source: Stacks Project, algebraization.tex Tag 0A0E; this is the power of the regular
section used in the principal Koszul complex (auxiliary; not a blueprint node).
-/
noncomputable def endoPow {D : Type ux} [Category.{vx, ux} D] {X : D} (f : X ⟶ X) :
    ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => endoPow f n ≫ f

variable [EssentiallySmall.{r} C]
variable (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "𝓞" => (sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{r} 𝓞

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-- Cache the existing sheaf-composition property on an essentially small site.
Source: Mathlib, `CategoryTheory.Sites.Whiskering` (auxiliary; not a blueprint node).
Proof: apply the existing instance. Naming this proof avoids repeated search when
constructing the actual single-complex maps and their cones. -/
theorem principalKoszulHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by infer_instance

attribute [local instance 20000] principalKoszulHasSheafCompose

/-- Multiplication by a global section on the unit module sheaf.

Source: Stacks Project, algebraization.tex Tag 0A0E (auxiliary; not a blueprint node).
-/
noncomputable def globalSectionMultiplication
    (t : (SheafOfModules.unit 𝓞).sections) :
    SheafOfModules.unit 𝓞 ⟶ SheafOfModules.unit 𝓞 :=
  (SheafOfModules.unit 𝓞).unitHomEquiv.symm t

/-- The specified power multiplication map on the degree-zero ring complex.

Source: Stacks Project, algebraization.tex Tag 0A0E (auxiliary; not a blueprint node).
This named map shares the actual single-functor construction between the principal
cone and its component API, without unfolding the single-functor coherence record. -/
noncomputable def principalKoszulScalarComplex
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :=
  (CochainComplex.singleFunctor (𝒜) 0).map
    (endoPow (globalSectionMultiplication R t) (m + 1))

set_option backward.isDefEq.respectTransparency false in
/-- Tensor with the representative in the K-flat (second) variable. The canonical symmetry
identifies this model with `P ⊗ Q_m`, including its maps and augmentations.
Source: Stacks Tags 06YN and 0941
(auxiliary; not a blueprint node). -/
noncomputable def koszulTensorFunctor (P : CochainComplex 𝒜 ℤ) :
    CochainComplex 𝒜 ℤ ⥤ CochainComplex 𝒜 ℤ :=
  (MonoidalCategory.curriedTensor 𝒜).map₂CochainComplex.flip.obj P

end CategoryTheory
