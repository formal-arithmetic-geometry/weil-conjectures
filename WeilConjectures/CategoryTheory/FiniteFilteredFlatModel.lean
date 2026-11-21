/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.UniformFiniteFilteredLocalization
public import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Quotient
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import WeilConjectures.Algebra.Homology.CyclePullbackResolution
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.CategoryTheory.Right.RightFractionDenseSubcategory
import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # Split flat models with a fixed finite filtration
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe uC vC w

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})

/-- The module sheaves over the coefficient sheaf on the given site. -/
abbrev finiteFilteredModules (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- Cochain complexes of the module sheaves, with the coefficient universe explicit. -/
abbrev finiteFilteredComplex (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{w}) :=
  CochainComplex (finiteFilteredModules J R) ℤ

/-- The split-flat and K-flat hypotheses used for a resolving filtered complex.
Splitting is imposed on module-sheaf maps in each degree, not on chain maps.
For a finite filtration the successor inclusions split exactly when the whole
filtration is degreewise a sum of its graded pieces. -/
def IsSplitFlatFiltered
    (K : WeilFilteredObject (finiteFilteredComplex J R)) : Prop :=
  (∀ p n : ℤ,
    IsSplitMono ((Subobject.ofLE (K.filtration.F (p + 1)) (K.filtration.F p)
      (K.filtration.F_succ_le p)).f n)) ∧
  (∀ p n : ℤ,
    SheafOfModules.IsFlatOnSite.{uC, vC, w, w} (J := J) (R := R)
      ((K.filtration.gradedPiece p).X n)) ∧
  CochainComplex.IsKFlatIndependentCoefficients (R := R) K.obj ∧
  (∀ p : ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (K.filtration.F p : finiteFilteredComplex J R) ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := R) (K.filtration.gradedPiece p))

/-- The split-flat property on objects of the actual filtered homotopy category.
The homotopy quotient has the same objects as the complex category. Its full
subcategory on these objects is the homotopy category of split-flat complexes. -/
def finiteFilteredSplitFlatProperty (a b : ℤ) :
    ObjectProperty (UniformFilteredHomotopyCategory (finiteFilteredModules J R)
      (some (a, b)) (CochainComplex.minus (finiteFilteredModules J R))) :=
  fun K => IsSplitFlatFiltered (J := J) R K.as.obj

/-- The canonical localization functor induced by the split-flat inclusion.
This is the localization lift of the inclusion of actual filtered homotopy
categories, at graded quasi-isomorphisms on both sides. -/
def finiteFilteredLocalizationComparison (a b : ℤ) :
    ((uniformFilteredHomotopyQuasiIso (some (a, b))
      (CochainComplex.minus (finiteFilteredModules J R))).inverseImage
        (finiteFilteredSplitFlatProperty (J := J) R a b).ι).Localization ⥤
    (uniformFilteredHomotopyQuasiIso (some (a, b))
      (CochainComplex.minus (finiteFilteredModules J R))).Localization :=
  Localization.Construction.lift
    ((finiteFilteredSplitFlatProperty (J := J) R a b).ι ⋙
      (uniformFilteredHomotopyQuasiIso (some (a, b))
        (CochainComplex.minus (finiteFilteredModules J R))).Q)
    (fun _ _ f hf =>
      (uniformFilteredHomotopyQuasiIso (some (a, b))
        (CochainComplex.minus (finiteFilteredModules J R))).Q_inverts
        ((finiteFilteredSplitFlatProperty (J := J) R a b).ι.map f) hf)

/-- The sum of the images defining the convolution filtration at weight `r`.
The image of the coproduct map is the sum of the images. Indexing by `p`
with second index `r-p` is exactly the condition `p+q=r`. -/
def finiteFilteredConvolutionStep
    (P Q : WeilFilteredObject (finiteFilteredComplex J R)) (r : ℤ) :
    Subobject (HomologicalComplex.tensorObj P.obj Q.obj) :=
  imageSubobject (Sigma.desc (fun p : ℤ =>
    HomologicalComplex.tensorHom (P.filtration.F p).arrow
      (Q.filtration.F (r - p)).arrow))

/--
Every bounded-above fixed-interval filtered complex admits a split-flat model,
the corresponding localized filtered homotopy categories are equivalent, and
ordinary total tensor with the model preserves graded quasi-isomorphisms for any
uniformly finite filtration on the right. -/
theorem finiteFilteredFlatModel
    (a b : ℤ) (hab : a ≤ b)
    (M : UniformFilteredComplexes (finiteFilteredModules J R) (some (a, b))
      (CochainComplex.minus (finiteFilteredModules J R))) :
    (∃ K : UniformFilteredComplexes (finiteFilteredModules J R) (some (a, b))
        (CochainComplex.minus (finiteFilteredModules J R)),
      IsSplitFlatFiltered (J := J) R K.obj ∧
      ∃ f : K.obj ⟶ M.obj,
        (∀ p : ℤ, QuasiIso (WeilFilteredObject.gradedMapSteps f p))) ∧
    (finiteFilteredLocalizationComparison (J := J) R a b).IsEquivalence ∧
    (∀ (P : UniformFilteredComplexes (finiteFilteredModules J R) (some (a, b))
          (CochainComplex.minus (finiteFilteredModules J R))),
      IsSplitFlatFiltered (J := J) R P.obj →
      ∀ {Q Q' : WeilFilteredObject (finiteFilteredComplex J R)},
        Q.filtration.IsFinite → Q'.filtration.IsFinite →
        ∀ g : Q ⟶ Q',
          (∀ p : ℤ, QuasiIso (WeilFilteredObject.gradedMapSteps g p)) →
          ∃ (FT : DecreasingFiltration (HomologicalComplex.tensorObj P.obj.obj Q.obj))
            (FT' : DecreasingFiltration (HomologicalComplex.tensorObj P.obj.obj Q'.obj))
            (t : (⟨HomologicalComplex.tensorObj P.obj.obj Q.obj, FT⟩ :
                WeilFilteredObject (finiteFilteredComplex J R)) ⟶
              ⟨HomologicalComplex.tensorObj P.obj.obj Q'.obj, FT'⟩),
            (∀ r : ℤ, FT.F r = finiteFilteredConvolutionStep (J := J) R P.obj Q r) ∧
            (∀ r : ℤ, FT'.F r = finiteFilteredConvolutionStep (J := J) R P.obj Q' r) ∧
            FT.IsFinite ∧ FT'.IsFinite ∧
            t.hom = HomologicalComplex.tensorHom (𝟙 P.obj.obj) g.hom ∧
            (∀ r : ℤ, QuasiIso (WeilFilteredObject.gradedMapSteps t r))) := by
  sorry

end CategoryTheory
