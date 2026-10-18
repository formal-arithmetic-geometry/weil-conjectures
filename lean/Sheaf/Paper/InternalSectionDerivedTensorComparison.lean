/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.InternalSectionTotalComparison

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Normalized internal-to-sectionwise derived tensor comparison

Source: Stacks Project, Tags 08J9, 08JA and 08JB; blueprint module objects and
derived tensor--Hom (blueprint: def-sfb-internal-section-derived-tensor-comparison).

## Main definitions

* `TensorComparison`: the canonical tensor comparison, normalized on K-flat models.
* `totalComparison`: the fixed comparison of the concrete sum-total complexes.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

/-- The representative localization square, abstracted over its four categories
and functors. This is the same equation used by the concrete K-flat normalizations;
abstracting the endpoints avoids unfolding coefficient transport during elaboration.
Source: Stacks 06YS, 08J9
(blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def tensorLocalizationSquare
    {C₀ : Type u₀} [Category.{v₀} C₀] {D₀ : Type u₁} [Category.{v₁} D₀]
    {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
    (qC : C₀ ⥤ C) (qD : D₀ ⥤ D) (f₀ : C₀ ⥤ D₀) (f : C ⥤ D)
    (factor : qC ⋙ f ≅ f₀ ⋙ qD)
    (t : C × C ⥤ C) (t₀ : C₀ × C₀ ⥤ C₀)
    (s : D × D ⥤ D) (s₀ : D₀ × D₀ ⥤ D₀)
    (μ : ∀ P Q : C₀, t.obj (qC.obj P, qC.obj Q) ⟶ qC.obj (t₀.obj (P, Q)))
    (c : ∀ P Q : C₀, f₀.obj (t₀.obj (P, Q)) ≅ s₀.obj (f₀.obj P, f₀.obj Q))
    (flat : D₀ → Prop)
    (model : ∀ (P Q : D₀), flat P → flat Q →
      (qD.obj (s₀.obj (P, Q)) ≅ s.obj (qD.obj P, qD.obj Q)))
    (iso : t ⋙ f ≅ (f.prod f) ⋙ s) : Prop :=
  ∀ (P Q : C₀) (hP : flat (f₀.obj P)) (hQ : flat (f₀.obj Q)),
    iso.hom.app (qC.obj P, qC.obj Q) ≫
      s.map (X := (f.obj (qC.obj P), f.obj (qC.obj Q)))
        (Y := (qD.obj (f₀.obj P), qD.obj (f₀.obj Q)))
        (factor.hom.app P, factor.hom.app Q) =
      f.map (μ P Q) ≫ factor.hom.app (t₀.obj (P, Q)) ≫
        qD.map (c P Q).hom ≫ (model (f₀.obj P) (f₀.obj Q) hP hQ).hom

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- The fixed comparison on the concrete native total complexes. The preceding
unique characterization determines its data, including every summand map.
Source: Stacks 03EK, 06YL
(blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def totalComparison (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj (internalTotalTensor Λ X P Q) ≅
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
      ((complexForward Λ X).obj P, (complexForward Λ X).obj Q) :=
  (totalComparison_existsUnique Λ X P Q).choose

/-- The representative-normalization predicate for a derived tensor comparison.
Separating this predicate keeps structure projections from expanding the concrete
localization and total-complex implementations.
Source: Stacks 06YS, 08J9
(blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def tensorComparisonNormalized
    (S : CoefficientClosedStructure (hom Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) S)
    (iso : Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ forward Λ X ≅
    ((forward Λ X).prod (forward Λ X)) ⋙ S.tensor) : Prop :=
  ∀ (P Q : CochainComplex (Internal Λ X) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology X) (R := ring Λ X) ((complexForward Λ X).obj P))
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology X) (R := ring Λ X) ((complexForward Λ X).obj Q)),
    HEq (iso.hom.app ((DerivedCategory.Q (C := Internal Λ X)).obj P,
        (DerivedCategory.Q (C := Internal Λ X)).obj Q) ≫
        S.tensor.map
          (X := ((forward Λ X).obj ((DerivedCategory.Q (C := Internal Λ X)).obj P),
            (forward Λ X).obj ((DerivedCategory.Q (C := Internal Λ X)).obj Q)))
          (Y := ((DerivedCategory.Q (C := Modules Λ X)).obj ((complexForward Λ X).obj P),
            (DerivedCategory.Q (C := Modules Λ X)).obj ((complexForward Λ X).obj Q)))
          ((localizationIso Λ X).hom.app P, (localizationIso Λ X).hom.app Q))
      ((forward Λ X).map (localizationTensorMap Λ X P Q) ≫
        (localizationIso Λ X).hom.app (internalTotalTensor Λ X P Q) ≫
        (DerivedCategory.Q (C := Modules Λ X)).map (totalComparison Λ X P Q).hom ≫
        (CoefficientTensorModels.iso (Scheme.ProEt.topology X) (ring Λ X) S T
          ((complexForward Λ X).obj P) ((complexForward Λ X).obj Q) hP hQ).hom)

/-- Tensor comparison with the fixed K-flat localization normalization.
The complex comparison is the dependency's canonical comparison, not extra data.
K-flatness is tested on the images under the exact equivalence; preservation and
reflection in lem-pe-internal-section-tensor-comparison identify this with the
internal K-flat test, so it restricts only representatives and not derived inputs.
Source: Stacks 06YS, 08J9 (blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
structure TensorComparison
    (S : CoefficientClosedStructure (hom Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) S) where
  /-- Natural comparison on derived tensor products. -/
  iso : Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ forward Λ X ≅
    ((forward Λ X).prod (forward Λ X)) ⋙ S.tensor
  /-- Agreement with the canonical ordinary total comparison on K-flat models. -/
  normalization : tensorComparisonNormalized Λ X S T iso

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
