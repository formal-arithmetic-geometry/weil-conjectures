/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FiniteAdicCompactificationSectionData

/-! # Common-stage adic ordinary section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-common-adic-section-data).

## Main definitions

- `CommonAt`: the common-stage coefficient unit and normalized ordinary sections.
- `commonLinear`: the existing scalar action transported to Ω.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicCompactificationSections
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [-instance] FiniteFieldDatum.CoefficientDatum.prime
  FiniteFieldDatum.CoefficientDatum.field FiniteFieldDatum.CoefficientDatum.algebra
  FiniteFieldDatum.CoefficientDatum.isAlgClosure in
/-- Cache the recorded finite-stage category at its literal rational presentation.
This is the existing category structure, without changing objects or morphisms.
Source: BS 6.8.14(2), common-stage conventions
(blueprint: def-a1-common-adic-section-data). -/
instance finiteStageCategory (W : Scheme.{u}) (N : Padic.FiniteCoefficientFields l Ω) :
    Category (sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W) :=
  GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω W N

attribute [-instance] FiniteFieldDatum.CoefficientDatum.prime
  FiniteFieldDatum.CoefficientDatum.field FiniteFieldDatum.CoefficientDatum.algebra
  FiniteFieldDatum.CoefficientDatum.isAlgClosure in
/-- Cache the existing full finite-stage heart category for the same coefficient model.
Source: blueprint constructible-heart convention
(blueprint: def-a1-common-adic-section-data). -/
instance finiteStageHeartCategory (W : Scheme.{u}) (N : Padic.FiniteCoefficientFields l Ω) :
    Category (sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W) :=
  CategoryTheory.ObjectProperty.FullSubcategory.category _

attribute [-instance] FiniteFieldDatum.CoefficientDatum.prime
  FiniteFieldDatum.CoefficientDatum.field FiniteFieldDatum.CoefficientDatum.algebra
  FiniteFieldDatum.CoefficientDatum.isAlgClosure in
/-- The actual Ω-linear action on common-stage morphisms, transported from the
unique finite-representative action along the recorded coefficient-size equivalence.
The full constructible heart inherits this same action.
Source: BS 6.8.14(2), common-stage scalar convention
(blueprint: def-a1-common-adic-section-data). -/
instance commonLinear (W : Scheme.{u}) :
    Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  Linear.ofRingMorphism
    ((Linear.toCatCenter (R := OrdinaryFieldRealization.Closure.{u} l Ω)
      (generalAlgebraicallyClosedConstructibleCategory l Ω W)).comp
        (OrdinaryFieldRealization.closureEquiv.{u} l Ω).symm.toRingHom)

attribute [-instance] FiniteFieldDatum.CoefficientDatum.prime
  FiniteFieldDatum.CoefficientDatum.field FiniteFieldDatum.CoefficientDatum.algebra
  FiniteFieldDatum.CoefficientDatum.isAlgClosure in
/-- Ordinary Ω-sections and their finite-stage normalization. The domain is the
actual common-stage heart, hence includes all common-stage objects and arrows.
Source: BS 6.8.14(1),(2); Milne 18.1
(blueprint: def-a1-common-adic-section-data). -/
structure CommonAt (F : FiniteFamily D l hl) (W : Geometry D) where
  unit : sfCommonStageHeart l W.scheme Ω
  inclusion : ∀ N : Padic.FiniteCoefficientFields l Ω,
    sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W.scheme ⥤
      sfCommonStageHeart l W.scheme Ω
  underlying : ∀ N : Padic.FiniteCoefficientFields l Ω,
    inclusion N ⋙ (sfCommonStageHeartProperty l W.scheme Ω).ι ≅
      (sfRationalHeartProperty l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W.scheme).ι ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion N
  inclusion_obj : ∀ (N : Padic.FiniteCoefficientFields l Ω)
      (M : sfRationalHeart l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W.scheme),
    ((inclusion N).obj M).obj = (GeneralAlgebraicallyClosedCoefficients.inclusion N).obj M.obj
  underlying_normalized : ∀ (N : Padic.FiniteCoefficientFields l Ω)
      (M : sfRationalHeart l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W.scheme),
    (underlying N).hom.app M = eqToHom (inclusion_obj N M)
  unit_stage : ∀ N : Padic.FiniteCoefficientFields l Ω,
    (inclusion N).obj (F.atScheme (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W).unit ≅
      unit
  ordinary : sfCommonStageHeart l W.scheme Ω ⥤ ModuleCat.{max u v} Ω
  ordinary_obj : ∀ M, ordinary.obj M = adicOrdinaryCohomology D l hl W.scheme Ω M.obj 0
  hom : ∀ M, (ordinary.obj M : Type (max u v)) ≃ₗ[Ω] (unit ⟶ M)
  natural : ∀ (M N : sfCommonStageHeart l W.scheme Ω) (f : M ⟶ N) (x : ordinary.obj M),
    hom N (ordinary.map f x) = hom M x ≫ f
  ordinary_stage : ∀ N : Padic.FiniteCoefficientFields l Ω,
    (F.atScheme (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W).ordinary ⋙
      ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω N) ≅
        inclusion N ⋙ ordinary
  ordinary_stage_normalized : ∀ (N : Padic.FiniteCoefficientFields l Ω)
    (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W.scheme)
    (x : (F.atScheme (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W).ordinary.obj M),
    (eqToIso (ordinary_obj ((inclusion N).obj M))).hom
        ((ordinary_stage N).hom.app M (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N) x)) =
      (eqToIso (congrArg
        (fun K : generalAlgebraicallyClosedConstructibleCategory l Ω W.scheme ↦
          adicOrdinaryCohomology D l hl W.scheme Ω K 0) (inclusion_obj N M))).inv
        (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N)
          ((eqToIso ((F.atScheme
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W).ordinary_obj M)).hom x))
  hom_stage : ∀ (N : Padic.FiniteCoefficientFields l Ω)
    (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W.scheme)
    (x : (F.atScheme (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W).ordinary.obj M),
    hom ((inclusion N).obj M)
        ((ordinary_stage N).hom.app M (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N) x)) =
      (unit_stage N).inv ≫ (inclusion N).map
        ((F.atScheme (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) W).ordinary_hom M x)


end WeilConjectures.AdicCompactificationSections
