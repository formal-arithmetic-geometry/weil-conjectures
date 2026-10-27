/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.CommonAdicOpenSectionData

/-! # Common-stage adic compactification and section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-common-adic-compactification-section-data).

## Main definitions

- `CommonProper`: common-stage compactification comparison diagrams.
- `CommonFamily`: simultaneous common-stage data over one finite family.
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
/-- Proper common-stage compactification sections, normalized on every finite-stage
object and morphism. Scalar extension of the finite Hom formula fixes the Ω formula.
Source: BS 6.8.14; Milne 18.1, 18.3(b)
(blueprint: def-a1-common-adic-compactification-section-data). -/
structure CommonProper {F : FiniteFamily D l hl} {U T : Geometry D}
    {AU : CommonAt D l hl Ω F U} {AT : CommonAt D l hl Ω F T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : CommonOpen D l hl Ω AU AT j)
    [IsProper (T.scheme ↘ Spec (.of D.k))] where
  compact : sfCommonStageHeart l U.scheme Ω ⥤ ModuleCat.{max u v} Ω
  compact_obj : ∀ M, compact.obj M =
    adicCompactCohomology D l hl U.scheme Ω
      (AdicCompactificationSections.compactification D j) M.obj 0
  hom : ∀ M, (compact.obj M : Type (max u v)) ≃ₗ[Ω] (AT.unit ⟶ O.shriek.obj M)
  natural : ∀ (M N : sfCommonStageHeart l U.scheme Ω) (f : M ⟶ N) (x : compact.obj M),
    hom N (compact.map f x) = hom M x ≫ O.shriek.map f
  comparison : compact ⟶ AU.ordinary
  comparison_canonical : ∀ (M : sfCommonStageHeart l U.scheme Ω) (x : compact.obj M),
    AU.hom M (comparison.app M x) = commonRestrictionHom D l hl Ω O M (hom M x)
  compactification : compact ≅ O.shriek ⋙ AT.ordinary
  compactification_hom : ∀ (M : sfCommonStageHeart l U.scheme Ω) (x : compact.obj M),
    AT.hom (O.shriek.obj M) (compactification.hom.app M x) = hom M x
  compact_stage : ∀ N : Padic.FiniteCoefficientFields l Ω,
    (F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).compact ⋙
      ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω N) ≅
        AU.inclusion N ⋙ compact
  compact_stage_normalized : ∀ (N : Padic.FiniteCoefficientFields l Ω)
    (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) U.scheme)
    (x : (F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).compact.obj M),
    (eqToIso (compact_obj ((AU.inclusion N).obj M))).hom
        ((compact_stage N).hom.app M (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N) x)) =
      (eqToIso (congrArg
        (fun K : generalAlgebraicallyClosedConstructibleCategory l Ω U.scheme ↦
          adicCompactCohomology D l hl U.scheme Ω
            (AdicCompactificationSections.compactification D j) K 0)
        (AU.inclusion_obj N M))).inv
        (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N)
          ((eqToIso ((F.proper
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).compact_obj M)).hom x))
  hom_stage : ∀ (N : Padic.FiniteCoefficientFields l Ω)
    (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) U.scheme)
    (x : (F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).compact.obj M),
    hom ((AU.inclusion N).obj M)
        ((compact_stage N).hom.app M (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N) x)) =
      (AT.unit_stage N).inv ≫ (AT.inclusion N).map
        ((F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).hom M x) ≫
        (O.extension_stage N).hom.app M
  compactification_stage : ∀ (N : Padic.FiniteCoefficientFields l Ω)
    (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) U.scheme)
    (x : (F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).compact.obj M),
    compactification.hom.app ((AU.inclusion N).obj M)
        ((compact_stage N).hom.app M (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N) x)) =
      AT.ordinary.map ((O.extension_stage N).hom.app M)
        ((AT.ordinary_stage N).hom.app
          ((F.openImage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).shriek.obj M)
          (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N)
            ((FiniteProper.compactification
            (F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j)).hom.app M x)))
  comparison_stage : ∀ (N : Padic.FiniteCoefficientFields l Ω)
    (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) U.scheme)
    (x : (F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).compact.obj M),
    comparison.app ((AU.inclusion N).obj M)
        ((compact_stage N).hom.app M (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N) x)) =
      (AU.ordinary_stage N).hom.app M (scalarUnit (sfAdicCoefficientEmbedding.{u} l Ω N)
        ((F.proper (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).comparison.app M x))


attribute [-instance] FiniteFieldDatum.CoefficientDatum.prime
  FiniteFieldDatum.CoefficientDatum.field FiniteFieldDatum.CoefficientDatum.algebra
  FiniteFieldDatum.CoefficientDatum.isAlgClosure in
/-- Simultaneous common-stage sections and open images, above the same finite-stage
family. Natural comparisons on functors include every represented arrow, inverse and
composition, not only objects coming from one selected field.
Source: BS 6.8.14(1),(2), Remark 6.8.15
(blueprint: def-a1-common-adic-compactification-section-data). -/
structure CommonFamily (F : FiniteFamily D l hl) where
  atScheme : ∀ W : Geometry D, CommonAt D l hl Ω F W
  openImage : ∀ {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))],
    CommonOpen D l hl Ω (atScheme U) (atScheme T) j
  proper : ∀ {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))], CommonProper D l hl Ω (openImage j)

end WeilConjectures.AdicCompactificationSections
