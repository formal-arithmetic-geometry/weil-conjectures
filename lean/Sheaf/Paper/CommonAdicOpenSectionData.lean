/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.CommonAdicSectionData

/-! # Common-stage adic open extension comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-common-adic-open-section-data).

## Main definitions

- `CommonOpen`: normalized common-stage open extension comparison diagrams.
- `commonRestrictionHom`: restriction through the inverse open unit.
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
/-- The actual common-stage completed pullback, without a universe equality.
Source: BS 6.8.15 (blueprint: def-a1-common-adic-open-section-data). -/
def commonPull {U T : Geometry D} (j : U.scheme ⟶ T.scheme) :=
  letI := smoothQbarResidueInvertible D l hl U.scheme
  letI := smoothQbarResidueInvertible D l hl T.scheme
  commonStageDerivedPullback l Ω j

attribute [-instance] FiniteFieldDatum.CoefficientDatum.prime
  FiniteFieldDatum.CoefficientDatum.field FiniteFieldDatum.CoefficientDatum.algebra
  FiniteFieldDatum.CoefficientDatum.isAlgClosure in
/-- Common-stage open extension: actual normalized compact support on every arrow,
exactness, the open unit, stage comparisons, and the recorded adic fibres.
Source: BS 6.8.14--6.8.15; Stacks 09AG, 09BN
(blueprint: def-a1-common-adic-open-section-data). -/
structure CommonOpen {F : FiniteFamily D l hl} {U T : Geometry D}
    (AU : CommonAt D l hl Ω F U) (AT : CommonAt D l hl Ω F T)
    (j : U.scheme ⟶ T.scheme) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] where
  action : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl)
    Ω (Compactification.ofIsOpenImmersion j)
  shriek : sfCommonStageHeart l U.scheme Ω ⥤ sfCommonStageHeart l T.scheme Ω
  [additive : shriek.Additive]
  [linear : shriek.Linear Ω]
  [limits : PreservesFiniteLimits shriek]
  [colimits : PreservesFiniteColimits shriek]
  tower : shriek ⋙ (sfCommonStageHeartProperty l T.scheme Ω).ι ≅
    (sfCommonStageHeartProperty l U.scheme Ω).ι ⋙ action.system.functor
  restriction : sfCommonStageHeart l T.scheme Ω ⥤ sfCommonStageHeart l U.scheme Ω
  pullback : restriction ⋙ (sfCommonStageHeartProperty l U.scheme Ω).ι ≅
    (sfCommonStageHeartProperty l T.scheme Ω).ι ⋙ commonPull D l hl Ω j
  adjunction : shriek ⊣ restriction
  [open_unit : IsIso adjunction.unit]
  unit : restriction.obj AT.unit ≅ AU.unit
  extension_stage : ∀ N : Padic.FiniteCoefficientFields l Ω,
    (F.openImage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).shriek ⋙
      AT.inclusion N ≅ AU.inclusion N ⋙ shriek
  restriction_stage : ∀ N : Padic.FiniteCoefficientFields l Ω,
    (F.openImage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).restriction ⋙
      AU.inclusion N ≅ AT.inclusion N ⋙ restriction
  unit_stage : ∀ N : Padic.FiniteCoefficientFields l Ω,
    (AU.inclusion N).map
        (F.openImage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).unit.hom ≫
          (AU.unit_stage N).hom =
      (restriction_stage N).hom.app
          (F.atScheme (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) T).unit ≫
        restriction.map (AT.unit_stage N).hom ≫ unit.hom
  adjunction_stage : ∀ (N : Padic.FiniteCoefficientFields l Ω)
    (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) U.scheme),
    (AU.inclusion N).map
        ((F.openImage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N)
          j).adjunction.unit.app M) ≫
        (restriction_stage N).hom.app
          ((F.openImage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N) j).shriek.obj M) ≫
        restriction.map ((extension_stage N).hom.app M) =
      adjunction.unit.app ((AU.inclusion N).obj M)
  ordinary_restriction : AT.ordinary ⟶ restriction ⋙ AU.ordinary
  ordinary_restriction_hom : ∀ (M : sfCommonStageHeart l T.scheme Ω) (x : AT.ordinary.obj M),
    AU.hom (restriction.obj M) (ordinary_restriction.app M x) =
      unit.inv ≫ restriction.map (AT.hom M x)
  inside : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ U.scheme)
    (FU : generalAlgebraicallyClosedConstructibleCategory l Ω U.scheme ⥤
      ModuleCat.{max (u + 1) v} Ω)
    (FT : generalAlgebraicallyClosedConstructibleCategory l Ω T.scheme
      ⥤ ModuleCat.{max (u + 1) v} Ω),
    SfAdicCommonFiberSpec l U.scheme x Ω FU → SfAdicCommonFiberSpec l T.scheme (x ≫ j) Ω FT →
      Nonempty (shriek ⋙ (sfCommonStageHeartProperty l T.scheme Ω).ι ⋙ FT ≅
        (sfCommonStageHeartProperty l U.scheme Ω).ι ⋙ FU)
  outside : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T.scheme)
    (FT : generalAlgebraicallyClosedConstructibleCategory l Ω T.scheme ⥤
      ModuleCat.{max (u + 1) v} Ω), SfAdicCommonFiberSpec l T.scheme x Ω FT →
    Set.range x.base ⊆ (Set.range j.base)ᶜ →
      ∀ M : sfCommonStageHeart l U.scheme Ω, IsZero (FT.obj (shriek.obj M).obj)

attribute [instance] CommonOpen.additive CommonOpen.linear CommonOpen.limits CommonOpen.colimits
  CommonOpen.open_unit

attribute [-instance] FiniteFieldDatum.CoefficientDatum.prime
  FiniteFieldDatum.CoefficientDatum.field FiniteFieldDatum.CoefficientDatum.algebra
  FiniteFieldDatum.CoefficientDatum.isAlgClosure in
/-- Common-stage restriction of a coefficient-unit morphism, through the actual
open-unit inverse. Source: Milne 18.3(b)
(blueprint: def-a1-common-adic-open-section-data). -/
def commonRestrictionHom {F : FiniteFamily D l hl} {U T : Geometry D}
    {AU : CommonAt D l hl Ω F U} {AT : CommonAt D l hl Ω F T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : CommonOpen D l hl Ω AU AT j)
    (M : sfCommonStageHeart l U.scheme Ω) (t : AT.unit ⟶ O.shriek.obj M) : AU.unit ⟶ M :=
  O.unit.inv ≫ O.restriction.map t ≫ (asIso (O.adjunction.unit.app M)).inv

end WeilConjectures.AdicCompactificationSections
