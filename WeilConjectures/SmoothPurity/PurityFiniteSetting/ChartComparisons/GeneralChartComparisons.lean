/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChartFactors.ChartDncVectorFactorData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage

/-! # Canonical comparisons between successive smooth etale charts

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Steps 1--4, and composition coherence Step 1.
(blueprint: def-pur-general-chart-comparisons).

The geometric and section comparisons are the published orientation-free constructions.
The chart interface names their values and the counit-normalized exceptional comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- Published canonical source; this is an alias, with no second construction.
Source: orientation charts Steps 1--4 (blueprint: def-pur-general-chart-comparisons). -/
abbrev source := @DiagonalEtaleComparison.source.{u}

/-- Published canonical normal; this is an alias, with no second construction.
Source: orientation charts Steps 1--4 (blueprint: def-pur-general-chart-comparisons). -/
abbrev normal := @DiagonalEtaleComparison.normal.{u}

/-- The actual finite exceptional value of the coefficient unit.
Source: orientation charts Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def omega (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := Dnc.compactifiable P g aY
  P.diagonalDualizing g

/-- Inverse counit-normalized etale locality, with every site comparison retained.
Source: orientation charts Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def epsilon (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aY
  letI := P.noetherian (g ≫ aY)
  letI := P.noetherian ((e ≫ g) ≫ aY)
  letI := Dnc.compactifiable P g aY
  letI := Dnc.compactifiable P (e ≫ g) aY
  P.diagonalDualizingComparison (e ≫ g) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.diagonalEtaleLocality N e g).symm ≪≫
    (Dnc.pullComparison P e (P.diagonalOrdinaryDualizing g)).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison g).symm

/-- The counit-preserving etale exceptional identification at the actual omega value.
Source: orientation charts Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def rho (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aY
  letI := P.noetherian (g ≫ aY)
  letI := P.noetherian ((e ≫ g) ≫ aY)
  letI := Dnc.compactifiable P g aY
  letI := Dnc.compactifiable P e (g ≫ aY)
  (ProEtale.rightDerivedUpperShriek P.Coefficient e).mapIso
      (P.diagonalDualizingComparison g) ≪≫
    P.chartEtaleIdentification e N (P.diagonalOrdinaryDualizing g)
      (Etale.plus_rightDerivedUpperShriek_obj P.Coefficient g _ (P.diagonalUnitPlus Y)) ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison g).symm

/-- Precisely the standing exceptional composition morphism on the coefficient unit.
Source: composition coherence Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def composition (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e] :=
  letI : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨g ≫ aY⟩
  letI : U.Over (Spec (.of P.field.k)) := ⟨e ≫ (g ≫ aY)⟩
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType aY)
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aY)
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (g ≫ aY))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (g ≫ aY))
  letI : LocallyOfFiniteType (U ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (e ≫ (g ≫ aY)))
  letI : QuasiCompact (U ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (e ≫ (g ≫ aY)))
  letI : e.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  ProEtale.standingExceptionalComposition P e g (P.chartCoefficientUnit Y)

/-- An affine smooth d-chart has only its etale coordinates, with no orientation.
Source: orientation charts Step 1 (blueprint: def-pur-general-chart-comparisons). -/
structure Chart (V : Scheme.{u}) (d : ℕ) where
  X : Scheme.{u}
  affine : IsAffine X
  coord : X ⟶ AffineSpace (ULift.{u} (Fin d)) V
  etale : Etale coord

attribute [instance] Chart.affine Chart.etale

/-- Projection of an etale coordinate chart.
Source: orientation charts Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def Chart.proj {V : Scheme.{u}} {d : ℕ} (C : Chart V d) : C.X ⟶ V :=
  C.coord ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V)

/-- Composition with an etale coordinate map preserves the pure relative dimension.
Source: orientation charts Step 1 (blueprint: def-pur-general-chart-comparisons).
Proof: the coordinate map is smooth of dimension zero and the standard projection is
smooth of dimension d; the composition has dimension 0+d=d, including d=0. -/
theorem Chart.smooth {V : Scheme.{u}} {d : ℕ} (C : Chart V d) :
    SmoothOfRelativeDimension d C.proj := by
  have : SmoothOfRelativeDimension 0 C.coord :=
    (Etale.iff_smoothOfRelativeDimension_zero C.coord).mp C.etale
  have : SmoothOfRelativeDimension d (AffineSpace (ULift.{u} (Fin d)) V ↘ V) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) V
  simpa only [Chart.proj, Nat.zero_add] using
    (smoothOfRelativeDimension_comp 0 d C.coord
      (AffineSpace (ULift.{u} (Fin d)) V ↘ V))

attribute [instance] Chart.smooth

/-- Chart projections are locally of finite type, as compositions of such maps.
Source: orientation charts Step 1 (blueprint: def-pur-general-chart-comparisons).
Proof: the etale coordinate map and affine-space projection are locally of finite type;
composition preserves local finite type. -/
theorem Chart.locallyOfFiniteType {V : Scheme.{u}} {d : ℕ} (C : Chart V d) :
    LocallyOfFiniteType C.proj := by
  unfold Chart.proj
  infer_instance

attribute [instance] Chart.locallyOfFiniteType

/-- An etale chart map is a map of its affine sources over V.
Source: composition coherence Step 1 (blueprint: def-pur-general-chart-comparisons). -/
structure Map {V : Scheme.{u}} {d : ℕ} (C B : Chart V d) where
  hom : C.X ⟶ B.X
  etale : Etale hom
  over_eq : hom ≫ B.proj = C.proj

attribute [instance] Map.etale

/-- Identity chart map, using the scheme identity.
Source: composition coherence Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def Map.id {V : Scheme.{u}} {d : ℕ} (C : Chart V d) : Map C C where
  hom := 𝟙 C.X
  etale := inferInstance
  over_eq := Category.id_comp _

/-- Composition is the actual composition of scheme morphisms.
Source: composition coherence Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def Map.comp {V : Scheme.{u}} {d : ℕ} {C B A : Chart V d}
    (v : Map C B) (e : Map B A) : Map C A where
  hom := v.hom ≫ e.hom
  etale := inferInstance
  over_eq := (Category.assoc _ _ _).trans
    ((congrArg (v.hom ≫ ·) e.over_eq).trans v.over_eq)

/-- The standard affine chart with identity coordinates.
Source: orientation charts Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def standard (V : Scheme.{u}) [IsAffine V] (d : ℕ) : Chart V d where
  X := AffineSpace (ULift.{u} (Fin d)) V
  affine := inferInstance
  coord := 𝟙 _
  etale := inferInstance

/-- The specified coordinate map to the standard chart.
Source: orientation charts Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def coordinate {V : Scheme.{u}} [IsAffine V] {d : ℕ} (C : Chart V d) :
    Map C (standard V d) where
  hom := C.coord
  etale := C.etale
  over_eq := rfl

/-- The canonical diagonal base-change identification, including coefficient units.
Source: orientation charts Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def alpha (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) :=
  P.chartDiagonalAlpha d C.proj aV

/-- The canonical source comparison for an arbitrary successive etale chart map.
Source: orientation charts Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def q (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  source P d B.proj C.proj aV e.hom e.over_eq N

/-- The canonical normal comparison for the actual zero-fibre normal square.
Source: orientation charts Steps 2--3 (blueprint: def-pur-general-chart-comparisons). -/
def r (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B) :=
  normal P d B.proj C.proj aV e.hom e.over_eq

end WeilConjectures.PurityFiniteSetting.ChartComparisons
