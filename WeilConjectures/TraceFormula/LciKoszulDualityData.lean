/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.AlgebraicGeometry.LciCotangentPresentation
public import WeilConjectures.TraceFormula.TwoTermPerfectDeterminant
public import WeilConjectures.AlgebraicGeometry.RelativeDualityPolynomialChart
public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom

/-! # Normalized Koszul duality and the cotangent determinant

Source: Stacks, duality.tex, Tags 0BQZ and 0BV2; dualizing.tex, Tags 0BZI and 0BZJ;
more-algebra.tex, Tags 0FJI and 0FJM
(blueprint: def-trf-lci-koszul-duality-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Algebra.CotangentResolution AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.LciKoszulDuality

variable [∀ Z : RingedSpace.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The existing localization or K-injective instance through the canonical ring-sheaf
identification. Source: Stacks 05RU, 079V
(blueprint: def-trf-lci-koszul-duality-data). -/
local instance schemeDerived (Z : Scheme.{u}) : HasDerivedCategory.{w} Z.Modules :=
  inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))

/-- The existing localization or K-injective instance through the canonical ring-sheaf
identification. Source: Stacks 05RU, 079V
(blueprint: def-trf-lci-koszul-duality-data). -/
local instance imageRingDerived {U P : Scheme.{u}} (i : U ⟶ P) :
    HasDerivedCategory.{w} (SheafOfModules.{u}
      (((TopologicalSpace.Opens.map i.base).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology P) (Opens.grothendieckTopology U)).obj U.ringCatSheaf)) :=
  inferInstanceAs (HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))

/-- The existing localization or K-injective instance through the canonical ring-sheaf
identification. Source: Stacks 05RU, 079V
(blueprint: def-trf-lci-koszul-duality-data). -/
local instance imageRingInjectives {U P : Scheme.{u}} (i : U ⟶ P) :
    Abelian.HasKInjectiveResolutions (SheafOfModules.{u}
      (((TopologicalSpace.Opens.map i.base).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology P) (Opens.grothendieckTopology U)).obj U.ringCatSheaf)) :=
  inferInstanceAs (Abelian.HasKInjectiveResolutions
    (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))

/-- The charts in the assertion, with precisely c equations and n=c+d coordinates.
The rank condition is on the actual conormal module, including rank zero.
Source: Stacks 0BQZ, 0BV2
(blueprint: def-trf-lci-koszul-duality-data). -/
structure Chart {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) where
  chart : RelativeDualityPolynomialChart f
  c : ℕ
  dimension : chart.n = c + d
  regular : ∀ x : chart.U.toScheme, ∃ W : chart.P.affineOpens, chart.i x ∈ W.1 ∧
    ∃ g : Fin c → Γ(chart.P, W.1),
      RingTheory.Sequence.IsKoszulRegular g ∧ Ideal.span (Set.range g) = chart.i.ker.ideal W
  conormal_free : (CotangentPresentation.conormalTerm chart.i).IsFiniteLocallyFreeOfRank c

/-- The displayed line D_i, using the existing exterior sheaf and sheaf dual.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.line {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :
    T.chart.U.toScheme.Modules :=
  dual (exteriorSheaf (CotangentPresentation.conormalTerm T.chart.i) T.c) ⊗
    exteriorSheaf (CotangentPresentation.ambientDifferentials T.chart.i T.chart.base) T.chart.n

/-- The ambient top differential line, before the polynomial shift.
Source: Stacks 0BZI (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.omega {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :
    T.chart.P.Modules := exteriorSheaf T.chart.base.relativeDifferentials T.chart.n

/-- The actual evaluation pairing C_top tensor D_i -> V_top; dual first in D_i.
Source: Stacks 0BQZ, 0FJI
(blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.pairing {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :
    exteriorSheaf (CotangentPresentation.conormalTerm T.chart.i) T.c ⊗ T.line ⟶
      exteriorSheaf (CotangentPresentation.ambientDifferentials T.chart.i T.chart.base)
        T.chart.n :=
  (α_ _ _ _).inv ≫ (dualEvaluation _ ▷ _) ≫ (λ_ _).hom

/-- Forget the closed-source algebra action by the existing exact scalar restriction.
Source: Stacks 0BUZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.scalars {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :=
  SheafOfModules.restrictScalars.{u} T.chart.i.toRingCatSheafHom

/-- The actual direct image into the direct-image algebra ringed space.
Source: Stacks 0AVW (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.image {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :=
  RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace T.chart.i)

/-- The target after the polynomial shift is i_*D_i[d], retaining its algebra action.
Source: Stacks 0BQZ, 0BZI
(blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.target {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :=
  T.image.obj (((DerivedCategory.singleFunctor _ 0).obj T.line)⟦(d : ℤ)⟧)

/-- A polynomial chart is also exactly the conormal presentation already recorded upstream.
Source: Stacks 08SL (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.presentation {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :
    CotangentPresentation.LciPresentation T.chart.i T.chart.base where
  dimension := T.chart.n
  ambient := T.chart.ambient
  closed := T.chart.closed
  open_immersion := T.chart.ambient_open
  structure_map := rfl
  koszul := fun x ↦ by
    obtain ⟨W, hx, g, hg, hI⟩ := T.regular x
    exact ⟨W, hx, T.c, g, hg, hI⟩

/-- The concrete two-term model with its conormal differential transported along
its specified term identifications. The ambient rank is an output of the theorem.
Source: Stacks 08SL, 0FJI
(blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.twoTerm {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (N : CotangentPresentation.ConormalModel T.chart.i T.chart.base)
    (hV : SheafOfModules.IsFiniteLocallyFreeOfRank
      (CotangentPresentation.ambientDifferentials T.chart.i T.chart.base) T.chart.n) :
    TwoTermDeterminantModel T.chart.U.toScheme where
  neg := CotangentPresentation.conormalTerm T.chart.i
  nonneg := CotangentPresentation.ambientDifferentials T.chart.i T.chart.base
  differential := N.negative.inv ≫ N.complex.d (-1) 0 ≫ N.zero.hom
  negRank := T.c
  nonnegRank := T.chart.n
  neg_free := T.conormal_free
  nonneg_free := hV

/-- The actual affine associated-sheaf functor, transported by the scheme's canonical
Spec isomorphism. It is used only to test the local Koszul formula.
Source: Stacks 01I7, 0BQZ
(blueprint: def-trf-lci-koszul-duality-data). -/
def affineSheaf (P : Scheme.{u}) [IsAffine P] :=
  tilde.functor Γ(P, ⊤) ⋙ Scheme.Modules.restrictFunctor P.isoSpec.hom

/-- A vector of an affine module as its actual global associated-sheaf section.
Source: Stacks 01I7 (blueprint: def-trf-lci-koszul-duality-data). -/
def affineSection (P : Scheme.{u}) [IsAffine P] (M : ModuleCat.{u} Γ(P, ⊤)) (x : M) :
    ((affineSheaf P).obj M).val.obj (op ⊤) :=
  (Scheme.Modules.restrictAppIso P.isoSpec.hom (tilde M) ⊤).inv
    (tilde.toOpen M (P.isoSpec.hom ''ᵁ (⊤ : P.Opens)) x)

/-- Exact affine sheafification is additive, including transport by the Spec isomorphism.
Source: Stacks 01I7 (blueprint: def-trf-lci-koszul-duality-data). -/
instance affineSheaf_additive (P : Scheme.{u}) [IsAffine P] : (affineSheaf P).Additive := by
  unfold affineSheaf
  infer_instance

/-- The affine Koszul resolution, put in nonpositive cohomological degrees.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
@[irreducible] def Chart.koszul {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : Chart f d) [IsAffine T.chart.P] (g : Fin T.c → Γ(T.chart.P, ⊤)) :=
  ((affineSheaf T.chart.P).mapHomologicalComplex (.up ℤ)).obj
    ((ExteriorAlgebra.koszulComplex Γ(T.chart.P, ⊤) T.c g).extend
      ComplexShape.embeddingDownNat)

/-- The degree identification of the nonpositive Koszul complex.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.koszulTerm {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : Chart f d) [IsAffine T.chart.P] (g : Fin T.c → Γ(T.chart.P, ⊤)) (r : ℕ) :
    (T.koszul g).X (-(r : ℤ)) ≅
      (affineSheaf T.chart.P).obj
        ((ExteriorAlgebra.koszulComplex Γ(T.chart.P, ⊤) T.c g).X r) := by
  unfold Chart.koszul
  exact (affineSheaf T.chart.P).mapIso
    ((ExteriorAlgebra.koszulComplex Γ(T.chart.P, ⊤) T.c g).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl)

/-- The standard top wedge as a section in degree zero after shifting by -c.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.topSection {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : Chart f d) [IsAffine T.chart.P] (g : Fin T.c → Γ(T.chart.P, ⊤)) :
    (((T.koszul g)⟦(-(T.c : ℤ))⟧).X 0).val.obj (op ⊤) :=
  (CochainComplex.shiftFunctorObjXIso (T.koszul g) (-(T.c : ℤ)) 0 (-(T.c : ℤ))
    (zero_add _).symm).inv.val.app (op ⊤)
    ((T.koszulTerm g T.c).inv.val.app (op ⊤)
      (affineSection T.chart.P
        (ModuleCat.of _ (⋀[Γ(T.chart.P, ⊤)]^T.c (Fin T.c →₀ Γ(T.chart.P, ⊤))))
        (exteriorPower.ιMulti _ T.c (fun j ↦ Finsupp.single j 1))))

/-- Direct image of the line as an actual sheaf over i_*O_U.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.imageLine {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :=
  (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace T.chart.i)).obj T.line

/-- The unshifted duality target, supported in degree c.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.unshiftedTarget {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d) :=
  (DerivedCategory.singleFunctor _ (T.c : ℤ)).obj T.imageLine

/-- Exact scalar restriction to the ambient derived category.
Source: Stacks 05S7 (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.scalarDerived {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : PolynomialChartExactData T.chart.i) :
    DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace T.chart.i))) ⥤
      schemeDerivedCategory T.chart.P := by
  letI : HasDerivedCategory.{w} (SheafOfModules.{u} T.chart.P.ringCatSheaf) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)))
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
    (((TopologicalSpace.Opens.map T.chart.i.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology T.chart.P)
      (Opens.grothendieckTopology T.chart.U.toScheme)).obj T.chart.U.toScheme.ringCatSheaf)) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace T.chart.i))))
  letI : PreservesFiniteLimits T.scalars := h.limits
  letI : T.scalars.Additive := inferInstanceAs
    ((SheafOfModules.restrictScalars.{u} T.chart.i.toRingCatSheafHom).Additive)
  letI : PreservesFiniteColimits T.scalars := h.colimits
  exact T.scalars.mapDerivedCategory

/-- Exact scalar restriction on a single complex, with its canonical comparison.
Source: Stacks 05S7 (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.scalarSingle {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : PolynomialChartExactData T.chart.i)
    (M : SheafOfModules.{u} (moduleRings (directImageAlgebraSpace T.chart.i))) (k : ℤ) :
    (T.scalarDerived h).obj ((DerivedCategory.singleFunctor _ k).obj M) ≅
      (DerivedCategory.singleFunctor _ k).obj (T.scalars.obj M) := by
  letI : HasDerivedCategory.{w} (SheafOfModules.{u} T.chart.P.ringCatSheaf) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)))
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
    (((TopologicalSpace.Opens.map T.chart.i.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology T.chart.P)
      (Opens.grothendieckTopology T.chart.U.toScheme)).obj T.chart.U.toScheme.ringCatSheaf)) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace T.chart.i))))
  letI : PreservesFiniteLimits T.scalars := h.limits
  letI : T.scalars.Additive := inferInstanceAs
    ((SheafOfModules.restrictScalars.{u} T.chart.i.toRingCatSheafHom).Additive)
  letI : PreservesFiniteColimits T.scalars := h.colimits
  exact (Functor.mapDerivedCategorySingleFunctor T.scalars k).app M

/-- The unshifted Hom model, with multiplication action and evaluation adjunction.
Source: Stacks 0BUZ, 0BQZ
(blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.unshiftedModel {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : PolynomialChartExactData T.chart.i) :=
  (polynomialChartDerivedHom T.chart.i h).obj ((DerivedCategory.singleFunctor _ 0).obj T.omega)

/-- The scalar-restriction/coinduction adjunction induced by the actual evaluation counit.
Source: Stacks 0BUZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.adjunction {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : PolynomialChartExactData T.chart.i) :
    T.scalarDerived h ⊣ polynomialChartDerivedHom T.chart.i h := by
  letI := h.additive
  letI : HasDerivedCategory.{w} (SheafOfModules.{u} T.chart.P.ringCatSheaf) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)))
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
    (((TopologicalSpace.Opens.map T.chart.i.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology T.chart.P)
      (Opens.grothendieckTopology T.chart.U.toScheme)).obj T.chart.U.toScheme.ringCatSheaf)) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace T.chart.i))))
  letI : PreservesFiniteLimits T.scalars := h.limits
  letI : T.scalars.Additive := inferInstanceAs
    ((SheafOfModules.restrictScalars.{u} T.chart.i.toRingCatSheafHom).Additive)
  letI : PreservesFiniteColimits T.scalars := h.colimits
  exact (polynomialChartDerivedAdjunction T.chart.i h).ofNatIsoLeft
    (Functor.rightDerivedFunctorIsoMapDerivedCategory T.scalars)

/-- Pair a line section with a wedge of conormal sections, using evaluation.
Source: Stacks 0BQZ, 0FJI
(blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.evaluate {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (V : T.chart.U.toScheme.Opens) (y : T.line.val.obj (op V))
    (z : (exteriorSheaf (CotangentPresentation.conormalTerm T.chart.i) T.c).val.obj (op V)) :=
  ((((SheafOfModules.tensorHomAdjunction T.chart.U.toScheme.sheaf
    (exteriorSheaf (CotangentPresentation.conormalTerm T.chart.i) T.c)).homEquiv _ _
      T.pairing).val.app (op V) y).app (op (Over.mk (𝟙 V)))) z

/-- The quotient-augmented affine Koszul resolution has the standard augmentation,
not a unit multiple. The formula in degree zero also covers c=0.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.IsAugmentation {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : Chart f d) [IsAffine T.chart.P] (g : Fin T.c → Γ(T.chart.P, ⊤))
    (ε : T.koszul g ⟶ (CochainComplex.singleFunctor T.chart.P.Modules 0).obj
      (T.scalars.obj (SheafOfModules.unit (moduleRings (directImageAlgebraSpace T.chart.i))))) :
    Prop :=
  ∀ a : Γ(T.chart.P, ⊤),
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (T.scalars.obj (SheafOfModules.unit (moduleRings (directImageAlgebraSpace
        T.chart.i))))).hom.val.app (op ⊤)
      (ε.f 0 |>.val.app (op ⊤) <|
        (T.koszulTerm g 0).inv.val.app (op ⊤)
          (affineSection T.chart.P
            (ModuleCat.of _ (⋀[Γ(T.chart.P, ⊤)]^0 (Fin T.c →₀ Γ(T.chart.P, ⊤))))
            ((exteriorPower.zeroEquiv _ _).symm a))) = T.chart.i.app ⊤ a

/-- Shift the augmentation to a resolution of the quotient in degree c.
Source: Stacks 0BQZ (blueprint: def-trf-lci-koszul-duality-data). -/
@[irreducible] def Chart.augmentationShift {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : Chart f d) [IsAffine T.chart.P] (g : Fin T.c → Γ(T.chart.P, ⊤))
    (ε : T.koszul g ⟶ (CochainComplex.singleFunctor T.chart.P.Modules 0).obj
      (T.scalars.obj (SheafOfModules.unit (moduleRings (directImageAlgebraSpace T.chart.i)))))
    [QuasiIso ε] :
    DerivedCategory.Q.{w}.obj ((T.koszul g)⟦(-(T.c : ℤ))⟧) ≅
      (DerivedCategory.singleFunctor _ (T.c : ℤ)).obj
        (T.scalars.obj (SheafOfModules.unit (moduleRings (directImageAlgebraSpace
          T.chart.i)))) :=
  (DerivedCategory.Q.commShiftIso (-(T.c : ℤ))).app (T.koszul g) ≪≫
    (shiftFunctor _ (-(T.c : ℤ))).mapIso (asIso (DerivedCategory.Q.map ε)) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (-(T.c : ℤ)) (T.c : ℤ) 0
      (neg_add_cancel _)).app _

/-- The local signed top-wedge formula on every quotient-augmented Koszul roof.
The coefficient is arbitrary, so no trivialization of the ambient line is chosen.
Source: Stacks 0BQZ, ordered contractions, and 0BZJ
(blueprint: def-trf-lci-koszul-duality-data). -/
def Chart.IsNormalized {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : Chart f d) (h : PolynomialChartExactData T.chart.i)
    (ρ : T.unshiftedModel h ≅ T.unshiftedTarget) : Prop :=
  ∀ (_haff : IsAffine T.chart.P) (g : Fin T.c → Γ(T.chart.P, ⊤))
    (_hg : RingTheory.Sequence.IsKoszulRegular g)
    (_hI : Ideal.span (Set.range g) = T.chart.i.ker.ideal ⟨⊤, isAffineOpen_top _⟩)
    (q : Fin T.c → Γ(T.chart.i.ker.toModules, ⊤)),
    (∀ j, T.chart.i.ker.toModulesι.val.app (op ⊤) (q j) = g j) →
    ∀ (ε : T.koszul g ⟶ (CochainComplex.singleFunctor T.chart.P.Modules 0).obj
      (T.scalars.obj (SheafOfModules.unit (moduleRings (directImageAlgebraSpace T.chart.i)))))
      (_hε : QuasiIso ε), T.IsAugmentation g ε →
    ∀ (s : SheafOfModules.unit (moduleRings (directImageAlgebraSpace T.chart.i)) ⟶ T.imageLine)
      (z : (T.koszul g)⟦(-(T.c : ℤ))⟧ ⟶
        (CochainComplex.singleFunctor T.chart.P.Modules 0).obj T.omega),
    ((T.adjunction h).homEquiv _ _).symm
      ((DerivedCategory.singleFunctor _ (T.c : ℤ)).map s ≫ ρ.inv) =
      (T.scalarSingle h _ (T.c : ℤ)).hom ≫ (T.augmentationShift g ε).inv ≫
        DerivedCategory.Q.{w}.map z →
    ∀ (a : Γ(T.chart.P, ⊤))
      (v : Fin T.chart.n → Γ(T.chart.base.relativeDifferentials, ⊤)),
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T.omega).hom.val.app (op ⊤)
      (z.f 0 |>.val.app (op ⊤) <|
        T.topSection g) =
        a • exteriorSheafSection T.chart.base.relativeDifferentials T.chart.n ⊤ v →
    T.evaluate (T.chart.i ⁻¹ᵁ ⊤)
      (s.val.app (op ⊤) (1 : Γ(T.chart.U.toScheme, T.chart.i ⁻¹ᵁ ⊤)))
      (exteriorSheafSection (CotangentPresentation.conormalTerm T.chart.i) T.c
        (T.chart.i ⁻¹ᵁ ⊤) (fun j ↦
          Scheme.Modules.tensorPullbackSection T.chart.i T.chart.i.ker.toModules ⊤ (q j))) =
      (-1 : Γ(T.chart.U.toScheme, T.chart.i ⁻¹ᵁ ⊤)) ^ (T.c * (T.c - 1) / 2) •
        (T.chart.i.app ⊤ a) •
        exteriorSheafSection
          (CotangentPresentation.ambientDifferentials T.chart.i T.chart.base) T.chart.n
          (T.chart.i ⁻¹ᵁ ⊤) (fun j ↦
            Scheme.Modules.tensorPullbackSection T.chart.i T.chart.base.relativeDifferentials
              ⊤ (v j))



end AlgebraicGeometry.LciKoszulDuality
