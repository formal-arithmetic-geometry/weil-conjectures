/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.WeilInternalHom
public import Sheaf.Paper.LocalizedTStructure
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntegralConstructibleInternalHom
import Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.CategoryTheory.RingedPresentationTransport

/-! # Internal Hom of completed rational Weil complexes

Source: main-20261015 blueprint, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
Internal Hom of Weil complexes (blueprint: lem-wf-internal-hom-weil).

The integral restriction, rational fraction action and shift comparisons use the recorded
completed coefficient category. Exactness means preservation of underlying distinguished
triangles, with equivariant shift comparisons; no Verdier structure on fixed pairs is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- Closure of the specified integral category under the existing ambient derived Hom.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil).
Proof: geometric-fiber finite-type geometry gives noetherianity, finite dimension and
invertibility of ell. The integral-stratified-perfect characterization identifies this
full category, including etale-origin witnesses, with the completed integral category in
cor-coef-integral-internal-hom. Apply its Hom closure and transport back through that
characterization. Raw rationalization does not require Frobenius-stable lattices. -/
theorem wfHom_constructible (M N : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E) :
    PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)
      ((wfOrdinaryDerivedHom (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E)).obj (op M.obj, N.obj)) := by
  sorry

/-- Restriction has exactly the ambient Hom objects and maps.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfConstructibleIntegralHom :
    (pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E)ᵒᵖ ×
      pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E ⥤
        pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E))
    (((pbcStageInclusion c.l c.Qbar (D.geometricFiber X₀).left E).op.prod
      (pbcStageInclusion c.l c.Qbar (D.geometricFiber X₀).left E)) ⋙
        wfOrdinaryDerivedHom (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E))
    (fun MN ↦ wfHom_constructible D c X₀ E MN.1.unop MN.2)

/-- The unique rational restriction has the integral action after localization.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil).
Proof: extend the integral Hom map bilinearly over the localized valuation ring, as in
wfRationalHomMap_exists. The map on two fractions has the product denominator.
Identity and composition follow on pure tensors and then by bilinearity. Integral
arrows and inverses of uniformizer multiples generate all rational arrows, so the
displayed restriction determines the functor uniquely. -/
theorem wfConstructibleRationalHom_existsUnique :
    ∃! H : (pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E)ᵒᵖ ×
        pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E ⥤
          pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E,
      ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).op.prod
        (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E)) ⋙ H =
          wfConstructibleIntegralHom D c X₀ E ⋙
            pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E := by
  sorry

/-- Rational Hom is the uniquely specified bilinear extension, with unchanged objects.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfConstructibleRationalHom :=
  (wfConstructibleRationalHom_existsUnique D c X₀ E).exists.choose

/-- The integral-object comparison is fixed by the rationalization equality.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfConstructibleHomModel
    (M N : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E) :
    (wfConstructibleRationalHom D c X₀ E).obj
        (op ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).obj M),
          (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).obj N) ≅
      (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).obj
        ((wfConstructibleIntegralHom D c X₀ E).obj (op M, N)) :=
  eqToIso (Functor.congr_obj
    (wfConstructibleRationalHom_existsUnique D c X₀ E).exists.choose_spec (op M, N))

section Shifts
variable [Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n)]
  [Fact (∀ t : (D.geometricFiber X₀).left,
    IsUnit (c.l : (D.geometricFiber X₀).left.presheaf.stalk t))]

/-- The existing coefficient-field action, at the canonical small model of E.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
instance wfHomCoefficientLinear :
    Linear (pbcFiniteField c.l c.Qbar E)
      (pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E) :=
  pbcRationalLinear c.l (pbcFiniteField c.l c.Qbar E) (D.geometricFiber X₀).left
    Fact.out Fact.out

/-- The coefficient scalar action restricts uniquely to commuting Weil morphisms.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil).
Proof: coefficient transport fixes constant scalars, hence is E-linear after the
canonical fraction map. Therefore scalar multiples satisfy the same commuting
equation. The inherited Hom module and composition give a linear category;
faithfulness of forgetting the structure determines every scalar multiple uniquely. -/
theorem wfHomWeilLinear_existsUnique :
    ∃! P : Linear (pbcFiniteField c.l c.Qbar E) (WeilD D c X₀ E),
      (fun [pInst : Linear (pbcFiniteField c.l c.Qbar E) (WeilD D c X₀ E)] ↦
        ∀ (K L : WeilD D c X₀ E) (a : pbcFiniteField c.l c.Qbar E) (f : K ⟶ L),
          (a • f).hom.f = a • f.hom.f) (pInst := P) := by
  sorry

/-- The uniquely normalized inherited coefficient-field action on Weil morphisms.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
instance wfHomWeilLinear : Linear (pbcFiniteField c.l c.Qbar E) (WeilD D c X₀ E) :=
  (wfHomWeilLinear_existsUnique D c X₀ E).exists.choose

/-- Integral target shift, with the recorded normalized ringed-site Hom comparison.
Source: main-20261015, Internal Hom of Weil complexes; Stacks 08JC
(blueprint: lem-wf-internal-hom-weil). -/
def wfIntegralHomRightShift
    (M N : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E) (n : ℤ) :
    (wfConstructibleIntegralHom D c X₀ E).obj (op M, N⟦n⟧) ≅
      ((wfConstructibleIntegralHom D c X₀ E).obj (op M, N))⟦n⟧ :=
  ObjectProperty.isoMk _
    ((wfOrdinaryDerivedHom (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)).mapIso
        ((Iso.refl (op M.obj)).prod
          (((pbcStageInclusion c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app N)) ≪≫
      ((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u + 1, u + 2}
        (ProEt.topology (D.geometricFiber X₀).left)
        (pbcAdicCompletion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E))
        M.obj).commShiftIso n).app N.obj ≪≫
      (((pbcStageInclusion c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app
        ((wfConstructibleIntegralHom D c X₀ E).obj (op M, N))).symm)

/-- Integral source shift, with the signed comparison of the existing Hom complex.
Source: main-20261015, Internal Hom of Weil complexes; Stacks 08JA
(blueprint: lem-wf-internal-hom-weil). -/
def wfIntegralHomLeftShift
    (M N : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E) (n : ℤ) :
    (wfConstructibleIntegralHom D c X₀ E).obj (op (M⟦n⟧), N) ≅
      ((wfConstructibleIntegralHom D c X₀ E).obj (op M, N))⟦-n⟧ :=
  ObjectProperty.isoMk _
    ((wfOrdinaryDerivedHom (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)).mapIso
        ((((pbcStageInclusion c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app
          M).symm.op.prod (Iso.refl N.obj)) ≪≫
      ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u + 1, u + 2}
        (ProEt.topology (D.geometricFiber X₀).left)
        (pbcAdicCompletion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E))
        M.obj n).app N.obj).symm ≪≫
      (((pbcStageInclusion c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso (-n)).app
        ((wfConstructibleIntegralHom D c X₀ E).obj (op M, N))).symm)

/-- Canonical rational target shift, obtained by localizing the integral comparison.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfRationalHomRightShift
    (M N : pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E) (n : ℤ) :
    (wfConstructibleRationalHom D c X₀ E).obj (op M, N⟦n⟧) ≅
      ((wfConstructibleRationalHom D c X₀ E).obj (op M, N))⟦n⟧ :=
  (wfConstructibleRationalHom D c X₀ E).mapIso
    ((Iso.refl (op M)).prod
      (((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app
        N.obj).symm) ≪≫
    wfConstructibleHomModel D c X₀ E M.obj (N.obj⟦n⟧) ≪≫
    (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).mapIso
      (wfIntegralHomRightShift D c X₀ E M.obj N.obj n) ≪≫
    ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app
      ((wfConstructibleIntegralHom D c X₀ E).obj (op M.obj, N.obj)) ≪≫
    (shiftFunctor _ n).mapIso (wfConstructibleHomModel D c X₀ E M.obj N.obj).symm

/-- Canonical rational source shift, retaining the signed Hom-complex normalization.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfRationalHomLeftShift
    (M N : pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E) (n : ℤ) :
    (wfConstructibleRationalHom D c X₀ E).obj (op (M⟦n⟧), N) ≅
      ((wfConstructibleRationalHom D c X₀ E).obj (op M, N))⟦-n⟧ :=
  (wfConstructibleRationalHom D c X₀ E).mapIso
    ((((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app
      M.obj).op.prod (Iso.refl N)) ≪≫
    wfConstructibleHomModel D c X₀ E (M.obj⟦n⟧) N.obj ≪≫
    (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).mapIso
      (wfIntegralHomLeftShift D c X₀ E M.obj N.obj n) ≪≫
    ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso (-n)).app
      ((wfConstructibleIntegralHom D c X₀ E).obj (op M.obj, N.obj)) ≪≫
    (shiftFunctor _ (-n)).mapIso (wfConstructibleHomModel D c X₀ E M.obj N.obj).symm

/-- Exact module transport restricted through the fully faithful integral inclusion.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
@[instance_reducible] def wfHomIntegralFrobeniusCommShift :
    (pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
      (pbcStageDatum.{u} c.l c.Qbar E)
      (hf := Iso.isIso_hom (D.geometricFrobenius X₀))).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.lift
    (PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E))
    (pbcStageInclusion c.l c.Qbar (D.geometricFiber X₀).left E ⋙
      pbcIsoAmbientPullback (D.geometricFrobenius X₀).hom
        (pbcStageDatum.{u} c.l c.Qbar E)
        (hf := Iso.isIso_hom (D.geometricFrobenius X₀)))
    (pbcIsoAmbientPullback_preserves (D.geometricFrobenius X₀).hom
      (pbcStageDatum.{u} c.l c.Qbar E)
      (hf := Iso.isIso_hom (D.geometricFrobenius X₀)))).CommShift ℤ)

/-- The coefficient Frobenius/shift component, localized from exact module transport.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfHomFrobeniusShiftComponent
    (M : pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E) (n : ℤ) :
    (weilFrobeniusPullback D c X₀ E).obj (M⟦n⟧) ≅
      ((weilFrobeniusPullback D c X₀ E).obj M)⟦n⟧ :=
  letI := wfHomIntegralFrobeniusCommShift D c X₀ E
  (weilFrobeniusPullback D c X₀ E).mapIso
    (((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app
      M.obj).symm ≪≫
    (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).mapIso
      (((pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
        (pbcStageDatum.{u} c.l c.Qbar E)
        (hf := Iso.isIso_hom (D.geometricFrobenius X₀))).commShiftIso n).app M.obj) ≪≫
    ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).commShiftIso n).app
      ((pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
        (pbcStageDatum.{u} c.l c.Qbar E)
        (hf := Iso.isIso_hom (D.geometricFrobenius X₀))).obj M.obj)

/-- Shift of a fixed pair with precisely P(K[n]) ≅ P(K)[n] followed by phi[n].
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfHomShiftPair (K : WeilD D c X₀ E) (n : ℤ) : WeilD D c X₀ E :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (K.carrier⟦n⟧)
    (wfHomFrobeniusShiftComponent D c X₀ E K.carrier n ≪≫
      (shiftFunctor _ n).mapIso K.str)

/-- The two signed Hom shifts combine to the canonical shift by s-r.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfHomDoubleShift
    (M N : pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E) (r s : ℤ) :
    (wfConstructibleRationalHom D c X₀ E).obj (op (M⟦r⟧), N⟦s⟧) ≅
      ((wfConstructibleRationalHom D c X₀ E).obj (op M, N))⟦s - r⟧ :=
  wfRationalHomLeftShift D c X₀ E M (N⟦s⟧) r ≪≫
    (shiftFunctor _ (-r)).mapIso (wfRationalHomRightShift D c X₀ E M N s) ≪≫
    (shiftFunctorAdd' _ s (-r) (s - r) (sub_eq_add_neg s r).symm).symm.app _

/-- The contravariant connecting arrow is the signed source-shift comparison and
H(h,id), shifted once, with the canonical cancellation of [-1][1].
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def wfHomLeftConnecting
    (A C L : pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E)
    (h : C ⟶ A⟦(1 : ℤ)⟧) :
    (wfConstructibleRationalHom D c X₀ E).obj (op A, L) ⟶
      ((wfConstructibleRationalHom D c X₀ E).obj (op C, L))⟦(1 : ℤ)⟧ :=
  (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (neg_add_cancel 1)).inv.app _ ≫
    (shiftFunctor _ (1 : ℤ)).map
      ((wfRationalHomLeftShift D c X₀ E A L 1).inv ≫
        (wfConstructibleRationalHom D c X₀ E).map (Prod.mkHom h.op (𝟙 L)))

/-- The full clause expressing triangle preservation on fixed-pair diagrams.
The input and output distinguished triangles live in the coefficient category.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
def WfHomPreservesTriangles
    (W : (WeilD D c X₀ E)ᵒᵖ × WeilD D c X₀ E ⥤ WeilD D c X₀ E) : Prop :=
  ∀ (A B C : WeilD D c X₀ E) (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ wfHomShiftPair D c X₀ E A 1),
    Triangle.mk f.hom.f g.hom.f h.hom.f ∈
      distTriang (pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E) →
    (∀ K : WeilD D c X₀ E,
      ∃ j : W.obj (op K, C) ⟶ wfHomShiftPair D c X₀ E (W.obj (op K, A)) 1,
        HEq j.hom.f
          ((wfConstructibleRationalHom D c X₀ E).map
            (Prod.mkHom (𝟙 (op K.carrier)) h.hom.f) ≫
              (wfRationalHomRightShift D c X₀ E K.carrier A.carrier 1).hom) ∧
        Triangle.mk (W.map (Prod.mkHom (𝟙 (op K)) f)).hom.f
          (W.map (Prod.mkHom (𝟙 (op K)) g)).hom.f j.hom.f ∈
            distTriang (pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E)) ∧
    (∀ L : WeilD D c X₀ E,
      ∃ j : W.obj (op A, L) ⟶ wfHomShiftPair D c X₀ E (W.obj (op C, L)) 1,
        HEq j.hom.f (wfHomLeftConnecting D c X₀ E A.carrier C.carrier L.carrier h.hom.f) ∧
        Triangle.mk (W.map (Prod.mkHom g.op (𝟙 L))).hom.f
          (W.map (Prod.mkHom f.op (𝟙 L))).hom.f j.hom.f ∈
            distTriang (pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E))

end Shifts

/-- The inclusion already defining Weil carriers, specialized without changing its data.
Source: main-20261015, Internal Hom of Weil complexes
(blueprint: lem-wf-internal-hom-weil). -/
abbrev wfHomCoefficientInclusion :=
  wfConstructibleInclusion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Internal Hom restricts with its specified conjugation, maps, signed shifts,
separate-variable exactness, addition and coefficient-field linearity.
Source: main-20261015 blueprint, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
Internal Hom of Weil complexes, order 2915 (blueprint: lem-wf-internal-hom-weil).

Proof:
1. Finite-type geometric-fiber geometry gives noetherianity, finite dimension and
   ell invertible. The integral-stratified-perfect characterization identifies the
   integral PBC category with the completed category in cor-coef-integral-internal-hom.
   That corollary gives closure. Raw rationalization changes only morphisms, so the
   integral restriction rationalizes to wfConstructibleRationalHom, with the same
   ambient objects and the fraction rule of def-wf-internal-hom.
2. The ringed-site Hom exactness theorem gives normalized signed shifts and exactness
   on the ambient derived category. Integral closure restricts it; every rational
   distinguished triangle is an isomorphic localized integral triangle by
   lem-weil-linear-scalar-localization-triangulated. Bilinearity gives separate
   linearity and additivity after localization.
3. The specified alpha and the two Weil isomorphisms make beta invertible, with inverse
   alpha inverse after H(phi_K,phi_L inverse). No lattice stable under Frobenius is used.
4. For commuting u,v, naturality of alpha and their two commuting equations give
   H(u,v) beta = beta' P(H(u,v)). Thus the same maps are Weil morphisms. The ambient
   bifunctor's identity and composition laws make them a bifunctor of fixed pairs.
5. Exact coefficient transport preserves K-injectives by ringed-presentation-transport.
   Transport acts on every local Hom component and preserves degree. Consequently it
   commutes with the signed source and target reindexings. Naturality also intertwines
   precomposition by phi_K inverse and postcomposition by phi_L. Rationalizing proves
   the normalized double-shift isomorphism is an isomorphism of Weil pairs.
6. Apply steps 2 and 5 to a diagram of commuting arrows with distinguished underlying
   triangle. The covariant connecting arrow uses the target shift. The contravariant
   one uses the source shift and cancellation of [-1][1]. Both are commuting arrows,
   and both underlying triangles are distinguished. Addition and the inherited scalar
   action preserve the commuting equation, so the coefficient linearity in step 2
   restricts to Weil morphisms as well.

The two Fact arguments below are supplied by the recorded geometric-fiber theorem,
so they add no hypothesis. The scalar field is the canonical small model of E; its
scalar action is the existing pbcRationalLinear action via pbcRationalCoefficientEquiv.
HEq expresses the literal formulas across the stated equal carrier objects. -/
theorem wf_internalHom_weil :
    ∃ W : (WeilD D c X₀ E)ᵒᵖ × WeilD D c X₀ E ⥤ WeilD D c X₀ E,
      ((wfHomCoefficientInclusion D c X₀ E).op.prod
        (wfHomCoefficientInclusion D c X₀ E)) ⋙ wfInternalHom D c X₀ E =
          wfConstructibleRationalHom D c X₀ E ⋙ wfHomCoefficientInclusion D c X₀ E ∧
      (∀ K L : WeilD D c X₀ E,
        (W.obj (op K, L)).carrier =
          (wfConstructibleRationalHom D c X₀ E).obj (op K.carrier, L.carrier) ∧
        HEq (wfWeilStructure D c X₀ E (W.obj (op K, L)))
          (wfInternalHomFrobenius D c X₀ E K L)) ∧
      (∀ (K K' L L' : WeilD D c X₀ E) (f : K' ⟶ K) (g : L ⟶ L'),
        HEq (W.map (Prod.mkHom f.op g)).hom.f
          ((wfConstructibleRationalHom D c X₀ E).map (Prod.mkHom f.hom.f.op g.hom.f))) ∧
      (∀ K : (WeilD D c X₀ E)ᵒᵖ, ((Functor.curry.obj W).obj K).Additive) ∧
      (∀ L : WeilD D c X₀ E, ((Functor.curry.obj W).flip.obj L).Additive) ∧
      (fun [hDim : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n)]
        [hInv : Fact (∀ t : (D.geometricFiber X₀).left,
          IsUnit (c.l : (D.geometricFiber X₀).left.presheaf.stalk t))] ↦
        WfHomPreservesTriangles D c X₀ E W ∧
        (∀ (K L : WeilD D c X₀ E) (r s : ℤ),
          ∃ e : W.obj (op (wfHomShiftPair D c X₀ E K r), wfHomShiftPair D c X₀ E L s) ≅
              wfHomShiftPair D c X₀ E (W.obj (op K, L)) (s - r),
            HEq e.hom.hom.f (wfHomDoubleShift D c X₀ E K.carrier L.carrier r s).hom) ∧
        (∀ K : (WeilD D c X₀ E)ᵒᵖ,
          ((Functor.curry.obj W).obj K).Linear (pbcFiniteField c.l c.Qbar E)) ∧
        (∀ (K K' L : WeilD D c X₀ E) (a : pbcFiniteField c.l c.Qbar E) (f : K' ⟶ K),
          W.map (Prod.mkHom (a • f).op (𝟙 L)) =
            a • W.map (Prod.mkHom f.op (𝟙 L))) ∧
        (∀ M : (pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E)ᵒᵖ,
          ((Functor.curry.obj (wfConstructibleRationalHom D c X₀ E)).obj M).Linear
            (pbcFiniteField c.l c.Qbar E)) ∧
        (∀ (M M' N : pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E)
          (a : pbcFiniteField c.l c.Qbar E) (f : M' ⟶ M),
          (wfConstructibleRationalHom D c X₀ E).map (Prod.mkHom (a • f).op (𝟙 N)) =
            a • (wfConstructibleRationalHom D c X₀ E).map (Prod.mkHom f.op (𝟙 N))))
        (hDim := ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.1⟩)
        (hInv := ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.2⟩) := by
  sorry

end WeilConjectures
