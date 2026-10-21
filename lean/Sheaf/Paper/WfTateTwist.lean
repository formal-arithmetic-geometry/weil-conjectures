/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.PbcWeilCategory
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Paper.WeilTensorWeil
public import Sheaf.Paper.WeilInternalHom
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PurIntegralTwistLineInverseImage

/-! # Tate twists in the raw rational Weil category

Source: main-20261015, sec-algebraic-groups-lie-algebras/sk-d-ab-cyclotomic,
Definition of Tate twists (blueprint: def-wf-tate-twist).

The signed lines and their root-normalized transport are the existing constructions.
This module transports them through the canonical completed coefficient isomorphism
and restricts their tensor action to the actual PBC integral and rational categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.WfTateTwist

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The inherited invertibility hypothesis on the geometric fibre.
Source: definition, finite-field hypotheses (blueprint: def-wf-tate-twist). -/
instance stalkUnits : Fact (∀ x : (D.geometricFiber X₀).left,
    IsUnit (c.l : (D.geometricFiber X₀).left.presheaf.stalk x)) :=
  ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.2⟩

variable (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The existing completed coefficient module category, with its fixed small-site size.
Source: definition, completed coefficients (blueprint: def-wf-tate-twist). -/
abbrev Modules := pbcModules (D.geometricFiber X₀).left
  (pbcAdicCompletion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E))

/-- The published signed line, in the PBC coefficient coordinates.
Source: definition, E(0), E(m), and E(-m) (blueprint: def-wf-tate-twist). -/
abbrev line (m : ℤ) : Modules D c X₀ E :=
  pbcTateLineSheaf c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m

/-- Exact transport on completed module sheaves along geometric Frobenius.
Source: definition, P_E (blueprint: def-wf-tate-twist). -/
abbrev pull := pbcIsoModulePullback (D.geometricFrobenius X₀).hom
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- Insertion into the canonical module pullback, through its normalized adjunction unit.
Source: definition, inverse-image tensor comparison (blueprint: def-wf-tate-twist). -/
def sectionMap (M : Modules D c X₀ E) (V : (D.geometricFiber X₀).left.ProEt)
    (x : M.val.obj (op V)) :=
  ((proEtaleRingModuleAdjunction (D.geometricFrobenius X₀).hom
    (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
    (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
    (asIso (AlgebraicGeometry.Scheme.completedCoefficientMap (D.geometricFrobenius X₀).hom
      (pbcStageDatum.{u} c.l c.Qbar E)))).unit.app M).val.app (op V) x

/-- Transport the existing root-normalized signed-line map through the coefficient
isomorphism, retaining its value on every adjunction-unit section. The underlying
additive sheaves of coefficient restriction are unchanged, hence the HEq formula.
Source: definition, root pullbacks, signed powers and duals (blueprint: def-wf-tate-twist).
Proof: the coefficient isomorphism is fixed by every finite projection. Its square
with Frobenius commutes since both maps induce the same constant quotient maps.
Restrict the published signedLineMaps through that square. The positive maps are
fixed on ordered root tensors, at zero on the coefficient unit, and the negative maps
by evaluation with the inverse positive map. This yields the displayed formula.
The module adjunction and generation by its unit sections prove uniqueness. -/
theorem lineMap_exists (m : ℤ) :
    ∃! t : (pull D c X₀ E).obj (line D c X₀ E m) ≅ line D c X₀ E m,
      ∀ (V : (D.geometricFiber X₀).left.ProEt)
        (x : (line D c X₀ E m).val.obj (op V)),
        HEq (t.hom.val.app (op ((proEtaleBaseChange
          (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E (line D c X₀ E m) V x))
          ((FrobeniusCoefficientTwists.signedLineMaps c.l
            (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFrobenius X₀).hom m).hom.val.app
              (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
            (FrobeniusCoefficientTwists.moduleSection c.l
              (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFrobenius X₀).hom
              (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
                (D.geometricFiber X₀).left m) V x)) := by
  sorry

/-- The canonical line transport, chosen only from its unique root/evaluation formula.
Source: definition, phi_m (blueprint: def-wf-tate-twist). -/
def lineMap (m : ℤ) := (lineMap_exists D c X₀ E m).exists.choose

/-- Every signed line belongs to the actual PBC integral coefficient category.
Source: definition, one-stratum perfect model R[0] (blueprint: def-wf-tate-twist).
Proof: the completed root line is locally free of rank one with its compatible
finite reductions. The unit, all positive powers and their duals have the same
local model R[0]. The geometric fibre is noetherian and finite dimensional and
l is invertible. The stratified-perfect characterization therefore applies with
one stratum, giving bounded constructibility, completeness and compatible etale
origin. Coefficient restriction along the canonical isomorphism preserves these
conditions and gives precisely the PBC line written here. -/
theorem line_mem (m : ℤ) :
    PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)
      ((DerivedCategory.singleFunctor _ 0).obj (line D c X₀ E m)) := by
  sorry

/-- The degree-zero signed line as an integral object, with real underlying data.
Source: definition, integral representatives of E(m) (blueprint: def-wf-tate-twist). -/
def integralLine (m : ℤ) : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj (line D c X₀ E m), line_mem D c X₀ E m⟩

/-- The root-normalized map in the ambient derived category, in degree zero.
Source: definition, placing tau in degree zero (blueprint: def-wf-tate-twist). -/
def ambientLineMap (m : ℤ) :
    (pull D c X₀ E).mapDerivedCategory.obj (integralLine D c X₀ E m).obj ≅
      (integralLine D c X₀ E m).obj :=
  ((pull D c X₀ E).mapDerivedCategorySingleFunctor 0).app (line D c X₀ E m) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (lineMap D c X₀ E m)

/-- Rationalization of the actual degree-zero signed integral line.
Source: definition, E(m) (blueprint: def-wf-tate-twist). -/
def rationalLine (m : ℤ) : pbcStageCategory c.l c.Qbar (D.geometricFiber X₀).left E :=
  (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).obj
    (integralLine D c X₀ E m)

/-- The specified strict arrow P_E E(m) isomorphic to E(m). At m=1 it is the
functorial root pullback, with no choice of a basis or of a trivialization.
Source: definition, phi_0 and phi_1 and signed Weil maps (blueprint: def-wf-tate-twist). -/
def rationalLineMap (m : ℤ) :
    (weilFrobeniusPullback D c X₀ E).obj (rationalLine D c X₀ E m) ≅
      rationalLine D c X₀ E m :=
  (pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).mapIso
    (ObjectProperty.isoMk _ (ambientLineMap D c X₀ E m))

/-- The signed coefficient Weil pair, using the canonical root arrow and its powers/duals.
Source: definition, E(m) as a Weil object (blueprint: def-wf-tate-twist). -/
def weilLine (m : ℤ) : WeilD D c X₀ E :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (rationalLine D c X₀ E m)
    (rationalLineMap D c X₀ E m)

/-- Exact sheaf tensor with the existing signed line.
Source: definition, K(m) (blueprint: def-wf-tate-twist). -/
abbrev tensor (m : ℤ) :=
  pbcTateSheafTensor c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m

/-- The unique ordinary tensor/pullback comparison, followed by the root-line map.
The formula tests every module, every local section and every signed-line section;
thus it fixes the entire natural isomorphism, including the negative exponents.
Source: definition, induced tensor Weil map (blueprint: def-wf-tate-twist).
Proof: the module pullback tensor comparison sends a pulled pure tensor x tensor y
to pulled x tensor pulled y. Compose the second factor with lineMap. The coefficient
isomorphism preserves balancing. These formulas give inverse maps by inverse transport
and the inverse line map. They are natural in the input module. Local pure tensors
generate after sheafification, and adjunction-unit sections generate pullback, so the
formula determines the comparison uniquely. -/
theorem tensorComparison_exists (m : ℤ) :
    ∃! g : tensor D c X₀ E m ⋙ pull D c X₀ E ≅
        pull D c X₀ E ⋙ tensor D c X₀ E m,
      ∀ (M : Modules D c X₀ E) (V : (D.geometricFiber X₀).left.ProEt)
        (x : M.val.obj (op V)) (y : (line D c X₀ E m).val.obj (op V)),
        HEq ((g.hom.app M).val.app (op ((proEtaleBaseChange
          (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E ((tensor D c X₀ E m).obj M) V
              (SheafOfModules.siteSheafTensorTmul
                ((purOrdinaryCoefficientModel c.l (pbcFiniteField.{u} c.l c.Qbar E)
                  (D.geometricFiber X₀).left).obj M)
                (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
                  (D.geometricFiber X₀).left m) (op V) x y)))
          (SheafOfModules.siteSheafTensorTmul
            ((purOrdinaryCoefficientModel c.l (pbcFiniteField.{u} c.l c.Qbar E)
              (D.geometricFiber X₀).left).obj ((pull D c X₀ E).obj M))
            (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
              (D.geometricFiber X₀).left m)
            (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E M V x)
            ((lineMap D c X₀ E m).hom.val.app
              (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
              (sectionMap D c X₀ E (line D c X₀ E m) V y))) := by
  sorry

/-- The ordinary comparison with its unique pure-tensor normalization.
Source: definition, tensor Frobenius map (blueprint: def-wf-tate-twist). -/
def tensorComparison (m : ℤ) := (tensorComparison_exists D c X₀ E m).exists.choose

/-- Exact descent of the ordinary tensor/pullback comparison to the derived category.
Source: definition, completed derived tensor with a line (blueprint: def-wf-tate-twist). -/
def ambientComparison (m : ℤ) :
    (tensor D c X₀ E m).mapDerivedCategory ⋙ (pull D c X₀ E).mapDerivedCategory ≅
      (pull D c X₀ E).mapDerivedCategory ⋙ (tensor D c X₀ E m).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (tensorComparison D c X₀ E m) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Restriction of the actual exact line tensor to the integral coefficient category.
Source: definition, integral representatives (blueprint: def-wf-tate-twist). -/
def integral (m : ℤ) :=
  pbcConditionalIntegral (pbcStageDatum.{u} c.l c.Qbar E)
    (pbcTateAmbient c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m)
    (pbcTateAmbient_mem c.l (D.geometricFiber X₀).left
      (pbcFiniteField.{u} c.l c.Qbar E)
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.1 m)

/-- The existing rational twist, with the geometric hypotheses supplied by finite type.
Source: definition, raw rationalization of K(m) (blueprint: def-wf-tate-twist). -/
def rational (m : ℤ) :=
  letI : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n) :=
    ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.1⟩
  pbcTateRational c.l (D.geometricFiber X₀).left c.Qbar E m

/-- Restrict and rationalize the prescribed comparison, without choosing a new map.
Its components on integral representatives are exactly the ambient derived comparison.
Source: definition, rational tensor Weil map (blueprint: def-wf-tate-twist).
Proof: tensor by a rank-one line preserves complete stratified-perfect objects by
the single-stratum criterion. Transport also preserves this full subcategory. Thus
the ambient comparison restricts uniquely. Apply raw scalar localization to its
components: denominators have the same scalar on both sides, so naturality extends
to every localized arrow. The integral representative equation below and linearity
fix the resulting natural isomorphism uniquely. -/
theorem rationalComparison_exists (m : ℤ) :
    ∃! g : rational D c X₀ E m ⋙ weilFrobeniusPullback D c X₀ E ≅
        weilFrobeniusPullback D c X₀ E ⋙ rational D c X₀ E m,
      ∀ K : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E,
        HEq (g.hom.app ((pbcStageLocalization c.l c.Qbar
          (D.geometricFiber X₀).left E).obj K))
          ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).map
            (ObjectProperty.homMk
              (X := (pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
                (pbcStageDatum.{u} c.l c.Qbar E)).obj ((integral D c X₀ E m).obj K))
              (Y := (integral D c X₀ E m).obj
                ((pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
                  (pbcStageDatum.{u} c.l c.Qbar E)).obj K))
              ((ambientComparison D c X₀ E m).hom.app K.obj))) := by
  sorry

/-- Rationalization of the specified derived comparison on the original integral models.
Source: definition, phi on K(m) (blueprint: def-wf-tate-twist). -/
def rationalComparison (m : ℤ) := (rationalComparison_exists D c X₀ E m).exists.choose

/-- The Tate twist on strict Weil pairs. Its underlying functor is tensor with the
signed root line and its underlying map is u tensor id. The structure map is the
canonical tensor/pullback comparison followed by tensor of the input Weil map.
Source: definition, final displayed formula (blueprint: def-wf-tate-twist). -/
def functor (m : ℤ) : WeilD D c X₀ E ⥤ WeilD D c X₀ E :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (rationalComparison D c X₀ E m)

end WeilConjectures.WfTateTwist
