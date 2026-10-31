/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSheafChartReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorScalarUnitTranspose

/-! # Scalar reduction of the unshifted positive root charts

Source: blueprint/latest, finite reduction of purity, Step 2, and the parent
finite tensor presentation reduction, Step 8; Stacks Tags 03EK and 07A4.
(blueprint: lem-pur-finite-tensor-line-chart-reduction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] finiteTensorFixedLine

attribute [local irreducible] finiteTensorPositiveChart
  finiteTensorReduction finiteTensorLineMaps
  finiteTensorCore finiteTensorLineComparison
  finiteTensorAdjunction finiteTensorFixedLineMap
  Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

attribute [local irreducible] Functor.mapDerivedCategory
  _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private theorem chart_of_transposes
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (S : C ⥤ C') (S' : D ⥤ D') (R : D ⥤ C) (F : C' ⥤ D') (G : D' ⥤ C')
    (adj : F ⊣ G) (i : S' ⋙ G ≅ R ⋙ S)
    {L U : C} {M V : D} {U' : C'} {V' : D'}
    (a : L ⟶ U) (b : M ⟶ V) (c : L ⟶ R.obj M) (j : U ⟶ R.obj V)
    (u : S.obj U ⟶ U') (v : S'.obj V ⟶ V')
    (l : F.obj (S.obj L) ⟶ S'.obj M) (e : F.obj U' ⟶ V')
    (hl : adj.homEquiv _ _ l = S.map c ≫ i.inv.app M)
    (hc : c ≫ R.map b = a ≫ j)
    (he : u ≫ adj.homEquiv _ _ e = S.map j ≫ i.inv.app V ≫ G.map v) :
    l ≫ S'.map b ≫ v = F.map (S.map a ≫ u) ≫ e := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
  rw [hl, G.map_comp]
  have hn := i.inv.naturality b
  change S.map (R.map b) ≫ i.inv.app V =
    i.inv.app M ≫ G.map (S'.map b) at hn
  calc
    (S.map c ≫ i.inv.app M) ≫ (G.map (S'.map b) ≫ G.map v) =
        S.map c ≫ S.map (R.map b) ≫ i.inv.app V ≫ G.map v := by
      rw [Category.assoc, ← reassoc_of% hn]
    _ = S.map a ≫ S.map j ≫ i.inv.app V ≫ G.map v := by
      rw [← S.map_comp_assoc, hc, S.map_comp, Category.assoc]
    _ = (S.map a ≫ u) ≫ adj.homEquiv _ _ e := by
      rw [Category.assoc, he]

private theorem line_transpose (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r : ℤ) :
    (P.finiteTensorAdjunction m hm hmn T).homEquiv _ _
        (P.finiteTensorLineComparison m hm hmn T r).hom =
      (_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
          (P.finiteTensorFixedLineMap m hm hmn T
            (P.finiteTensorLineMaps m hm hmn T) r) ≫
        (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
          (sfFixedRestriction.{u, u + 1, u + 1} T
            (P.finiteReductionRingHom m hm hmn)) 0).inv.app
          ((P.finiteReductionSetting m hm).finiteTensorFixedSheaf T r) := by
  unfold finiteTensorLineMaps finiteTensorLineComparison
  have hl := ((P.existsUnique_finiteTensorLines m hm hmn T).choose_spec.1.2).choose_spec.1 r
  unfold TransposedFamilyData.Pointwise at hl
  unfold finiteTensorLineComparisonData at hl
  exact eq_of_heq hl

private theorem line_maps_normalized (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    P.FiniteTensorLineMapsNormalized m hm hmn T (P.finiteTensorLineMaps m hm hmn T) := by
  unfold finiteTensorLineMaps
  exact (P.existsUnique_finiteTensorLines m hm hmn T).choose_spec.1.1

/-- The signed-line comparison preserves compatible unshifted positive root charts.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2; parent
lem-pur-finite-tensor-presentation-reduction, Step 8; Stacks 03EK and 07A4.
(blueprint: lem-pur-finite-tensor-line-chart-reduction).
Proof: lift ζ to a compatible sequence of primitive ℓ-power roots. Its coordinate
at m is η by hroot. Trivialize the integral rank-one line using this sequence.
The degree-one balancing normalization of finiteTensorLineMaps sends its reduced
A-basis to the reduced B-basis. The positive tensor recursion therefore sends
all ordered d-fold basis tensors to their B-counterparts. Both ordinary root
charts send these basis tensors to 1. In degree zero the semilinear map is the
coefficient ring map. The normalized tensorator and its unit axiom identify the
core unit inverse with scalar multiplication, so the assertion holds for d = 0
as well. These are equations of ordinary sheaf maps, checked on generators after
local trivialization and then glued. Apply the exact single-complex functor and
the scalar adjunction. Its hom equivalence is injective, and the recorded adjoint
normalization of finiteTensorLineComparison identifies the two transposes with
these same ordinary maps. This proves the derived equality without testing
arbitrary derived arrows locally. Changing the integral lift fixes the finite
basis at level n and therefore at level m, so the calculation is independent of
the lift. It applies to m = P.level, the empty scheme, and ramified coefficients;
no flatness of the quotient map is used. -/
theorem finiteTensorLineChart_reduction (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (d : ℕ) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (η : P.field.k)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    (P.finiteTensorLineComparison m hm hmn T d).hom ≫
        ((P.finiteReductionSetting m hm).finiteTensorPositiveChart T η hη d).hom =
      (P.finiteTensorReduction m hm hmn T).map
          (P.finiteTensorPositiveChart T ζ hζ d).hom ≫
        (P.finiteTensorCore m hm hmn T).εIso.inv := by
  let c := P.finiteTensorLineMaps m hm hmn T
  have hc : P.FiniteTensorLineMapsNormalized m hm hmn T c :=
    line_maps_normalized P m hm hmn T
  have hl' := line_transpose P m hm hmn T (d : ℤ)
  have hs := P.finiteTensorSheafChart_reduction m hm hmn T c hc d ζ hζ η hη hroot
  have he := P.finiteTensorScalarUnit_transpose m hm hmn T
  have h := chart_of_transposes
    (_root_.DerivedCategory.singleFunctor.{u + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0)
    (_root_.DerivedCategory.singleFunctor.{u + 1}
      (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient)) 0)
    (sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn))
    (P.finiteTensorReduction m hm hmn T)
    (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
      (P.finiteReductionRingHom m hm hmn) T)
    (P.finiteTensorAdjunction m hm hmn T)
    (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
      (sfFixedRestriction.{u, u + 1, u + 1} T
        (P.finiteReductionRingHom m hm hmn)) 0)
    (P.finiteTensorSheafCharts T ζ hζ d).hom
    ((P.finiteReductionSetting m hm).finiteTensorSheafCharts T η hη d).hom
    (P.finiteTensorFixedLineMap m hm hmn T c d)
    (Functor.LaxMonoidal.ε
      (sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn)))
    (_root_.DerivedCategory.singleFunctorObjUnitIso _).hom
    (_root_.DerivedCategory.singleFunctorObjUnitIso _).hom
    (P.finiteTensorLineComparison m hm hmn T d).hom
    (P.finiteTensorCore m hm hmn T).εIso.inv hl' hs he
  unfold finiteTensorPositiveChart finiteTensorSingleUnitChart
  dsimp only [finiteTensorFixedLine, Functor.mapIso, Iso.trans]
  simpa only [Category.assoc] using h

end WeilConjectures.PurityFiniteSetting
