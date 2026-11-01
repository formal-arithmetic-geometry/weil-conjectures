/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionUnshiftedPullbackCube
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionPullbackComparisonShift

/-! # Finite scalar extension and the shifted ordinary pullback square

Source: blueprint finite-reduction-of-purity proof, Steps 2 and 4.
(blueprint: lem-pur-finite-reduction-shifted-pullback-cube)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem shifted_cube
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (F : C ⥤ C') (Q : C ⥤ D) (R : C' ⥤ D') (G : D ⥤ D')
    [F.CommShift ℤ] [Q.CommShift ℤ] [R.CommShift ℤ] [G.CommShift ℤ]
    (e : F ⋙ R ≅ Q ⋙ G) {E : C} {L : C'} {M : D} {N : D'}
    (s : F.obj E ⟶ L) (a : R.obj L ⟶ N) (p : Q.obj E ⟶ M) (t : G.obj M ⟶ N)
    (r : ℤ)
    (hcube : R.map s ≫ a = e.hom.app E ≫ G.map p ≫ t)
    (hshift : R.map ((F.commShiftIso r).hom.app E) ≫
      (R.commShiftIso r).hom.app (F.obj E) ≫ (e.hom.app E)⟦r⟧' =
      e.hom.app (E⟦r⟧) ≫ G.map ((Q.commShiftIso r).hom.app E) ≫
        (G.commShiftIso r).hom.app (Q.obj E)) :
    R.map ((F.commShiftIso r).hom.app E) ≫ R.map (s⟦r⟧') ≫
      (R.commShiftIso r).hom.app L ≫ a⟦r⟧' =
    e.hom.app (E⟦r⟧) ≫ G.map ((Q.commShiftIso r).hom.app E ≫ p⟦r⟧') ≫
      (G.commShiftIso r).hom.app M ≫ t⟦r⟧' := by
  calc
    _ = R.map ((F.commShiftIso r).hom.app E) ≫
        (R.commShiftIso r).hom.app (F.obj E) ≫ (R.map s ≫ a)⟦r⟧' := by
      simp only [Functor.map_comp]
      rw [Functor.commShiftIso_hom_naturality_assoc]
    _ = R.map ((F.commShiftIso r).hom.app E) ≫
        (R.commShiftIso r).hom.app (F.obj E) ≫
          (e.hom.app E ≫ G.map p ≫ t)⟦r⟧' := by rw [hcube]
    _ = (R.map ((F.commShiftIso r).hom.app E) ≫
        (R.commShiftIso r).hom.app (F.obj E) ≫ (e.hom.app E)⟦r⟧') ≫
          (G.map p)⟦r⟧' ≫ t⟦r⟧' := by
      simp only [Functor.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [hshift]
      simp only [Functor.map_comp, Category.assoc]
      rw [Functor.commShiftIso_hom_naturality_assoc]

private def comparisonNatIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P.finiteReductionPullback f ⋙ P.finiteReduction m hm hmn X ≅
      P.finiteReduction m hm hmn Y ⋙
        (P.finiteReductionSetting m hm).finiteReductionPullback f :=
  Functor.isoWhiskerRight (P.finiteReductionRawPullbackModel f).symm
      (P.finiteReduction m hm hmn X) ≪≫
    (Scheme.proEtaleReductionPullbackIso f
      (Scheme.proEtaleConstantRing Y P.Ring)
      (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing X P.Ring)
      (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison f P.Ring)
      (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn f)).symm ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn Y)
      ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f)

/-- Scalar extension respects the ordinary inverse-image square with an arbitrary shift.
There is no Tate line, root chart, smoothness assumption or exceptional inverse image.
Source: blueprint `thm-pur-finite-reduction-of-purity`, Steps 2 and 4;
Stacks 0D6D and 06YY
(blueprint: lem-pur-finite-reduction-shifted-pullback-cube).

Proof: compare the two composites of ordinary inverse images and exact restriction
of scalars. The section maps are the same pullback of a section with the same scalar
restriction; the two compositors are induced by the same fibre-product association.
Localizing this identity gives the derived restriction cube. Transpose its coefficient
edges through extension/restriction adjunctions. The triangle identities identify the
result with the coefficient/pullback comparisons in the statement. The section-unit
normalization of the raw pullback models identifies the geometric square with the
realization square used here. Exact restriction and inverse image commute termwise
with every integer shift. Scalar extension's shift is the adjoint of this exact shift,
so transposing the shifted restriction cube gives the displayed equation, including
its specified shift comparisons. Equivalently, first apply the unshifted cube and
then the shift compatibility of its coefficient mates. This uses derived extension,
not flatness of the quotient. Identity coefficient maps, empty schemes, zero objects
and shift zero satisfy the same formulas. -/
theorem finiteReduction_shiftedPullbackCube (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (r : ℤ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X').map
        (((P.finiteReductionPullback u).commShiftIso r).hom.app
          ((P.finiteReductionPullback f).obj K)) ≫
      (P.finiteReduction m hm hmn X').map
        ((P.finiteReductionPullbackSquare u f' f v sq K).hom⟦r⟧') ≫
      ((P.finiteReduction m hm hmn X').commShiftIso r).hom.app
        ((P.finiteReductionPullback f').obj ((P.finiteReductionPullback v).obj K)) ≫
      (P.finiteReductionPullbackComparison m hm hmn f'
        ((P.finiteReductionPullback v).obj K)).hom⟦r⟧' ≫
      (((P.finiteReductionSetting m hm).finiteReductionPullback f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom)⟦r⟧' =
    (P.finiteReductionPullbackComparison m hm hmn u
        (((P.finiteReductionPullback f).obj K)⟦r⟧)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (((P.finiteReduction m hm hmn X).commShiftIso r).hom.app
          ((P.finiteReductionPullback f).obj K) ≫
        (P.finiteReductionPullbackComparison m hm hmn f K).hom⟦r⟧') ≫
      (((P.finiteReductionSetting m hm).finiteReductionPullback u).commShiftIso r).hom.app
        (((P.finiteReductionSetting m hm).finiteReductionPullback f).obj
          ((P.finiteReduction m hm hmn Y).obj K)) ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullbackSquare u f' f v sq
        ((P.finiteReduction m hm hmn Y).obj K)).hom⟦r⟧' := by
  let e := comparisonNatIso P m hm hmn u
  have hs := P.finiteReduction_pullbackComparison_shift m hm hmn u r
    ((P.finiteReductionPullback f).obj K)
  have hc := finiteReduction_unshiftedPullbackCube P m hm hmn u f' f v sq K
  have he (L) : e.hom.app L = (P.finiteReductionPullbackComparison m hm hmn u L).hom := by
    rfl
  have h := shifted_cube (P.finiteReductionPullback u)
    (P.finiteReduction m hm hmn X) (P.finiteReduction m hm hmn X')
    ((P.finiteReductionSetting m hm).finiteReductionPullback u) e
    (P.finiteReductionPullbackSquare u f' f v sq K).hom
    ((P.finiteReductionPullbackComparison m hm hmn f'
      ((P.finiteReductionPullback v).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom)
    (P.finiteReductionPullbackComparison m hm hmn f K).hom
    ((P.finiteReductionSetting m hm).finiteReductionPullbackSquare u f' f v sq
      ((P.finiteReduction m hm hmn Y).obj K)).hom r hc (by
        simpa only [he, Category.assoc] using hs)
  simpa only [Functor.map_comp, Category.assoc, he] using h

end WeilConjectures.PurityFiniteSetting
