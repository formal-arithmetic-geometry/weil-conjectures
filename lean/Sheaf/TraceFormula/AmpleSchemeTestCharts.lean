/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-!
# Geometric scheme-test charts

Source: Stacks, Spaces, Tags 02X2 and 025Y; Topologies on Spaces, Tag 041F
(blueprint: lem-trf-ample-scheme-test-charts).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme pullback chart, with its actual structure map to the fixed base.
Source: Stacks, Spaces, Tag 02X2
(blueprint: lem-trf-ample-scheme-test-charts). -/
noncomputable def ampleTestChartOver {S : Scheme.{u}} {A B C : Over S}
    (p : A ⟶ C) (q : B ⟶ C) : Over S :=
  Over.mk (Limits.pullback.fst p.left q.left ≫ A.hom)

/-- The first projection of the explicit scheme pullback chart.
Source: Stacks, Spaces, Tag 02X2
(blueprint: lem-trf-ample-scheme-test-charts). -/
noncomputable def ampleTestChartFst {S : Scheme.{u}} {A B C : Over S}
    (p : A ⟶ C) (q : B ⟶ C) : ampleTestChartOver p q ⟶ A :=
  Over.homMk (Limits.pullback.fst p.left q.left) rfl

/-- The second projection of the explicit scheme pullback chart.
Source: Stacks, Spaces, Tag 02X2
(blueprint: lem-trf-ample-scheme-test-charts). -/
noncomputable def ampleTestChartSnd {S : Scheme.{u}} {A B C : Over S}
    (p : A ⟶ C) (q : B ⟶ C) : ampleTestChartOver p q ⟶ B :=
  Over.homMk (Limits.pullback.snd p.left q.left) (by
    change Limits.pullback.snd p.left q.left ≫ B.hom =
      Limits.pullback.fst p.left q.left ≫ A.hom
    rw [← q.w, ← p.w]
    exact (Limits.pullback.condition_assoc C.hom).symm)

/-- Geometric charts for an arbitrary scheme base change. There is no module or
ampleness data in this structure. The underlying source schemes are explicit scheme
pullbacks, so the relative-ampleness base-change theorem applies literally.
Source: Stacks, Spaces, Tags 02X2 and 025Y; Topologies on Spaces, Tag 041F
(blueprint: lem-trf-ample-scheme-test-charts). -/
structure AmpleSchemeTestCharts {S : Scheme.{u}} {F Y : AlgebraicSpace S}
    (f : F ⟶ Y) {I : Type v} (Yᵢ : I → Y.EtaleSite) (Fᵢ : I → F.EtaleSite)
    (pᵢ : ∀ i : I, (Fᵢ i).obj.left ⟶ (Yᵢ i).obj.left)
    (T : Over S) (h : yoneda.obj T ⟶ Y.obj.obj) where
  X : AlgebraicSpace S
  toF : X ⟶ F
  toT : X.obj.obj ⟶ yoneda.obj T
  cartesian : IsPullback toF.hom.hom toT f.hom.hom h
  Tᵢ : I → Over S
  tY : ∀ i : I, Tᵢ i ⟶ (Yᵢ i).obj.left
  tT : ∀ i : I, Tᵢ i ⟶ T
  baseCartesian : ∀ i : I, IsPullback (yoneda.map (tY i)) (yoneda.map (tT i))
    (Yᵢ i).obj.hom h
  baseEtale : ∀ i : I, Etale (tT i).left
  baseSurjective : IsJointlySurjective (fun i : I ↦ yoneda.map (tT i))
  source : ∀ i : I, yoneda.obj (ampleTestChartOver (pᵢ i) (tY i)) ⟶ X.obj.obj
  sourceEtale : ∀ i : I, IsEtale (source i)
  sourceCartesian : ∀ i : I, IsPullback (source i)
    (yoneda.map (ampleTestChartSnd (pᵢ i) (tY i))) toT (yoneda.map (tT i))
  sourceToF : ∀ i : I, source i ≫ toF.hom.hom =
    yoneda.map (ampleTestChartFst (pᵢ i) (tY i)) ≫ (Fᵢ i).obj.hom
  sourceSurjective : IsJointlySurjective source
  etale_toF : IsEtale h → IsEtale toF.hom.hom

/-- Form the geometric charts, using the explicit scheme pullbacks for the sources.
Source: Stacks, Spaces, Tags 02X2 and 025Y; Topologies on Spaces, Tag 041F
(blueprint: lem-trf-ample-scheme-test-charts).

Proof: form the sheaf fibre product F ×_Y T; closure under fibre products makes it
an algebraic space. Represent each Y_i ×_Y T using representable etaleness of Y_i → Y;
these are the T_i and their projections to T are etale. Pullback of the given jointly
surjective family gives joint surjectivity. Take X_i to be the actual scheme pullback
F_i ×_{Y_i} T_i. Map it to F ×_Y T by its projections to F_i → F and T_i → T.
Pasting the original and base-change cartesian squares shows X_i = X ×_T T_i.
Its projection to X is consequently representable etale, and the source family is
jointly surjective by stability under base change. If h is etale, the first projection
of F ×_Y T is etale by the same stability. These arguments include the empty cover:
its joint-surjectivity hypothesis forces the target to have no points. -/
theorem exists_ampleSchemeTestCharts
    {S : Scheme.{u}} {F Y : AlgebraicSpace S} (f : F ⟶ Y)
    (I : Type v) (Yᵢ : I → Y.EtaleSite) (Fᵢ : I → F.EtaleSite)
    (pᵢ : ∀ i : I, (Fᵢ i).obj.left ⟶ (Yᵢ i).obj.left)
    (hcover : IsJointlySurjective (fun i : I ↦ (Yᵢ i).obj.hom))
    (hpb : ∀ i : I, IsPullback (Fᵢ i).obj.hom (yoneda.map (pᵢ i))
      f.hom.hom (Yᵢ i).obj.hom)
    (T : Over S) (h : yoneda.obj T ⟶ Y.obj.obj) :
    Nonempty (AmpleSchemeTestCharts f Yᵢ Fᵢ pᵢ T h) := by sorry

end AlgebraicGeometry.AlgebraicSpace
