/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.Paper.ProjectionMateExact
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift

/-!
# The ringed projection mate and shifts of the direct-image input

Source: Stacks Project, Cohomology on Sites, Tags 0B56 and 07A4;
Derived Categories, Tag 0A8D. The first-variable mate calculation is assembled
in the DAG proof (blueprint: lem-sfb-ringed-projection-first-shift).
-/

@[expose] public section

universe u w

set_option autoImplicit false
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Pretriangulated

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false in
private def projectionTriangleMorphism
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (pi : F ⟶ G) [NatTrans.CommShift pi ℤ] (T : Triangle C) :
    F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := pi.app T.obj₁
  hom₂ := pi.app T.obj₂
  hom₃ := pi.app T.obj₃
  comm₁ := pi.naturality T.mor₁
  comm₂ := pi.naturality T.mor₂
  comm₃ := by
    change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
      (shiftFunctor D (1 : ℤ)).map (pi.app T.obj₁) =
      pi.app T.obj₃ ≫ (G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
    rw [Category.assoc, NatTrans.shift_app_comm pi (1 : ℤ) T.obj₁,
      pi.naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical projection mate is a transformation of exact functors in its
first variable, including the connecting square on distinguished triangles.
Source: Stacks Project, Tags 0B56, 07A4 and 0A8D
(blueprint: lem-sfb-ringed-projection-first-shift).

The corners and their models are the small ringed sites and ordinary K-flat
unbounded derived tensors of `lem-weil-pbc-ringed-projection-mate-exact`.
`e.left`, `e.right` and `e.derivedAdjunction` are its derived adjunction. The
normalizations `MateCanonicalShifts` and shift compatibility of `e.epsilon`
specify the canonical tensor and pullback shifts. Compatibility of the derived
adjunction specifies the unique compatible right-adjoint shifts, as in
`lem-weil-pbc-adjunction-shift-compatibility-unique`. No projection mate is
asserted to be invertible.

Proof:
1. Use `lem-weil-pbc-ringed-projection-mate-exact` for the normalized tensor
shifts, canonical pullback shifts, tensor exactness and canonical tensor comparison.
`lem-weil-pbc-ringed-topoi-derived-pullback` gives exactness of U. The unique
compatible shift on R has shift-compatible unit and counit by
`lem-weil-pbc-adjunction-shift-compatibility-unique`; R is exact by
`lem-sf-triangulated-right-adjoint`.
2. Fix P. Compose R with tensoring on the right by P to obtain F; compose
right tensoring by UP with R to obtain G. Both are exact. The composite shifts
are sF(K) = (rK tensor 1) followed by the tensor shift, and sG(K) = R of the
tensor shift followed by r. These are the coherent composite structures of
`lem-weil-pbc-commshift-nattrans-comp-whisker`.
3. Set betaK = mu(RK,P) followed by counitK tensor identity. By
`lem-weil-pbc-adjunction-of-natural-bijection`, its adjunct is the unit at F(K)
followed by R(betaK). This is exactly `derivedProjectionFormulaMate`.
Naturality in K is supplied by `lem-weil-pbc-ringed-projection-mate-exact`.
4. Apply naturality of mu at rK and then its first-factor shift square from
`lem-weil-pbc-ringed-projection-mate-exact`. Their composite identifies mu on
R(K[1]) with shifted mu on RK, using the composite shift on UR.
5. Substitute counit(K[1]) = sUR(K) followed by counitK[1], from
`lem-weil-pbc-adjunction-shift-compatibility-unique`. Naturality of the tensor
shift at counitK then gives beta(K[1]) followed by the tensor shift equal to
the composite shift on UF(K) followed by betaK[1].
6. Write piK = unit(FK) followed by R(betaK). Use step 5, naturality of r at
betaK, and naturality of the unit at sF(K). Unit shift compatibility reduces
the result to sF(K) followed by piK[1]. Thus pi(K[1]) followed by sG(K)
equals sF(K) followed by piK[1]; integer coherence gives `CommShift`.
7. For a distinguished triangle, exactness gives distinguished image triangles.
The first two squares for the components pi are naturality. Naturality at the
connecting arrow followed by step 6 gives the third square. These are precisely
the equations for a triangle morphism in `def-weil-pbc-triangles-with-shift`. -/
theorem ringedProjectionFirstShift
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) :
    ∃ (_ : (Functor.curryObj Y.tensor).CommShift₂Int)
      (_ : (Functor.curryObj X.tensor).CommShift₂Int)
      (_ : e.left.CommShift ℤ) (_ : e.right.CommShift ℤ),
      a.MateCanonicalShifts ∧ b.MateCanonicalShifts ∧
      NatTrans.CommShift e.epsilon ℤ ∧ e.derivedAdjunction.CommShift ℤ ∧
      ∀ P : Y.mateDerived,
        (e.right ⋙ (Functor.curryObj Y.tensor).flip.obj P).IsTriangulated ∧
        ((Functor.curryObj X.tensor).flip.obj (e.left.obj P) ⋙ e.right).IsTriangulated ∧
        ∃ pi : e.right ⋙ (Functor.curryObj Y.tensor).flip.obj P ⟶
            (Functor.curryObj X.tensor).flip.obj (e.left.obj P) ⋙ e.right,
          (∀ K : X.mateDerived, pi.app K =
            derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
              (e.tensorComparison a b) K P) ∧
          NatTrans.CommShift pi ℤ ∧
          (∀ K : X.mateDerived,
            pi.app (K⟦(1 : ℤ)⟧) ≫
                (((Functor.curryObj X.tensor).flip.obj (e.left.obj P) ⋙
                  e.right).commShiftIso (1 : ℤ)).hom.app K =
              ((e.right ⋙ (Functor.curryObj Y.tensor).flip.obj P).commShiftIso
                (1 : ℤ)).hom.app K ≫ (shiftFunctor Y.mateDerived (1 : ℤ)).map (pi.app K)) ∧
          (∀ T : Triangle X.mateDerived, T ∈ distTriang X.mateDerived →
            ∃ m : (Functor.mapTriangle
                (e.right ⋙ (Functor.curryObj Y.tensor).flip.obj P)).obj T ⟶
                (Functor.mapTriangle
                  ((Functor.curryObj X.tensor).flip.obj (e.left.obj P) ⋙ e.right)).obj T,
              m.hom₁ = pi.app T.obj₁ ∧ m.hom₂ = pi.app T.obj₂ ∧
                m.hom₃ = pi.app T.obj₃) := by
  obtain ⟨hY, hX, hL, hR, ha, hb, heps, hleft, hright, hadj, hYtri, hXtri, hrest⟩ :=
    ringedProjectionMateExact e a b
  let _ := hY
  let _ := hX
  let _ := hL
  let _ := hR
  let _ := hadj
  refine ⟨hY, hX, hL, hR, ha, hb, heps, hadj, ?_⟩
  intro P
  have hYP := hYtri P
  have hXP := hXtri (e.left.obj P)
  let _ := hYP.2
  let _ := hXP.2
  have hF : (e.right ⋙ (Functor.curryObj Y.tensor).flip.obj P).IsTriangulated := by
    infer_instance
  have hG : ((Functor.curryObj X.tensor).flip.obj (e.left.obj P) ⋙ e.right).IsTriangulated := by
    infer_instance
  let φ : (Functor.postcompose₂.obj e.left).obj (Functor.curryObj Y.tensor) ⟶
      (((Functor.whiskeringLeft₂ X.mateDerived).obj e.left).obj e.left).obj
        (Functor.curryObj X.tensor) :=
    Functor.curry.map (e.tensorComparison a b).hom ≫
      (Functor.curryObjProdComp e.left e.left X.tensor).hom
  let pi := e.derivedAdjunction.rightAdjointProjectionMapFlipApp
      (T_C := Functor.curryObj X.tensor) (T_D := Functor.curryObj Y.tensor) φ P
  have hpi : ∀ K : X.mateDerived, pi.app K =
      derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
        (e.tensorComparison a b) K P := by
    intro K
    dsimp [pi, φ, CategoryTheory.Adjunction.rightAdjointProjectionMapFlipApp,
      derivedProjectionFormulaMate]
  have hφapp (U : Y.mateDerived) :
      (CategoryTheory.Adjunction.comparisonFlipApp φ P).app U =
        (e.tensorComparison a b).hom.app (U, P) := by
    change (e.tensorComparison a b).hom.app (U, P) ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hφ : NatTrans.CommShift (CategoryTheory.Adjunction.comparisonFlipApp φ P) ℤ := by
    apply NatTrans.CommShift.of_core
    intro n
    constructor
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      hφapp, Functor.commShiftIso_comp_hom_app, Category.assoc]
    exact (hrest.2.1 n K P).symm
  have hcomm : NatTrans.CommShift pi ℤ := by
    apply CategoryTheory.Adjunction.commShift_rightAdjointProjectionMapFlipApp
  refine ⟨hF, hG, pi, hpi, hcomm, ?_, ?_⟩
  · intro K
    exact (NatTrans.shift_app_comm pi (1 : ℤ) K).symm
  · intro T _
    exact ⟨projectionTriangleMorphism pi T, rfl, rfl, rfl⟩

end SheafOfModules
