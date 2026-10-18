/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.BoundaryOrdinaryImages
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.A1QbarOpenClosedCohomology
import Sheaf.Paper.SfWeilSheafComplex

/-! # Boundary-supported maps to and from the shifted ordinary middle extension

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/
sk-d-dl-a1-setup/rem-dl-a1-conventions.md, final paragraph;
parent intermediate-extension argument, boundary-subobject/quotient step
(blueprint: lem-dl-a1-boundary-hom-vanishing).

All geometric arrows are in the actual finite-stage pair category underlying the
recorded common-stage heart. All Weil arrows are in its Frobenius fixed-pair category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Both Hom groups between i_*E and (j_*F)[1] vanish, geometrically and for the
induced Frobenius pairs. The existential shift-commutation structure supplies the
cohomological shift on fixed pairs; it is not a triangulation of their category.
Source: blueprint rem-dl-a1-conventions, final paragraph, and the boundary step of
lem-dl-a1-curve-intermediate-extension (blueprint: lem-dl-a1-boundary-hom-vanishing).

Proof, following the node:
1. The open-closed cohomology lemma lem-a1-qbar-open-closed-cohomology puts
A = j_*F and B = i_*E in the standard constructible heart, with j^*B = 0,
exact j^*, and the ordinary adjunction j^* ⊣ j_* with invertible counit.
The cohomological Frobenius pullback commutes with shifts, first on complexes at
a finite coefficient field and then after rationalization and common-stage descent.
2. Complete any δ : B → A[1] to a triangle A → M → B → A[1]. Extension closure
and clause (4) of lem-weil-heart-short-exact-triangles give the associated short
exact sequence in the standard heart.
3. Restrict it to U. Since j^*B = 0, j^*a is invertible. The adjoint of the
counit composed with (j^*a) inverse is a retraction r of a, by naturality of
the ordinary adjunction and injectivity of its Hom bijection.
4. Consecutive arrows in the twice-rotated triangle compose to zero, by
lem-weil-pbc-hom-into-triangle-exact. Thus a[1] ∘ δ = 0, and composing with
r[1] gives δ = 0.
5. Hom(A[1],B) = Hom(A,B[-1]) vanishes by ordinary t-structure orthogonality,
since A and B are in its heart.
6. The canonical ordinary images carry the adjunction-mate Frobenius structures.
Forgetting fixed-pair morphisms is faithful and preserves their underlying arrows.
Each of their two Hom sets therefore injects into its zero geometric Hom group;
the zero arrow commutes with Frobenius. No Frobenius structure is imposed on the
arbitrary geometric E, and no triangle of Weil pairs is used. -/
theorem boundaryHomVanishing
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c : MiddleExtensionCurve D) [GeometricallyConnected c.C.hom]
    (Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ c.C) [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (hcomp : IsCompl (Set.range c.j.left.base) (Set.range i₀.left.base))
    (F₀ : sfCommonStageWeilSheaf D l hl c.U Ω)
    (hF₀ : HasCommonStageLisseLattice l Ω (D.geometricFiber c.U).left F₀.obj.carrier) :
    ∃ sΦ : (sfCommonStageWeilFrobeniusPullback D l hl c.C Ω).CommShift ℤ,
      (∀ E : sfCommonStageHeart l (D.geometricFiber Z₀).left Ω,
        Subsingleton
          (((boundaryClosedPushforward D l hl Ω i₀).obj E).obj ⟶
            ((qbarCurveOrdinaryPushforward D l hl Ω c).obj
              ⟨F₀.obj.carrier, F₀.property⟩).obj⟦(1 : ℤ)⟧) ∧
        Subsingleton
          (((qbarCurveOrdinaryPushforward D l hl Ω c).obj
              ⟨F₀.obj.carrier, F₀.property⟩).obj⟦(1 : ℤ)⟧ ⟶
            ((boundaryClosedPushforward D l hl Ω i₀).obj E).obj)) ∧
      (∀ E₀ : sfCommonStageWeilSheaf D l hl Z₀ Ω,
        Subsingleton
          (boundaryOrdinaryWeilImage D l hl Ω i₀
              (boundaryClosedPushforward D l hl Ω i₀)
              (boundaryClosedAdjunction D l hl Ω i₀) E₀ ⟶
            boundaryWeilShift D l hl Ω c.C sΦ
              (boundaryOrdinaryWeilImage D l hl Ω c.j
                (qbarCurveOrdinaryPushforward D l hl Ω c)
                (qbarCurveOrdinaryAdjunction D l hl Ω c) F₀)) ∧
        Subsingleton
          (boundaryWeilShift D l hl Ω c.C sΦ
              (boundaryOrdinaryWeilImage D l hl Ω c.j
                (qbarCurveOrdinaryPushforward D l hl Ω c)
                (qbarCurveOrdinaryAdjunction D l hl Ω c) F₀) ⟶
            boundaryOrdinaryWeilImage D l hl Ω i₀
              (boundaryClosedPushforward D l hl Ω i₀)
              (boundaryClosedAdjunction D l hl Ω i₀) E₀)) := by
  sorry

end WeilConjectures
