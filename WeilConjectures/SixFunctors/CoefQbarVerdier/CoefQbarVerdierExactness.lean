/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierShift
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Exactness component for the common-stage dual

Source: thm-coef-qbar-verdier, proof steps 3--4.
(blueprint: lem-coef-qbar-verdier-exactness-component)

The finite shift comparisons descend and carry distinguished triangles to
distinguished triangles. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open GeneralAlgebraicallyClosedCoefficients (Stage)
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

/-- The descended dual is exact for the prescribed triangulation.
Source: thm-coef-qbar-verdier, proof steps 3--4.
(blueprint: lem-coef-qbar-verdier-exactness-component)

Proof: take the shift-coherent structures from descended_shift_compatibility.
Apply distinguished_iff to the unopposite triangle. The counit of
triangleOpEquivalence and its compatibility with the finite inclusion exhibit
the original triangle as an included finite opposite distinguished triangle.
Apply its finite exact dual followed by the exact stage inclusion. The image
under the descended dual is isomorphic to this distinguished triangle by
mapTriangleCompIso and mapTriangleIso for descendedComparison; the latter is
available precisely because of the shift-coherence hypothesis. Isomorphism
closure gives the required result with exactly the prescribed connecting map. -/
theorem descended_exactness (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    ∃ s : (descendedDual D l hl Ω X F hF).CommShift ℤ,
      ∀ T : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ,
        T ∈ distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ →
        Triangle.mk ((descendedDual D l hl Ω X F hF).map T.mor₁)
          ((descendedDual D l hl Ω X F hF).map T.mor₂)
          ((descendedDual D l hl Ω X F hF).map T.mor₃ ≫
            (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω X) := by
  obtain ⟨s, ht⟩ := descended_shift_compatibility D l hl Ω X F hF
  let := s
  refine ⟨s, ?_⟩
  intro T hT
  let P := generalAlgebraicallyClosedConstructibleCategory l Ω X
  obtain ⟨E, U, hU, ⟨e⟩⟩ :=
    (GeneralAlgebraicallyClosedCoefficients.distinguished_iff _).1
      (unop_distinguished T hT)
  obtain ⟨t, ht, hc⟩ := ht E
  let V : Pᵒᵖ ⥤ P := descendedDual D l hl Ω X F hF
  let J : Stage l Ω X E ⥤ P := GeneralAlgebraicallyClosedCoefficients.inclusion E
  let d : (Stage l Ω X E)ᵒᵖ ⥤ Stage l Ω X E := (F.datum E).dual
  let : V.CommShift ℤ := s
  let : d.CommShift ℤ := t
  let : d.IsTriangulated := ht
  let jshift : J.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
  let oshift : J.op.CommShift ℤ :=
    @Pretriangulated.Opposite.commShiftFunctorOpInt _ _ _ _ _ _ J jshift
  let cA : (d ⋙ J).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ d J ℤ _ _ _ _ t jshift
  let cB : (J.op ⋙ V).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ J.op V ℤ _ _ _ _ oshift s
  let r : d ⋙ J ≅ J.op ⋙ V := descendedComparison D l hl Ω X F hF E
  let : @NatTrans.CommShift _ _ _ _ _ _ r.hom ℤ _ _ _ cA cB := hc
  let Uop := (triangleOpEquivalence (Stage l Ω X E)).functor.obj (op U)
  let eT : T ≅ J.op.mapTriangle.obj Uop :=
    ((triangleOpEquivalence P).counitIso.app T).symm ≪≫
      (triangleOpEquivalence P).functor.mapIso e.op.symm ≪≫
      J.mapTriangleOpCompTriangleOpEquivalenceFunctorApp U
  have hfinite := J.map_distinguished _
    (d.map_distinguished Uop (op_distinguished U hU))
  let eV : V.mapTriangle.obj T ≅
      J.mapTriangle.obj (d.mapTriangle.obj Uop) :=
    V.mapTriangle.mapIso eT ≪≫
      ((Functor.mapTriangleCompIso J.op V).app Uop).symm ≪≫
      ((Functor.mapTriangleIso r).app Uop).symm ≪≫
      (Functor.mapTriangleCompIso d J).app Uop
  exact isomorphic_distinguished _ hfinite _ eV

end WeilConjectures.CoefQbarVerdier
