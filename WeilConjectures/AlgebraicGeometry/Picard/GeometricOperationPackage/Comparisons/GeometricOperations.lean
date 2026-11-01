/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.GeometricOperationPackage.GeometricComparisonData

/-! # Geometric operation packages

Source: Weil blueprint, sec-trace-formula/sk-d-six (blueprint: sk-d-six).
The canonical duality maps and component coherence complete the specified
comparison data on the given finite-coefficient operations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace GeometricOperationPackage

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ)
  (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)))

namespace Comparisons

variable {F l hl E n G} {A : ExceptionalAdjunctions F l hl E n G}
  (P : Comparisons F l hl E n G A)

/-- The canonical Kunneth--Verdier arrow, rather than a freely supplied comparison.
It is the tensor-Hom adjunct of reassociation, the pullback tensorator, pulled-back
evaluation, and the specified exceptional adjunct alpha.
Source: sk-d-six, final displayed composite (blueprint: sk-d-six). -/
def kunnethVerdier (X Y Z : TraceFormulaGeometricSpace F) (px : Z ⟶ X) (py : Z ⟶ Y)
    (h : ChosenCartesianSquare py.hom.hom.left px.hom.hom.left
      (TraceFormulaGeometricSpace.structureMap Y).hom.hom.left
      (TraceFormulaGeometricSpace.structureMap X).hom.hom.left)
    (M : Ctf F l E n X) (N : Ctf F l E n Y) :
    external px py M.obj ((P.dual Y).obj (op N.obj)) ⟶
      (traceFormulaFiniteInternalHom l E Z.obj.obj.left n).obj
        (op ((pull F l E n py).obj N.obj),
          ((exceptionalCtf F l hl E n G px).obj M).obj) :=
  (closed F l E n Z).transpose _ _ _
    (((closed F l E n Z).monoidal.associator ((pull F l E n px).obj M.obj)
      ((pull F l E n py).obj ((P.dual Y).obj (op N.obj)))
      ((pull F l E n py).obj N.obj)).hom ≫
    (closed F l E n Z).tensor.map
      (Prod.mkHom (𝟙 ((pull F l E n px).obj M.obj))
        (pullTensorIso F l E n py (P.monoidal py) ((P.dual Y).obj (op N.obj)) N.obj).hom) ≫
    (closed F l E n Z).tensor.map
      (Prod.mkHom (𝟙 ((pull F l E n px).obj M.obj))
        ((pull F l E n py).map (P.evaluation Y N.obj))) ≫
    (P.alpha X Y Z px py h M).hom)

end Comparisons
end GeometricOperationPackage

end WeilConjectures
