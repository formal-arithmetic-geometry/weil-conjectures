module

public import Sheaf.Paper.EtaleSystemProjectionData
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-! # Unbounded compact support and projection on strict étale systems

Source: Stacks Tags 0B56, 0F0G, 0GL1 and 0GL6; the ordinary strict-system
refinement of the integral exceptional-adjoint argument
(blueprint: def-coef-etale-system-tensor-evaluation).

All presentations below are conclusion data. The coefficient index n means n+1.
Tensor comparisons are normalized on ordinary pure tensors and signed total complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.SemilinearSections
open scoped TensorProduct

namespace AlgebraicGeometry.Etale.SystemCompactSupport
open SystemProjection

/-- The existing ordinary-derived calculus, specialized to these constant ring sheaves.
Source: Zheng 4.1, 4.10 (blueprint: def-coef-etale-system-tensor-evaluation). -/
abbrev Calculus (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :=
  Data.{u + 1, u, u + 1} W.smallEtaleTopology (coefficients W B) (transitions W B)

/-- The fixed-ring sheaf tensor's actual map on local pure tensors.
Source: sheafification tensor adjunction, Stacks 03EL
(blueprint: def-coef-etale-system-tensor-evaluation). -/
def fixedTensorSection (W : Scheme.{u}) (A : CommRingCat.{u + 1})
    (M N : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))
    (U : W.Etaleᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U) :
    (M ⊗ N).obj.obj U :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf W.smallEtaleTopology
    (ModuleCat.{u + 1} A)) M N).app U).hom (x ⊗ₜ[A] y)

/-- Termwise exact evaluation, using its recorded additive proof.
Source: Stacks 05RU (blueprint: def-coef-etale-system-tensor-evaluation). -/
def evalComplex {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {n : ℕ}
    (e : Evaluation W B n) :=
  letI := e.additive
  (level W B n).mapHomologicalComplex (.up ℤ)

/-- The canonical exact-evaluation localization comparison.
Source: Stacks 05RU (blueprint: def-coef-etale-system-tensor-evaluation). -/
def evalFactors {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {n : ℕ}
    (e : Evaluation W B n) :=
  letI := e.additive
  letI := e.limits
  letI := e.colimits
  (level W B n).mapDerivedCategoryFactors

set_option backward.isDefEq.respectTransparency true in
/-- Normalized tensor evaluation into the ordinary finite-coefficient category.
The ordinary map is fixed on all pure tensors, and the derived map is fixed before
localization by its signed total-complex summands.
Source: Stacks 03EL, 06YU, 07A4
(blueprint: def-coef-etale-system-tensor-evaluation). -/
structure TensorEvaluationData (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1})
    (A : Calculus W B) (n : ℕ) (e : Evaluation W B n) where
  ordinary : ∀ M N : Modules W B,
    (level W B n).obj M ⊗ (level W B n).obj N ≅
      (level W B n).obj (ordinaryTensor.{u + 1, u, u + 1}
        (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
        (rings W B) M N)
  pure : ∀ (M N : Modules W B) (U : W.Etaleᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))),
    ((ordinary M N).hom.hom.app U).hom
        (fixedTensorSection W (B.obj (op n)) ((level W B n).obj M)
          ((level W B n).obj N) U x y) =
      tensorSection.{u + 1, u, u + 1}
        (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
        (rings W B) M N (op (n, U.unop)) x y
  tensor : A.closed.tensor ⋙ e.E ≅ (e.E.prod e.E) ⋙
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} (B.obj (op n))) W)
  chain : ∀ P Q : CochainComplex (Modules W B) ℤ,
    (evalComplex e).obj P ⊗
        (evalComplex e).obj Q ⟶
      (evalComplex e).obj
        ((totalTensor.{u + 1, u, u + 1}
          (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
          (rings W B)).obj (P, Q))
  summand : ∀ (P Q : CochainComplex (Modules W B) ℤ) (p q k : ℤ) (h : p + q = k),
    HomologicalComplex.ιTensorObj
        ((evalComplex e).obj P)
        ((evalComplex e).obj Q) p q k h ≫
          (chain P Q).f k =
      (ordinary (P.X p) (Q.X q)).hom ≫
        (level W B n).map (tensorSummand.{u + 1, u, u + 1}
          (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
          (rings W B) P Q p q k h)

end AlgebraicGeometry.Etale.SystemCompactSupport
