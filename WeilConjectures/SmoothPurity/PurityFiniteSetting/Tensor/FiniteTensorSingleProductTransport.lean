/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle

/-! # Transport of ordinary binary product squares to degree-zero derived objects

Source: Stacks Project Tags 06YY, 07A4 and 0FPT; finite reduction of purity Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- The scalar/single comparison intertwines the ordinary and derived binary tensor maps.
Source: Stacks Project Tags 06YY, 07A4 and 0FPT; parent Step 5, last sentence.
(blueprint: lem-pur-finite-tensor-single-product-transport).
Proof: use uniqueness of the normalized core to identify finiteTensorCore with the
constructed finiteScalarMonoidalModel, whose representative equation holds on all
cochain complexes. Replace each scalar/single adjunct by its representative formula
using purityAdjunctionSingleMap_eq_representative. Expand cupSingleTensorMap into
the single/cochain identifications, localization tensor map and ordinary single
complex tensor isomorphism. Apply the full representative equation to the two
single complexes. The cochain scalar tensor map specializes in degree zero to the
ordinary oplax tensor map: use the bifunctor comparison on a single complex and
the exact single/mapHomologicalComplex isomorphism. Naturality moves these single
isomorphisms through the localization tensorator. Cancel the single/cochain
identifications and reassociate to obtain the equation. No scalar/single arrow is
inverted, so the argument requires neither flat sheaves nor a flat quotient. -/
theorem finiteTensorSingleProductTransport (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :
    let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
    let E := ProEtale.sheafExtendScalars φ T
    let U := sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)
    let F := P.finiteTensorReduction m hm hmn T
    let G := ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
      (P.finiteReductionRingHom m hm hmn) T
    let i := DerivedCategory.singleFunctor.{u + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0
    let j := DerivedCategory.singleFunctor.{u + 1}
      (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient)) 0
    let ad : E ⊣ U := ProEtale.sheafExtendScalarsAdjunction φ T
    let bd : F ⊣ G := P.finiteTensorAdjunction m hm hmn T
    let s := purityAdjunctionSingleMap E U F G i j ad bd
      (U.mapDerivedCategorySingleFunctor 0)
    F.map (ProEtale.cupSingleTensorMap M N) ≫ s (M ⊗ N) ≫
        j.map (Functor.OplaxMonoidal.δ E M N) =
      ((P.finiteTensorCore m hm hmn T).μIso (i.obj M) (i.obj N)).inv ≫
        (s M ⊗ₘ s N) ≫ ProEtale.cupSingleTensorMap (E.obj M) (E.obj N) := by sorry

end WeilConjectures.PurityFiniteSetting
