/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Unit contraction of the reindexing tensor square

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-unit-contraction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- The specialized tensor square at the coefficient unit. -/
def unitTensorSquare
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left) : Prop := by
  letI := (C.data T).units
  letI := (C.data U).units
  exact
    (derivedPull l T.base.left g.hom (C.ring T U g)).map
          ((C.data U).tensor.tensor.hom.app
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left,
             pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)) ≫
        (C.comparison T U g).inv.app
          ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left,
             pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)) ≫
          (ordinary l T.base.left (C.data T).realization).map
            (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)).hom =
        (C.pullTensor T U g).tensor.hom.app
          ((ordinary l U.base.left (C.data U).realization).obj
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left),
           (ordinary l U.base.left (C.data U).realization).obj
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)) ≫
          (C.data T).tensor.closed.tensor.map (Prod.mkHom
            ((C.comparison T U g).inv.app
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))
            ((C.comparison T U g).inv.app
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))) ≫
          (C.data T).tensor.tensor.hom.app
            ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left),
             (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))

/-- Contract the tensor square at the coefficient unit.  The proof expands the
reindexing representative equation on the degree-zero unit complex, uses
`reindexUnitSections`, and then cancels the tensor and ordinary unitors. -/
theorem reindexing_tensor_unit_contraction
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (h_tensor : unitTensorSquare l D C T U g) :
    letI := (C.data T).units
    letI := (C.data U).units
    (derivedPull l T.base.left g.hom (C.ring T U g)).map (C.data U).tensor.unit.hom ≫
      (C.comparison T U g).inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (C.unit_spec T U g).exists.choose.hom =
    (pullUnit l T.base.left g.hom (C.pullTensor T U g)).hom ≫
      (C.data T).tensor.unit.hom := by
  sorry

end WeilConjectures.AdicQbarRealization
