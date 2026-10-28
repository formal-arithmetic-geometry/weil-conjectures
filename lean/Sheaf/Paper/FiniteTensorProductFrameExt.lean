/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.FiniteTensorReductionData

/-! # Detection of tensor maps on coherent finite signed frames

Source: finite-reduction proof Step 2 and Stacks Project, Modules on Sites,
Sections 03EK and 04TT.
(blueprint: lem-pur-finite-tensor-product-frame-ext)

The frame and section definitions are relocated unchanged from FiniteSignedTwistProducts
so that the local sheaf arguments do not depend on the product they construct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

/-- A coherent signed frame, formed before specializing the coefficient ring or line.
Positive bases are ordered tensors; negative bases evaluate to one.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
structure FiniteTensorLineFrame (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L : proEtaleRingModules T R) (V : T.ProEt) where
  basis : ∀ r : ℤ, Module.Basis (Fin 1) (R.obj.obj (Opposite.op V))
    ((coefficientTwistLine T L r).val.obj (Opposite.op V))
  zero : basis 0 0 = (1 : R.obj.obj (Opposite.op V))
  positive : ∀ j : ℕ, basis (j + 2) 0 =
    SheafOfModules.siteSheafTensorTmul (A := R)
      (coefficientTwistLine T L (j + 1)) L (Opposite.op V)
      (basis (j + 1) 0) (basis 1 0)
  negative : ∀ j : ℕ,
    ((basis (Int.negSucc j) 0).app (Opposite.op (Over.mk (𝟙 V)))) (basis (j + 1) 0) =
      (1 : R.obj.obj (Opposite.op V))

/-- The coherent frame of exactly the prescribed integral-reduced finite line.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
abbrev FiniteTensorFrame (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt) :=
  FiniteTensorLineFrame T (proEtaleConstantRing T P.Ring) (P.finiteTensorFirstLine T) V

/-- The basis vector of a coherent signed frame, with its section module fixed.
Source: blueprint proof Steps 5 and 8
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorFrameBasis (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt)
    (b : P.FiniteTensorFrame T V) (r : ℤ) :
    (P.finiteTensorLine T r).val.obj (Opposite.op V) :=
  b.basis r 0

/-- The canonical local-section realization, using its scalar unit and counit.
Source: Stacks 00YV, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V)) :=
  ((sfIntrinsicModuleEquivalence T P.Ring).counitIso.hom.app
    (P.finiteTensorLine T r)).val.app (Opposite.op V)
      (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T r) (Opposite.op V) x)

/-- The ordinary sheaf pure tensor, before passing to degree-zero complexes.
Source: Stacks 03EK, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSectionTmul (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r t : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
    (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)) :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} P.Coefficient))
      (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t)).app (Opposite.op V)
        (x ⊗ₜ[P.Coefficient] y)

/-- Maps out of a tensor of signed lines are detected on coherent frame products.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, invertible twists;
Stacks Project, sites-modules.tex, Section tensor-product and Section invertible.
(blueprint: lem-pur-finite-tensor-product-frame-ext).
Proof: trivialize the first line on a pro-etale covering sieve. Ordered powers
of its generator and their evaluation duals give a coherent frame on each member
and every further restriction. The scalar realization unit and counit are
bijections on sections. Under the intrinsic tensor comparison, the product of
two frame vectors is a basis of the tensor line. The hypothesis therefore
identifies the maps on that generator. Intrinsic module linearity identifies
all its multiples. Sections of a sheaf tensor locally lift to finite sums of
pure tensors, so the two maps agree after restriction to a covering sieve.
Separatedness of the target gives equality of sections before restriction;
faithfulness of the realization equivalence gives equality of sheaf maps.
At zero degrees the generator is one; opposite signs use the dual basis.
The same argument covers the zero ring and empty site objects. -/
theorem finiteTensorSheafProduct_frame_ext (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t s : ℤ)
    (f g : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T s)
    (h : ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T r V x = e.basis r 0 →
      P.finiteTensorSection T t V y = e.basis t 0 →
      P.finiteTensorSection T s V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
      P.finiteTensorSection T s V
        (g.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y))) :
    f = g := by sorry

end WeilConjectures.PurityFiniteSetting
