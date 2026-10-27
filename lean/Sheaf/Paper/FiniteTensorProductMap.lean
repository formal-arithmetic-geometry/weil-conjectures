/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.FiniteTensorProductFrameExt

/-! # Normalized ordinary finite signed product maps

Source: finite-reduction proof Step 2; Stacks Project, Modules on Sites,
Sections 03EK and 04TT.
(blueprint: lem-pur-finite-tensor-product-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- The local signed multiplication rule glues to an ordinary sheaf morphism.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, invertible twists;
Stacks Project, sites-modules.tex, Section tensor-product and Section invertible.
(blueprint: lem-pur-finite-tensor-product-map).
Proof: choose a pro-etale cover trivializing the finite first line. Its ordered
powers, the coefficient unit at zero, and evaluation-dual powers in negative
degrees give coherent frames. On such a chart define the bilinear rule
(a e_r, b e_t) to map to ab e_(r+t). For a change of the first generator by a
unit u, induction gives e_j mapped to u^j e_j for every integer j; for negative
j this follows by evaluation on the positive basis. Thus the local bilinear
rules agree on overlaps since u^r u^t = u^(r+t). Sheaf descent glues them.
The tensor universal property produces a morphism of intrinsic module sheaves.
Transport it through the canonical scalar realization and its tensor comparison.
Their section formulas give exactly the displayed normalization for every frame,
not just the frames used to construct the map. Only existence of a morphism
is asserted here: neither invertibility nor uniqueness is assumed. Zero degrees
use multiplication by the coefficient unit; opposite signs use evaluation.
Zero rings and empty objects satisfy the same bilinear and sheaf universal properties. -/
theorem exists_finiteTensorSheafProductMap (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t : ℤ) :
    ∃ f : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T (r + t),
      ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T r V x = e.basis r 0 →
      P.finiteTensorSection T t V y = e.basis t 0 →
      P.finiteTensorSection T (r + t) V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
          e.basis (r + t) 0 := by sorry

end WeilConjectures.PurityFiniteSetting
