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
(blueprint: lem-pur-finite-tensor-product-map-isIso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- A normalized ordinary signed product morphism is locally a basis isomorphism.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, invertible twists;
Stacks Project, sites-modules.tex, Section invertible and Lemma constructions-invertible.
(blueprint: lem-pur-finite-tensor-product-map-isIso).
Proof: on a cover trivializing the first line, take its ordered-power and dual
frames. Realization identifies their ordinary representatives with the same
intrinsic sections. The tensor comparison identifies the product of the two
frame vectors with the basis of the tensor line. The hypothesis says that f
sends this basis to the basis of the sum-degree line. In these charts f is the
identity of the coefficient unit, hence invertible. The inverses agree on overlaps
because they are inverses of the same morphism, so they glue to a two-sided inverse.
The equivalence with fixed-scalar sheaves reflects this isomorphism. This works
for arbitrary signs, including zero and opposite signs, because the negative
frames are evaluation-dual bases. No uniqueness of product morphisms or preexisting
signed product is used. Empty charts and the zero ring have the unique inverse. -/
theorem finiteTensorSheafProductMap_isIso (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t : ℤ)
    (f : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T (r + t))
    (hf : ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T r V x = e.basis r 0 →
      P.finiteTensorSection T t V y = e.basis t 0 →
      P.finiteTensorSection T (r + t) V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
          e.basis (r + t) 0) :
    IsIso f := by sorry

end WeilConjectures.PurityFiniteSetting
