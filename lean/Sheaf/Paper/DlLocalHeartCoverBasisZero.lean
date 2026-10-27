/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.DlLocallyConstructibleAdicHeart
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Cover vanishing on each finite-type basis open

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
local-heart construction in lem-dl-a1-local-heart-cover-defects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (T : Over (Spec (.of D.k₀)))

/-- A cartesian local object vanishing on a cover vanishes on every basis open.
Source: BS Proposition 6.8.14 and Remark 6.8.15; local-heart proof Step 8;
Stacks Tag 04TQ (blueprint: lem-dl-a1-local-heart-cover-basis-zero).

Proof: fix a basis open V and a geometric point of V. The cover contains its
underlying point in some U_i. Since T is locally of finite type over k0, choose
a separated finite-type basis neighbourhood W inside V intersect U_i through
which that point factors. The cartesian comparison identifies K_W with the
completed restriction of K_(U_i), which is zero. The normalized pullback-fibre
comparison identifies the geometric fibre of K_V at this point with that of K_W.
It is zero. Joint conservativity of geometric coefficient fibres on the bounded
common-stage standard heart gives K_V zero. Use the coefficient-model comparisons
to express these fibres on the literal sf heart, retaining the completed-section
normalization. This applies to every V and uses no finite subcover or coefficient
field shared by all opens. The empty scheme and empty cover cause no exception:
each basis open then has no geometric points and fibre conservativity gives zero. -/
theorem dlLocalHeartCoverBasisZero [LocallyOfFiniteType T.hom]
    (I : Type w) (U : I → DlAdicFiniteOpen D T) (hU : (⨆ i : I, (U i).val) = ⊤)
    (K : DlLocallyConstructibleAdicHeart D c T)
    (hK : ∀ i : I, IsZero ((dlAdicLocalEvaluation D c T (U i)).obj K)) :
    ∀ V : DlAdicFiniteOpen D T, IsZero ((dlAdicLocalEvaluation D c T V).obj K) := by sorry

end WeilConjectures
