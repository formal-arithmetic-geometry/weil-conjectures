/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
import Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison

/-! # Invertibility of the evaluation-defined perfect internal-Hom pullback map

Source: Stacks Project, cohomology.tex, Tags 08I3 and 0FPC.
(blueprint: lem-pc-perfect-internal-hom-pullback-isIso).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Pullback of internal Hom from a perfect source commutes with internal Hom.
This asserts invertibility of the evaluation-defined map, for the fixed normalized
tensor-Hom adjunctions and a canonical pullback tensor comparison, rather than
existence of an unrelated isomorphism between the two objects.

Source: Stacks Project, cohomology.tex, Remark 08I3 and Example 0FPC.
(blueprint: lem-pc-perfect-internal-hom-pullback-isIso).

Proof: Locally represent M by a bounded complex of finite projective modules.
Its dual is perfect, and the tensor-Hom evaluation comparison identifies RHom(M,K)
with K tensor the dual of M, for arbitrary unbounded K. Equivalently use the exact
pairing and evaluation comparison of perfect_rhom_tensor_comparison.
Strong monoidal derived pullback transports evaluation and coevaluation and both
triangle identities. The perfect-dual pullback comparison identifies the transported
dual with the internal dual of Lg*M. The tensor-Hom evaluation comparison on the
source and target therefore identifies Lg*RHom(M,K) with RHom(Lg*M,Lg*K).
To identify the resulting isomorphism with the displayed arrow, apply the injective
tensor-Hom equivalence on the target: its evaluation is pullback of evaluation,
precomposed with the inverse tensor comparison. The fixed canonical adjunctions
have exactly this evaluation normalization. Uniqueness of the canonical tensor
comparison identifies the supplied t with that of the monoidal pullback model.
Thus the displayed map is the constructed isomorphism and is invertible. -/
theorem perfect_internalHom_pullback_isIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {T X : Scheme.{u}} (g : T ⟶ X)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M K : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M)
    (t : tensor (schemeDerivedCategory X) ⋙ derivedPullback g ≅
      (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory T))
    (ht : IsCanonicalPullbackTensorComparison g (fun E K => t.hom.app (E, K))) :
    IsIso
      ((canonicalTensorHomAdjunction T ((derivedPullback g).obj M)).homEquiv
        ((derivedPullback g).obj
          ((derivedInternalHom (Opens.grothendieckTopology X)
            X.toRingedSpace.sheaf).obj (op M, K))) ((derivedPullback g).obj K)
        (t.inv.app
            ((derivedInternalHom (Opens.grothendieckTopology X)
              X.toRingedSpace.sheaf).obj (op M, K), M) ≫
          (derivedPullback g).map ((canonicalTensorHomAdjunction X M).counit.app K))) := by
  sorry

end AlgebraicGeometry
