/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
import WeilConjectures.AlgebraicGeometry.Sp.SpQbarPositiveRootBasis

/-! # Local bases from a prescribed compatible root tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

/-- On one slice with a normalized compatible root basis, the specified field colimit
of rational twists is a free rank-one module over the field-colimit coefficient. -/
theorem spQbarRootBasis
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n)) :
    Nonempty ((spSignedTwist X _ (spQbarTwist X ℓ) 1).over W ≅
      (spSignedTwist X _ (spQbarTwist X ℓ) 0).over W) := by
  simpa using spQbarPositiveRootBasis X ℓ W ζ e hζ he 0

end AlgebraicGeometry.ProEtale
