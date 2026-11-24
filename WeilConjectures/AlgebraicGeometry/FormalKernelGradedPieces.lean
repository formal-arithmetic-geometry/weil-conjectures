/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-! # The homogeneous pieces of a formal system's kernel module

`op n` represents F_(n+1). The degree-zero kernel is F_1 (the convention F_0 = 0).
The algebra's degree n is I^n / I I^n = I^n / I^(n+1).

## References

* Stacks Project, Tags 087Z and 0EHN
-/

@[expose] public section

universe uk

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The degree n of the associated graded ideal algebra, including I^0 = O_X.
(Stacks, Tag 087Z.) -/
noncomputable def formalAssociatedGradedPiece {X : Scheme.{uk}} (I : X.IdealSheafData)
    (n : ℕ) : X.Modules :=
  formalModuleQuotient I 1 (Scheme.idealSheafPower I.toModulesι n).1

/-- The projection I^n → I^n / I^(n+1). (Stacks, Tag 087Z.) -/
noncomputable def formalAssociatedGradedπ {X : Scheme.{uk}} (I : X.IdealSheafData)
    (n : ℕ) : (Scheme.idealSheafPower I.toModulesι n).1 ⟶
      formalAssociatedGradedPiece I n :=
  formalModuleQuotientπ I 1 (Scheme.idealSheafPower I.toModulesι n).1

/-- The successive kernel K_n; at n = 0 this is F_1, with F_0 understood as zero.
(Stacks, Tag 087Z.) -/
noncomputable def formalKernelPiece {X : Scheme.{uk}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) : ℕ → X.Modules
  | 0 => F.obj.obj (op 0)
  | n + 1 => kernel (F.obj.map (homOfLE (Nat.le_succ n)).op)

/-- The inclusion K_n → F_(n+1), the identity in degree zero. (Stacks, Tag 087Z.) -/
noncomputable def formalKernelι {X : Scheme.{uk}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) :
    ∀ n : ℕ, formalKernelPiece F n ⟶ F.obj.obj (op n)
  | 0 => 𝟙 _
  | n + 1 => kernel.ι (F.obj.map (homOfLE (Nat.le_succ n)).op)

end AlgebraicGeometry
