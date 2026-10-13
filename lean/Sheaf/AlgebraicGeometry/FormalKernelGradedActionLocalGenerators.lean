/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.FormalKernelGradedPieces
public import Sheaf.AlgebraicGeometry.GradedSheafStructures

/-! # Local degree-zero generators for the kernel action

Source: Stacks Project, Cohomology of Schemes, Lemma 087Z.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A kernel action with the representative formula in module degree zero is locally
finitely generated in degree zero.
Source: Stacks Project, Lemma 087Z, affine finite-generation argument via Lemma 087W;
https://stacks.math.columbia.edu/tag/087Z and https://stacks.math.columbia.edu/tag/087W.
(blueprint: lem-weil-pbc-formal-kernel-graded-action-local-generators).

Proof: Choose an affine neighbourhood U of the given point. Restrict the coherent
formal system to U, and apply coherentFormalModules_affine to obtain its finite
completion module N with projections having kernels I^(r+1)N. The tilde/global
sections adjunction and the ideal-power and quotient affine-sections formulas
identify B_n and K_n on U with the sheaves of I^n/I^(n+1) and I^n N/I^(n+1)N.
In particular K_0 is N/IN. Choose a finite family generating N/IN, and lift it to N;
its quotient classes give sections s of K_0 on U. The completed-module associated
graded generator theorem says that every class in I^n N/I^(n+1)N is a sum of
classes of a_i times those fixed lifted generators, with a_i in I^n. Under the
identifications, hact identifies each such product with M.act n 0 of the coefficient
class and s_i: apply hact to the projection of the fixed lift to F_(n+1).
Thus the finite sum of these degree-n action maps is an epimorphism on U. Tilde,
a left adjoint, preserves the relevant quotient epimorphisms. On any smaller open
V and any q in V, local surjectivity of this sheaf epimorphism supplies an open
W inside V containing q and coefficient sections a_i of B_n on W expressing the
restriction of y. This is exactly IsLocallyGeneratedInDegreeZero, including its
HEq for n+0=n. No global lift on V or generating family on X is required.
For n=0 the same quotient-generator argument applies. For the zero module use an
empty family. If I is the unit ideal, every formal term is zero by annihilation;
if I=0, all positive kernel degrees vanish. Empty schemes have no points to check.
Only the action formula with module degree zero is used; no formula in positive
module degree, nor a new construction of A or M, is needed. -/
theorem formalKernel_graded_action_local_generators {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (A : GradedSheafAlgebra (formalAssociatedGradedPiece I))
    (M : GradedSheafModule A (formalKernelPiece F))
    (hact : ∀ (n : ℕ) (U : X.Opens)
      (a : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U))
      (s : (formalKernelPiece F 0).val.obj (op U))
      (t : (F.obj.obj (op n)).val.obj (op U)),
      (F.obj.map (homOfLE (Nat.zero_le n)).op).val.app (op U) t =
        (formalKernelι F 0).val.app (op U) s →
      (formalKernelι F n).val.app (op U)
        (M.act n 0 U ((formalAssociatedGradedπ I n).val.app (op U) a) s) =
          (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) a)) • t) :
    M.IsLocallyGeneratedInDegreeZero := by sorry

end AlgebraicGeometry
