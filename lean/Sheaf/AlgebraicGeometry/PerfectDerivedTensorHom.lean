/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.Algebra.Homology.DerivedInternalHom

/-! # Derived tensor-Hom adjunction for perfect complexes

Source: Stacks Project, perfect.tex, Section RHom; cohomology.tex, Tag 08DJ,
equation (1), and Tag 0FPB (blueprint: lem-sc-affine-perfect-derived-tensor-hom).
-/

universe u w

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry

/-- For perfect `A` and `I` and arbitrary `E` in `D(O_X)`, morphisms `I → RHom(A,E)`
correspond bijectively to morphisms `A ⊗ᴸ I → E`, naturally in all three objects.
The single equation expresses contravariance in `A` and `I` and covariance in `E`.
Source: Stacks Project, perfect.tex, Section RHom; cohomology.tex, Tag 08DJ,
equation (1), and Tag 0FPB (blueprint: lem-sc-affine-perfect-derived-tensor-hom).

Proof:
1. Apply `lem-sc-derived-internal-hom-adjunction` with `K = I`, `L = A`, `M = E`.
   Its symmetric form gives `Hom(I,RHom(A,E)) ≃ Hom(A ⊗ᴸ I,E)`, functorially in
   `I`, `A` and `E`. This uses the tensor symmetry of Tag 0FPB and the adjunction
   of Tag 08DJ. Perfectness is retained as in the node, although not used in this step.
2. Evaluate the equivalence on a morphism to obtain its transpose `A ⊗ᴸ I → E`.
   Functoriality gives the displayed simultaneous naturality equation, by precomposition
   in the first two variables and postcomposition in the third. -/
theorem exists_perfectDerivedTensorHomEquiv (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ e : ∀ (A I : schemeDerivedCategory X),
        Scheme.IsPerfect X A → Scheme.IsPerfect X I → ∀ E : schemeDerivedCategory X,
        (I ⟶ (derivedInternalHom (Opens.grothendieckTopology X)
          X.sheaf).obj (op A, E)) ≃ (A ⊗ I ⟶ E),
      ∀ (A A' I I' E E' : schemeDerivedCategory X)
        (hA : Scheme.IsPerfect X A) (hA' : Scheme.IsPerfect X A')
        (hI : Scheme.IsPerfect X I) (hI' : Scheme.IsPerfect X I')
        (f : A' ⟶ A) (g : I' ⟶ I) (h : E ⟶ E')
        (t : I ⟶ (derivedInternalHom (Opens.grothendieckTopology X)
          X.sheaf).obj (op A, E)),
        e A' I' hA' hI' E'
          (g ≫ t ≫ (derivedInternalHom (Opens.grothendieckTopology X)
            X.sheaf).map (f.op, h)) =
          (f ⊗ₘ g) ≫ e A I hA hI E t ≫ h := by
  sorry

end AlgebraicGeometry
