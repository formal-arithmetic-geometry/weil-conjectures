/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.PositiveTensorFamily
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-!
# The line bundle and sections of the symmetric product

Source: Weil conjectures blueprint, symmetric-product-properties, sections paragraph and (a);
Stacks Project, Etale Cohomology, proof of Tag 0A4F
(blueprint: def-weil-pbc-symmetric-product-sections).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The i-th pulled-back twisting sheaf on a scheme with projections to P^1_S.
Source: blueprint symmetric-product-properties, definition of L_n
(blueprint: def-weil-pbc-symmetric-product-sections). -/
noncomputable def symmetricProductFactor {X S : Scheme.{u}} {n : ℕ}
    (pr : Fin n → (X ⟶ ℙ(ULift.{u} (Fin 2); S))) (i : Fin n) : X.Modules :=
  (Scheme.Modules.tensorPullback (pr i)).obj (ProjectiveSpace.twist _ S 1)

/-- Pull back one of the two coordinate sections to the i-th factor.
Source: blueprint symmetric-product-properties, definitions of x_i and y_i
(blueprint: def-weil-pbc-symmetric-product-sections). -/
noncomputable def symmetricProductFactorSection {X S : Scheme.{u}} {n : ℕ}
    (pr : Fin n → (X ⟶ ℙ(ULift.{u} (Fin 2); S))) (i : Fin n) (k : Fin 2) :
    (symmetricProductFactor pr i).sections :=
  (symmetricProductFactor pr i).unitHomEquiv
    (Scheme.Modules.homOfGlobalSection (symmetricProductFactor pr i)
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (pr i))).unit.app
    (ProjectiveSpace.twist _ S 1)).val.app (Opposite.op ⊤)
      (ProjectiveSpace.twistOneSection _ S (ULift.up k))))

/-- O(1,...,1), the ordered tensor of the pulled-back twisting sheaves.
Source: blueprint symmetric-product-properties, definition of L_n
(blueprint: def-weil-pbc-symmetric-product-sections). -/
noncomputable def symmetricProductLineBundle {X S : Scheme.{u}} {m : ℕ}
    (pr : Fin (m + 1) → (X ⟶ ℙ(ULift.{u} (Fin 2); S))) : X.Modules :=
  Scheme.Modules.positiveTensorFamily m (symmetricProductFactor pr)

open Classical in
/-- The global section F_j is the sum of pure tensor monomials over j-element subsets.
The compatible family of sections is obtained from its value on the top open.
Source: blueprint symmetric-product-properties, part (a); Stacks Tag 0A4F
(blueprint: def-weil-pbc-symmetric-product-sections). -/
noncomputable def symmetricProductCoordinateSection {X S : Scheme.{u}} {m : ℕ}
    (pr : Fin (m + 1) → (X ⟶ ℙ(ULift.{u} (Fin 2); S)))
    (j : ULift.{u} (Fin (m + 2))) : (symmetricProductLineBundle pr).sections :=
  (symmetricProductLineBundle pr).unitHomEquiv
    (∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset.filter
        (fun J ↦ J.card = j.down.val),
      (symmetricProductLineBundle pr).unitHomEquiv.symm
        (Scheme.Modules.positiveTensorFamilySection m (symmetricProductFactor pr)
          (fun i ↦ symmetricProductFactorSection pr i (if i ∈ J then 0 else 1))))

end AlgebraicGeometry
