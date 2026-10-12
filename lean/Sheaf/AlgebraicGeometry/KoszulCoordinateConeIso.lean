/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Paper.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.RingTheory.KoszulTensorConeCoordinates

/-! # A Koszul coordinate as a scalar mapping cone

Source: Stacks Project, Tag 0629.
(blueprint: lem-pc-koszul-coordinate-cone-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The sheafified Koszul complex, with one distinguished coordinate, is the
mapping cone of multiplication by that coordinate on the remaining complex.
Source: Stacks Project, More on Algebra, Tags 0628 and 0629.
(blueprint: lem-pc-koszul-coordinate-cone-iso).

Proof: Reindex the standard basis by the equivalence which places `i` last
and sends the preceding coordinates to `i.succAbove`. Exterior powers of this
basis change commute with contraction against the reindexed linear form,
and therefore give an isomorphism of Koszul complexes. For the last coordinate,
split every exterior power according to whether it contains that coordinate.
Writing the last basis vector first, the degree `q` identification is
`wedge^q(prefix) + wedge^(q-1)(prefix)`. Contraction has matrix
`(x,y) |-> (d x + a y, -d y)`, by the graded Leibniz formula. In degree zero
only the first summand remains. These are exactly the mapping-cone terms and
differentials after extending chain degree `q` to cochain degree `-q`.
Termwise sheafification preserves these finite biproducts and the matrix
formulas because it is additive, giving the stated cochain isomorphism.
The construction includes `r = 0`, zero generators and the zero ring. -/
theorem koszul_coordinate_cone_iso
    (A : Type u) [CommRing A] (r : ℕ) (g : Fin (r + 1) → A)
    (i : Fin (r + 1)) (a : A) :
    let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
    let P := (ExteriorAlgebra.koszulComplex A r (fun j ↦ g (i.succAbove j))).extend
      ComplexShape.embeddingDownNat
    Nonempty (T.obj ((ExteriorAlgebra.koszulComplex A (r + 1)
        (Function.update g i a)).extend ComplexShape.embeddingDownNat) ≅
      CochainComplex.mappingCone (T.map (a • 𝟙 P))) := by sorry

end AlgebraicGeometry
