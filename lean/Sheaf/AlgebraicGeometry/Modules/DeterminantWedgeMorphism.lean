/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal

/-!
# The wedge morphism associated to a short exact sequence

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-wedge-morphism).
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The wedge formula descends to a morphism, without asserting its invertibility.
Only the first term needs a finite locally free rank for this construction.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-wedge-morphism).

Proof: Since `S.g` is an epimorphism of sheaves, any finite tuple of quotient sections
lifts on an open cover. On a member of that cover, send the tensor of the wedge of
`r₁` first-term sections and the wedge of `r₃` quotient sections to the wedge of their
images under `S.f` followed by the chosen lifts, reindexed by `hr`. Two lifts differ
locally by images under `S.f`, by exactness. Their wedge difference vanishes: after
expanding by multilinearity, every term contains at least `r₁ + 1` first-term factors.
Trivialize the first term and expand these factors in a basis of size `r₁`; every term
has a repeated basis vector and is zero by alternation. Thus the local sections are
independent of the lifts and agree on overlaps, and glue by the sheaf property.
The resulting rule is multilinear and alternating separately in the two tuples:
verify this using common local lifts and the corresponding properties of the wedge.
It commutes with restriction for the same reason. The universal properties of the
two exterior-power presheaves and the tensor product, followed by sheafification,
therefore give the stated sheaf morphism. Its formula for every set of lifts follows
from its local construction and separatedness. For either rank zero the same argument
uses the empty wedge, and for the empty open the sheaf property gives the unique section. -/
theorem determinant_wedgeMorphism_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] :
    ∃ φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  apply determinant_wedgeMorphism_of_local_data S hS r₁ r₂ r₃ hr
  exact determinant_wedgeMorphism_local_data S hS r₁ r₂ r₃ hr

end AlgebraicGeometry.Scheme.Modules
