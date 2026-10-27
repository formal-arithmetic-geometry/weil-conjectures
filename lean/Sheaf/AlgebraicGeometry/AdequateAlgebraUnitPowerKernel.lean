/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.StackScalarAlgebra
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The adequate-moduli algebra unit has universal power lifting and nil kernel

Source: Alper, Adequate moduli spaces, Lemma 5.2.6 and Proposition 3.3.5,
printed pp.508 and 498 (blueprint: lem-sfb-adequate-algebra-unit-power-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

namespace CategoryTheory

/-- Every scalar extension of the canonical algebra unit has elementwise nil kernel
and lifts positive powers. The section ring and its C action are the explicit compatible
families and the canonical 1 tensor c unit, with no chosen arbitrary algebra map.
Source: Alper, Lemma 5.2.6 and Proposition 3.3.5
(blueprint: lem-sfb-adequate-algebra-unit-power-kernel).

Proof:
1. The adequate-moduli structure identifies R with Γ(F,O_F), and the affine-target
adequacy criterion gives adequate affineness. Present C as P/I, where P=R[T_c : c∈C]
and evaluation sends T_c to c; this is surjective (lem-sfb-affine-target-adequacy-criterion,
def-weil-pbc-mv-polynomial-ring).
2. Base change to Spec P. Adequate affineness persists, the polynomial projection is
flat, and flat scalar-sections identifies Γ(F_P,O)=P, respecting structural sections
(lem-sfb-adequately-affine-affine-target-base-change,
lem-nagata-polynomial-projection-flat, lem-weil-pbc-flat-morphism-affine-criterion,
lem-sfb-stack-flat-scalar-sections).
3. Apply lem-sfb-adequate-ideal-quotient-comparison to I in P. Its source is P/I=C.
The relative-spectrum construction and tensor pushout universal property identify
its target with Γ(F,O_F tensor_R C) and its map with the specified 1 tensor c unit
(lem-sfb-stack-relative-spec-construction,
lem-weil-pbc-algebra-tensor-pushout-universal-property). These identifications persist
on tensoring with any C-algebra C', giving both asserted clauses. No nonflat
commutation of global sections with tensor products is used. -/
theorem adequateAlgebraUnit_power_kernel
    {k : Type u} [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F)
    (φ : BasedFunctor F (discreteModuli
      (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))))))
    (hφ : IsAdequateModuliSpace F hF
      (AlgebraicSpace.schemeSpace
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))))) φ)
    (C : Type u) [CommRing C] [Algebra R C]
    (C' : Type (max u t)) [CommRing C'] [Algebra C C'] :
    (∀ c' : C',
      (algebraMap C' (C' ⊗[C] moduliGlobalSectionsRing (moduliScalarSheaf φ C))) c' = 0 →
        IsNilpotent c') ∧
    (∀ d' : C' ⊗[C] moduliGlobalSectionsRing (moduliScalarSheaf φ C),
      ∃ N : ℕ, 0 < N ∧ ∃ c' : C',
        (algebraMap C' (C' ⊗[C] moduliGlobalSectionsRing (moduliScalarSheaf φ C))) c' =
          d' ^ N) := by
  sorry

end CategoryTheory
