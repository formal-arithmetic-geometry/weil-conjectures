/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Localization of the base of the naive cotangent complex

Source: Stacks Project, Algebra, Tag 07BS (lemma-NL-localize-bottom), with the
standard presentations of Section 00S0
(blueprint: lem-sfb-naive-cotangent-localize-base).

The cone of the degree-zero single cotangent differential is the standard
naive cotangent complex in cohomological degrees `-1,0`. The comparison is the
cone map of the canonical coefficient-localization square, fixing every variable.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Algebra

variable {A : Type u} [CommRing A] (S : Submonoid A) (B : Type v) [CommRing B]
variable [Algebra A B] [Algebra (Localization S) B] [IsScalarTower A (Localization S) B]

/-- The canonical square of standard cotangent differentials induced by
`A[B] → (S⁻¹A)[B]`. The default hom between these two self presentations sends
`x_b` to `x_b`, since the designated section of the target is `MvPolynomial.X`.
Source: Stacks, Tag 07BS and Section 00S0, functoriality of presentations
(blueprint: lem-sfb-naive-cotangent-localize-base). -/
def naiveCotangentLocalizeBaseSquare :=
  Arrow.homMk'
    (f := ModuleCat.ofHom (Generators.self A B).toExtension.cotangentComplex)
    (g := ModuleCat.ofHom
      (Generators.self (Localization S) B).toExtension.cotangentComplex)
    (ModuleCat.ofHom (Extension.Cotangent.map
      (Generators.defaultHom (Generators.self A B)
        (Generators.self (Localization S) B)).toExtensionHom))
    (ModuleCat.ofHom (Extension.CotangentSpace.map
      (Generators.defaultHom (Generators.self A B)
        (Generators.self (Localization S) B)).toExtensionHom))
    (congrArg ModuleCat.ofHom (Extension.CotangentSpace.map_comp_cotangentComplex
      (Generators.defaultHom (Generators.self A B)
        (Generators.self (Localization S) B)).toExtensionHom).symm)

/-- The canonical chain map on standard naive cotangent complexes: the cone map
of the degree-zero single complexes of the canonical cotangent square.
Its degree minus one map sends `[h]` to `[h/1]`, and its degree zero map sends
`b ⊗ dh` to `b ⊗ d(h/1)`.
Source: Stacks, Tag 07BS and Section 00S0
(blueprint: lem-sfb-naive-cotangent-localize-base). -/
def naiveCotangentLocalizeBaseMap :=
  HomologicalComplex.homotopyCofiber.mapArrowHom _ _
    (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    (((HomologicalComplex.single (ModuleCat.{max u v} B) (.up ℤ) 0).mapArrow).map
      (naiveCotangentLocalizeBaseSquare S B))

/-- The specified canonical base-localization comparison is invertible in `D(B)`
and is a homotopy equivalence of the standard two-term complexes.
Source: Stacks Project, Algebra, Tag 07BS (lemma-NL-localize-bottom)
(blueprint: lem-sfb-naive-cotangent-localize-base).

Proof for stage 3:
1. Write P = A[B] and P_S = (S⁻¹A)[B]. A polynomial has only finitely many
coefficients, so common denominators identify P_S with the localization of P
at the constants from S. An element killed by the coefficient map is killed
by a common product of its coefficient annihilators. Evaluation sends p/s
to s_B⁻¹ epsilon(p), since every s_B is a unit in B.
2. For I = ker(P → B) and J = ker(P_S → B), a fraction p/s belongs to J
exactly when p belongs to I. Thus J = I P_S, without an injectivity assumption.
3. By lem-weil-pbc-localization-flat and
lem-weil-pbc-ideal-cotangent-flat-base-change-ring, the conormal comparison is
(I/I²) tensor_P P_S ≃ J/J². Multiplication m tensor p/s ↦ epsilon(p)s_B⁻¹ m
identifies its source with I/I²; the inverse is m ↦ m tensor 1. Tensor
balancing and invertibility of s prove both inverse identities. Thus the
canonical degree minus one map has inverse [i/s] ↦ s_B⁻¹[i].
4. By lem-weil-pbc-polynomial-ring-kahler-basis-any-variables, both degree zero
modules are free B-modules on dx_b. The comparison fixes their indices, so
reversing this basis assignment gives its inverse, for arbitrary variable sets.
5. The differentials send [i] to 1 tensor di. Coefficient localization fixes
variables and commutes with their formal partial derivatives, so the maps in
steps 3 and 4 form the canonical chain map. Their inverses commute with the
differentials too. The composites are identities, hence admit zero homotopies.
The functor to the derived category preserves the inverse. If 0 belongs to S,
existence of the map to B forces B to be the zero ring and the same formulas
remain valid. No finiteness or nonzero-ring hypothesis is used. -/
theorem naiveCotangent_localize_base
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)] :
    IsIso (DerivedCategory.Q.map (naiveCotangentLocalizeBaseMap S B)) ∧
      ∃ e : HomotopyEquiv _ _, e.hom = naiveCotangentLocalizeBaseMap S B := by
  sorry

end Algebra
