/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.CategoryTheory.Category.Preorder

/-! # Ramified regular divisor towers

Source: Stacks Project, Tag 0EYM, applied to the root tower in direct-images paragraph (3)
of blueprint main-20261015 (blueprint: def-sfb-ramified-root-tower).

## Main definitions

- `RamifiedRootIndex`: positive prime-to-p integers with the divisibility preorder.
- `RamifiedRootTower`: regular affine stages, ramified parameters and a genuine limit cone.
- `RamifiedRootTower.divisor`, `RamifiedRootTower.puncture`: actual closed and open subschemes.
- `RamifiedRootTower.limitOpen`: the principal puncture of the limit at the original parameter.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Positive integers prime to p, with divisibility as their order.
Source: the prime-to-p root tower in direct-images paragraph (3)
(blueprint: def-sfb-ramified-root-tower). -/
structure RamifiedRootIndex (p : ℕ) where
  val : ℕ
  positive : 0 < val
  coprime : val.Coprime p

/-- Divisibility preorder on root orders. Source: direct-images paragraph (3)
(blueprint: def-sfb-ramified-root-tower). -/
instance (p : ℕ) : Preorder (RamifiedRootIndex p) where
  le n m := n.val ∣ m.val
  le_refl n := dvd_refl n.val
  le_trans _ _ _ := dvd_trans

/-- The initial root order. Source: direct-images paragraph (3)
(blueprint: def-sfb-ramified-root-tower). -/
def RamifiedRootIndex.one (p : ℕ) : RamifiedRootIndex p :=
  ⟨1, Nat.zero_lt_one, Nat.coprime_one_left p⟩

/-- Geometric data of the full root tower. All divisors are the scheme-theoretic zero
loci, and the limit cone is specified by its universal property. Regularity and the
nonzerodivisor hypothesis are retained, also for empty schemes and empty divisors.
Source: Stacks 0EYM and direct-images paragraph (3)
(blueprint: def-sfb-ramified-root-tower). -/
structure RamifiedRootTower (p ℓ : ℕ) where
  diagram : (RamifiedRootIndex p)ᵒᵖ ⥤ Scheme.{u}
  affine (n : RamifiedRootIndex p) : IsAffine (diagram.obj (op n))
  noetherian (n : RamifiedRootIndex p) : IsNoetherian (diagram.obj (op n))
  regular (n : RamifiedRootIndex p) : IsRegularScheme (diagram.obj (op n))
  transition_affine {n m : RamifiedRootIndex p} (a : n ⟶ m) :
    IsAffineHom (diagram.map a.op)
  parameter (n : RamifiedRootIndex p) : Γ(diagram.obj (op n), ⊤)
  nonzerodivisor (n : RamifiedRootIndex p) : parameter n ∈ nonZeroDivisors _
  ell_unit (n : RamifiedRootIndex p) : IsUnit (ℓ : Γ(diagram.obj (op n), ⊤))
  divisor_regular (n : RamifiedRootIndex p) :
    IsRegularScheme ((diagram.obj (op n)).zeroLocusSubscheme {parameter n})
  ramification {n m : RamifiedRootIndex p} (a : n ⟶ m) :
    (diagram.map a.op).appTop.hom (parameter n) = parameter m ^ (m.val / n.val)
  cone : Cone diagram
  isLimit : IsLimit cone

/-- The limit parameter is the pullback of the original order-one parameter.
Source: Stacks 0EYM and the displayed principal open at the limit
(blueprint: def-sfb-ramified-root-tower). -/
def RamifiedRootTower.limitParameter {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ) :
    Γ(T.cone.pt, ⊤) :=
  (T.cone.π.app (op (RamifiedRootIndex.one p))).appTop.hom
    (T.parameter (RamifiedRootIndex.one p))

/-- The actual stage scheme. Source: Stacks 0EYM
(blueprint: def-sfb-ramified-root-tower). -/
abbrev RamifiedRootTower.stage {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    (n : RamifiedRootIndex p) := T.diagram.obj (op n)

/-- The actual zero-locus scheme, with its scheme structure. Source: ILO XVI 2.1
(blueprint: def-sfb-ramified-root-tower). -/
abbrev RamifiedRootTower.divisor {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    (n : RamifiedRootIndex p) := (T.stage n).zeroLocusSubscheme {T.parameter n}

/-- The closed immersion of the actual divisor. Source: ILO XVI 2.1
(blueprint: def-sfb-ramified-root-tower). -/
abbrev RamifiedRootTower.closed {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    (n : RamifiedRootIndex p) := (T.stage n).zeroLocusSubschemeι {T.parameter n}

/-- The principal punctured open, allowing the empty open. Source: Stacks 0EYM
(blueprint: def-sfb-ramified-root-tower). -/
abbrev RamifiedRootTower.puncture {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    (n : RamifiedRootIndex p) := ((T.stage n).basicOpen (T.parameter n)).toScheme

/-- Its canonical inclusion. Source: Stacks 0EYM
(blueprint: def-sfb-ramified-root-tower). -/
abbrev RamifiedRootTower.open {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    (n : RamifiedRootIndex p) := ((T.stage n).basicOpen (T.parameter n)).ι

/-- The limit puncture is defined using the original parameter at stage one.
Source: Stacks 0EYM (blueprint: def-sfb-ramified-root-tower). -/
abbrev RamifiedRootTower.limitOpen {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ) :=
  (T.cone.pt.basicOpen T.limitParameter).toScheme

/-- The principal open inclusion on the limit. Source: Stacks 0EYM
(blueprint: def-sfb-ramified-root-tower). -/
abbrev RamifiedRootTower.limitInclusion {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ) :=
  (T.cone.pt.basicOpen T.limitParameter).ι

end AlgebraicGeometry
