/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.CoherentGrothendieckSupport
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Length
public import Mathlib.Data.Finsupp.Defs

/-! # Presentations for coherent support groups and cycles

Source: Stacks Project, Chow Homology, Tags 02S8, 02S9, 02QW and 02QX;
Homology, Tag 02MX (blueprint: def-sfb-coherent-support-cycle-data).

The bounded-support group has its own exact-sequence relations: it is not defined
as the image subgroup of the unrestricted coherent group. Integral closed subschemes
are indexed by their irreducible closed supports, equipped with the unique reduced
induced structure (Stacks 01J3). The coefficient of a cycle is its Finsupp evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Coherent objects of support dimension at most `r`; negative indices contain just
zero objects. Source: Stacks 02S8 (blueprint: def-sfb-coherent-support-cycle-data). -/
def HasSupportBound {X : Scheme.{u}} (r : ℤ) (M : CoherentObject X) : Prop :=
  if r < 0 then Limits.IsZero M.val else
    topologicalKrullDim {x : X // ¬ Subsingleton (M.val.presheaf.stalk x)} ≤
      (r.toNat : WithBot ℕ∞)

/-- The collection C_r(X), retaining the ambient module sheaf of every object.
Source: Stacks 02S8 (blueprint: def-sfb-coherent-support-cycle-data). -/
abbrev SupportCoherentObject (X : Scheme.{u}) (r : ℤ) :=
  {M : CoherentObject X // HasSupportBound r M}

/-- Isomorphism and inherited short exact sequence relations within C_r(X).
Source: Stacks 02MX, 02S9 (blueprint: def-sfb-coherent-support-cycle-data). -/
def supportK0Relations (X : Scheme.{u}) (r : ℤ) :
    AddSubgroup (FreeAbelianGroup (SupportCoherentObject X r)) :=
  AddSubgroup.closure {z |
    (∃ A B : SupportCoherentObject X r, Nonempty (A.val.val ≅ B.val.val) ∧
      z = FreeAbelianGroup.of B - FreeAbelianGroup.of A) ∨
    (∃ A B C : SupportCoherentObject X r,
      ∃ (f : A.val.val ⟶ B.val.val) (g : B.val.val ⟶ C.val.val) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).ShortExact ∧
        z = FreeAbelianGroup.of B - FreeAbelianGroup.of A - FreeAbelianGroup.of C)}

/-- The Grothendieck group K_0(C_r(X)), with exactly the presentation above.
Source: Stacks 02MX, 02S9 (blueprint: def-sfb-coherent-support-cycle-data). -/
abbrev SupportK0 (X : Scheme.{u}) (r : ℤ) :=
  FreeAbelianGroup (SupportCoherentObject X r) ⧸ supportK0Relations X r

/-- The canonical class of an object in its bounded-support Grothendieck group.
Source: Stacks 02S9 (blueprint: def-sfb-coherent-support-cycle-data). -/
def supportK0Class {X : Scheme.{u}} {r : ℤ} (M : SupportCoherentObject X r) :
    SupportK0 X r :=
  QuotientAddGroup.mk (FreeAbelianGroup.of M)

/-- Integral closed subschemes of dimension k, represented without duplicate embeddings
by their irreducible closed supports and the unique reduced induced structure.
Source: Stacks 01J3, 02QX (blueprint: def-sfb-coherent-support-cycle-data). -/
abbrev IntegralCycleIndex (X : Scheme.{u}) (k : ℕ) :=
  {V : IrreducibleCloseds X // topologicalKrullDim (V : Set X) = (k : WithBot ℕ∞)}

/-- The free abelian group on the dimension-k integral closed subschemes.
Source: Stacks 02QX, 02S9 (blueprint: def-sfb-coherent-support-cycle-data). -/
abbrev IntegralCycles (X : Scheme.{u}) (k : ℕ) :=
  IntegralCycleIndex X k →₀ ℤ

/-- The generic point in X of an integral closed cycle index.
Source: Stacks 02QW, 02QX (blueprint: def-sfb-coherent-support-cycle-data). -/
def cycleGenericPoint {X : Scheme.{u}} {k : ℕ} (V : IntegralCycleIndex X k) : X :=
  V.val.isIrreducible.genericPoint

/-- Generic multiplicity, measured as module length over the ambient local ring.
Source: Stacks 02QW, 02QX (blueprint: def-sfb-coherent-support-cycle-data). -/
def cycleStalkLength {X : Scheme.{u}} {k : ℕ} (M : X.Modules)
    (V : IntegralCycleIndex X k) : ℕ∞ :=
  Module.length (X.presheaf.stalk (cycleGenericPoint V))
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace (cycleGenericPoint V)).obj M)

/-- A homomorphism induced by inclusion, specified on every generator and every
isomorphic representative in the larger category. This pins down the canonical map.
Source: Stacks 02MX, 02S9 (blueprint: def-sfb-coherent-support-cycle-data). -/
def IsSupportK0Inclusion (X : Scheme.{u}) (k : ℕ)
    (ι : SupportK0 X ((k : ℤ) - 1) →+ SupportK0 X (k : ℤ)) : Prop :=
  ∀ (A : SupportCoherentObject X ((k : ℤ) - 1))
    (B : SupportCoherentObject X (k : ℤ)), Nonempty (A.val.val ≅ B.val.val) →
      ι (supportK0Class A) = supportK0Class B

/-- The cycle formula, specified coefficientwise on every object class. The finite
length assertion in the theorem ensures that `toNat` is the actual length.
Source: Stacks 02QX, 02S9 (blueprint: def-sfb-coherent-support-cycle-data). -/
def IsGenericLengthCycleMap (X : Scheme.{u}) (k : ℕ)
    (c : SupportK0 X (k : ℤ) →+ IntegralCycles X k) : Prop :=
  ∀ (M : SupportCoherentObject X (k : ℤ)) (V : IntegralCycleIndex X k),
    c (supportK0Class M) V = ((cycleStalkLength M.val.val V).toNat : ℤ)

end AlgebraicGeometry.Scheme.Modules
