/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.VeryTameDivisorialAction
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Endomorphism
public import Sheaf.RingTheory.ExcellentRing
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic

/-!
# Gabber equivariant very-tame modification

Source: Illusie--Laszlo--Orgogozo, *Travaux de Gabber*, Exposé VIII,
Theorem 1.1, printed p. 85, and Exposé VI, 3.1, pp. 73--74
(blueprint: lem-per-gabber-equivariant-log-modification).

The auxiliary predicates below spell out the largest invariant free open and the
per-affine-open projectivity convention used in the statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An invariant open on which the finite group action is free on geometric points.
Source: ILO VIII 1.1 (blueprint: lem-per-gabber-equivariant-log-modification). -/
def IsFreeInvariantOpen {C : Scheme.{u}} {G : Type v} [Group G]
    (a : G →* Aut C) (V : C.Opens) : Prop :=
  (∀ (g : G) (x : C), (a g).hom x ∈ V ↔ x ∈ V) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ C) (g : G),
      (Scheme.SpecToEquivOfField Ω C t).1 ∈ V →
        t ≫ (a g).hom = t → g = 1

/-- The largest invariant open on which the action is free on geometric points.
Source: ILO VIII 1.1 (blueprint: lem-per-gabber-equivariant-log-modification). -/
def IsLargestFreeInvariantOpen {C : Scheme.{u}} {G : Type v} [Group G]
    (a : G →* Aut C) (V : C.Opens) : Prop :=
  Dense (V : Set C) ∧ IsFreeInvariantOpen a V ∧
    ∀ W : C.Opens, IsFreeInvariantOpen a W → (W : Set C) ⊆ (V : Set C)

/-- Projectivity on every affine open of the target in the finite-projective-space
convention. Source: Stacks 01W8 and ILO VIII 1.1 (blueprint:
lem-per-gabber-equivariant-log-modification). -/
def IsAffineLocallyHProjective {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ W : Y.Opens, IsAffineOpen W → IsHProjective (f ∣_ W)

/-- An integral excellent separated Noetherian scheme with a divisorial log-regular pair
admits a very-tame equivariant projective modification.

Source: Illusie--Laszlo--Orgogozo, *Travaux de Gabber*, Exposé VIII, Theorem 1.1,
printed p. 85, and Exposé VI, 3.1, pp. 73--74
(blueprint: lem-per-gabber-equivariant-log-modification).

Proof:
1. The complement of the closed boundary is dense and its divisorial log structure is
   fine saturated and log regular by `def-trf-log-regular-pair`. Excellence implies the
   quasi-excellence required by the absolute modification theorem, while the order and
   geometric stabilizer hypotheses give tameness and the free-open hypothesis gives
   generic freeness.
2. Apply `lem-per-gabber-absolute-equivariant-modification` to obtain the equivariant
   normalized blowup modification. Its full inverse-image isomorphism over the complement
   of the boundary and non-free locus gives the displayed dense open `C0`; the divisorial
   recognition theorem identifies the resulting log structure with the pair `(C1,B₁)`.
3. Projectivity of the modification restricts over every affine open of `C`, and the
   source is integral and Noetherian by the construction. The inverse image of every
   dense open is dense because it contains the inverse image of the displayed dense
   isomorphism locus.
-/
theorem exists_gabber_equivariant_log_modification
    (C : Scheme.{u}) [IsIntegral C] [IsNoetherian C] [C.IsSeparated]
    (hExcellent : ∀ W : C.Opens, IsAffineOpen W → IsExcellent Γ(C, W))
    (B : TopologicalSpace.Closeds C) (U : C.Opens)
    (hBU : (U : Set C) = (B : Set C)ᶜ)
    (hU : DenseRange U.ι)
    (hlog : IsDivisorialFineSaturatedLogRegularPair C U.toScheme U.ι hU)
    (G : Type v) [Group G] [Finite G] (a : G →* Aut C)
    (horder : ∀ x : C, IsUnit (Nat.card G : C.presheaf.stalk x))
    (hboundary : ∀ (g : G) (x : C), (a g).hom x ∈ U ↔ x ∈ U)
    (V : C.Opens) (hV : IsLargestFreeInvariantOpen a V)
    (T : TopologicalSpace.Closeds C) (hT : (T : Set C) = (V : Set C)ᶜ) :
    ∃ C1 : Scheme.{u}, ∃ hC1int : IsIntegral C1, ∃ hC1noeth : IsNoetherian C1,
      ∃ a1 : G →* (Aut C1), ∃ f : C1 ⟶ C, ∃ C0 : C.Opens,
      Dense (C0 : Set C) ∧
        IsIso (pullback.snd f C0.ι) ∧
        (∀ g : G, (a1 g).hom ≫ f = f ≫ (a g).hom) ∧
        IsAffineLocallyHProjective f ∧
        (∀ W : C.Opens, Dense (W : Set C) →
          Dense ((f ⁻¹ᵁ W : C1.Opens) : Set C1)) ∧
        ∃ (B1 : TopologicalSpace.Closeds C1) (U1 : C1.Opens) (hU1 : DenseRange U1.ι),
          (B1 : Set C1) = f ⁻¹' ((B : Set C) ∪ (T : Set C)) ∧
          (U1 : Set C1) = (B1 : Set C1)ᶜ ∧
          @IsDivisorialFineSaturatedLogRegularPair C1 U1.toScheme U1.ι
            inferInstance hC1noeth.toIsLocallyNoetherian hU1 ∧
          (∀ (g : G) (x : C1), (a1 g).hom x ∈ U1 ↔ x ∈ U1) ∧
          IsVeryTameDivisorialAction U1 a1 := by
  sorry

end AlgebraicGeometry
