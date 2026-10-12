/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# A Sylow cover and its associated-sheaf functor

Source: Stacks Project, Tags 0A3R, 0DV5 and 0DV6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- The geometric part of the Sylow reduction, without constructing any filtration.

Source: Stacks Project, `etale-cohomology.tex`, Lemma 0A3R
(`lemma-pullback-filtered`), first part of the proof; Lemma 0DV5 and Remark 0DV6.
(blueprint: lem-weil-pbc-sylow-cover-associated-sheaf)

Proof: Choose a geometric point of the nonempty connected scheme U. The finite
locally constant sheaf determines a finite-dimensional representation over ZMod ℓ.
Its finite image Q gives a connected finite étale Q-torsor Y over U. Choose an
ℓ-Sylow subgroup P of Q and put V = Y/P. The connected cover V has degree
[Q:P], prime to ℓ. Its geometric fibres have that cardinality: the finite locally
free degree is constant on connected U, preserved by base change, and equals the
number of copies of a separably closed field in the fibre algebra.
The P-torsor Y over V associates a sheaf to every P-representation: descend the
constant module sheaf on Y with its P-action, and extend scalars along the canonical
ring isomorphism ZMod ℓ ≃ ULift (ZMod ℓ). This construction works also for infinite
modules, since P is finite. On the étale cover Y it is the constant-sheaf functor,
which is additive and exact; exactness can be checked on geometric stalks, so the
associated-sheaf functor preserves finite limits and colimits. The trivial rank-one
representation descends to the constant coefficient sheaf. Functoriality of the
monodromy correspondence identifies the image of the restricted representation M
with v*G. If G is zero, Q and P are trivial and M is zero; V can be U. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_associated_sheaf
    {U : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      ∃ (P : Type u) (_ : Group P) (_ : Finite P), IsPGroup ℓ P ∧
        ∃ (M : Rep.{u + 1} (ZMod ℓ) P) (_ : FiniteDimensional (ZMod ℓ) M.V)
          (T : Rep.{u + 1} (ZMod ℓ) P ⥤
            Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
          (_ : T.Additive) (_ : PreservesFiniteLimits T) (_ : PreservesFiniteColimits T),
          Nonempty (T.obj M ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
          Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
            (constantSheaf V.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by sorry

end AlgebraicGeometry
