/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Artinian.Module
import Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale

/-! # Artinian test-diagram lifting from infinitesimal étaleness

Source: Stacks Project, Tag 0A43, proof of part (1).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Every small Artinian test diagram at a point over the closed subscheme lifts.
Source: Stacks Project, More on Morphisms, Lemma 0A43, proof of part (1).
(blueprint: lem-weil-pbc-etale-infinitesimal-artinian-tests)

Proof: The spectrum of an Artinian local ring has a single point. Surjectivity
of φ identifies the closed points of Spec B and Spec B'. The commutative
square and the condition on α therefore put the image of β in the support
of J. On an affine neighbourhood of g(x), the image of the ideal J in B'
is contained in its maximal ideal. This maximal ideal is nilpotent, so some
power J^(n+1) maps to zero. Hence β factors through the closed subscheme
cut out by J^(n+1). Commutativity gives a factorization of α through the
pullback X_n. The kernel of φ has length one, so it is a residue-field module
and its square is zero. The étale morphism X_n → Z_n is formally smooth;
apply its infinitesimal lifting property to obtain a lift Spec B' → X_n.
Compose with the projection X_n → X. The pullback projection equations give
both required equalities. -/
theorem artinian_lifting_tests_of_etale_infinitesimal
    {X S Z : Scheme.{u}} (g : X ⟶ S) (i : Z ⟶ S)
    [IsClosedImmersion i] (J : S.IdealSheafData) (hJ : J = i.ker)
    (h_etale : ∀ n : ℕ,
      Etale (pullback.snd g ((J ^ (n + 1)).subschemeι)))
    (x : X) (hx : (g : X → S) x ∈ Set.range (i : Z → S)) :
    ∀ (B' B : Type u) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B),
      Function.Surjective φ → Module.length B' ↥(RingHom.ker φ) = 1 →
      ∀ (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S),
        α ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ β →
        α (IsLocalRing.closedPoint B) = x →
        ∃ γ : Spec (CommRingCat.of B') ⟶ X,
          Spec.map (CommRingCat.ofHom φ) ≫ γ = α ∧ γ ≫ g = β := by
  sorry

end AlgebraicGeometry
