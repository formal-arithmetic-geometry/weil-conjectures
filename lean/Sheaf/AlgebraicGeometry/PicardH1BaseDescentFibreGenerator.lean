/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus

/-! # A free generator on the descended marked fibre
Source: Stacks Project, Tag 0BF2, fibre triviality before the perfect-complex argument.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Fibre descent and universal structure pushforward give a generator on the marked fibre.
Source: Stacks Project, Tag 0BF2, the reduction to a trivial bundle on the marked fibre.
(blueprint: lem-sc-picard-h1-base-descent-fibre-generator)

Proof: The immersion k identifies κ(w) with κ(s). Transport hLs across this identification.
The descended module N over Spec κ(s) is finite free. Its rank is one: the fibre
pullback of L is invertible, and the universal structure-pushforward unit implies that
the fibre structure morphism is surjective. A nonzero fibre point therefore detects
the rank of N. Choose a basis of this one-dimensional vector space, pull it back, and
transport it through the descent isomorphism to obtain a global free generator.
This generates locally at every fibre point. If the fibre were empty, its pushforward
could not be the nonzero structure module of Spec κ(s), so this case is excluded by hO.
No H1 injectivity or target-family descent is used. -/
theorem picard_h1_base_descent_fibre_generator {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    ∃ τ : Γ((Modules.tensorPullback
      (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L, ⊤),
      ∀ y : (pullback f (W.fromSpecResidueField w ≫ k) : Scheme.{v}),
        Modules.GeneratesAt τ y := by sorry

end AlgebraicGeometry.Scheme
