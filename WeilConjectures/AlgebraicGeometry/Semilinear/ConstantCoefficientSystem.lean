/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # The constant system of modules on a ringed site

Source: Zheng, Construction 4.1; the actual reduction construction in step 1 of
`lem-sfb-finite-proper-exceptional-coherent-tower`.
(blueprint: def-sfb-constant-coefficient-system)

The sectionwise characterizations determine the functor, including its horizontal
maps. In particular its derived functor is an actual functor to the localization
of the abelian category of systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})

/-- Constant coefficients, with the identity horizontal coefficient homomorphism.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
def constantCoefficients : ℕ → Sheaf J CommRingCat.{max c v r} := fun _ ↦ R

/-- The identity coefficient transitions.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
def constantCoefficientTransitions (n : ℕ) :
    constantCoefficients.{c, v, r} J R (n + 1) ⟶ constantCoefficients.{c, v, r} J R n := 𝟙 R

/-- A constant system keeps each module and each morphism at every vertex, and
its horizontal maps are the identity. Heterogeneous equality only suppresses
the restriction-of-scalars presentations of the same identity action.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
def IsConstantSystemFunctor
    (F : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R)) : Prop :=
  (∀ (M : Mod.{c, v, max c v r} J R) (n : ℕ),
    (evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) n).obj (F.obj M) = M) ∧
  (∀ {M N : Mod.{c, v, max c v r} J R} (f : M ⟶ N) (n : ℕ),
    HEq ((evaluation.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) n).map (F.map f)) f) ∧
  (∀ (M : Mod.{c, v, max c v r} J R) {m n : ℕ} (h : n ≤ m),
    HEq ((transition.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R) h).app (F.obj M)) (𝟙 M))

/-- The constant module system is uniquely determined and is exact.
Source: Zheng, Construction 4.1; Stacks, Tag 0941
(blueprint: def-sfb-constant-coefficient-system).

Proof: on the product site put M(U) at (n,U), use the restriction of M on a
vertical arrow and the identity on every horizontal arrow. The ring action is
the original R(U)-action. The vertical sheaf condition is exactly that of M.
Apply the same construction to morphisms. Evaluation gives the three displayed
identities. Conversely these identities determine every section, action,
restriction, horizontal map and component of every morphism, so extensionality
of module presheaves and functors proves uniqueness. Kernels and sheafified
cokernels in the sequence topos are computed componentwise. Constant systems
therefore preserve finite limits and finite colimits; their maps preserve
addition sectionwise. This includes the zero ring, empty site and zero module.
-/
theorem constantSystem_existsUnique :
    (∃! F : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R), IsConstantSystemFunctor.{c, v, r} J R F) ∧
    (∀ F : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
      (constantCoefficientTransitions.{c, v, r} J R), IsConstantSystemFunctor.{c, v, r} J R F →
      F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F) := by
  sorry

/-- The genuine diagonal functor, selected from its unique sectionwise characterization.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
def constantSystem : Mod.{c, v, max c v r} J R ⥤
      Systems.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
    (constantCoefficientTransitions.{c, v, r} J R) :=
  (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose

/-- Additivity of the genuine constant-system functor.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
instance constantSystem_additive : (constantSystem.{c, v, r} J R).Additive :=
  ((constantSystem_existsUnique.{c, v, r} J R).2 _
    (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose_spec).1

/-- Left exactness of the genuine constant-system functor.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
instance constantSystem_limits : PreservesFiniteLimits (constantSystem.{c, v, r} J R) :=
  ((constantSystem_existsUnique.{c, v, r} J R).2 _
    (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose_spec).2.1

/-- Right exactness of the genuine constant-system functor.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
instance constantSystem_colimits : PreservesFiniteColimits (constantSystem.{c, v, r} J R) :=
  ((constantSystem_existsUnique.{c, v, r} J R).2 _
    (constantSystem_existsUnique.{c, v, r} J R).1.exists.choose_spec).2.2

/-- Termwise localization of the exact diagonal, before any coefficient extension.
Source: Zheng, Construction 4.1 (blueprint: def-sfb-constant-coefficient-system). -/
def derivedConstantSystem : D.{c, v, max c v r} J R ⥤
    DS.{c, v, max c v r} J (constantCoefficients.{c, v, r} J R)
    (constantCoefficientTransitions.{c, v, r} J R) :=
  (constantSystem.{c, v, r} J R).mapDerivedCategory

end WeilConjectures.SemilinearSections
