/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Paper.FiniteFreeScalarCalculusData

/-! # Normalized finite-free scalar constructions

Source: Stacks Project, Tags 03CZ, 05V4, 06YU and 05RT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  [Algebra A B] (r : ℕ) (basis : Module.Basis (Fin r) A B)

/-- Exact finite-free scalar descent and the normalized ordinary balancing maps.
Source: Stacks 03CZ, 05V4, 06YY and 05RT; steps 1-6 and the ordinary part of step 7
of lem-sf-finite-free-derived-scalar-calculus.
(blueprint: lem-sf-finite-free-scalar-tensor-calculus).

Proof: sheafify the basis map and its coordinates to identify restriction after extension
with a finite direct sum. Restriction preserves the underlying abelian sheaf, hence is
exact and conservative; exactness of finite sums makes extension exact, also in rank zero.
Descend the termwise functors through quasi-isomorphisms. The localization universal
property makes this exact descent the left derived functor with its specified counit.
Localize the scalar adjunction; its localized unit and counit are exactly the two
factorization formulas in FiniteFreeScalarDescent. Homology commutes with restriction,
so the unbounded cohomology criterion reflects isomorphisms and zero objects. Localize
the basis decomposition; its inclusions are the scalar unit followed by multiplication
by the chosen basis element. Extension of K-flat complexes is K-flat by the acyclic
tensor test and tensor cancellation. For ordinary balancing use the maps
(b tensor m) tensor n to m tensor b n and m tensor n to (1 tensor m) tensor n.
Balancedness gives inverse module maps before sheafification; their sheafifications give
the displayed comparisons with exactly the stated local pure-tensor normalizations. -/
theorem finiteFreeScalarTensorCalculus :
    Nonempty (FiniteFreeScalarTensorCalculus J r basis) := by sorry

end AlgebraicGeometry
