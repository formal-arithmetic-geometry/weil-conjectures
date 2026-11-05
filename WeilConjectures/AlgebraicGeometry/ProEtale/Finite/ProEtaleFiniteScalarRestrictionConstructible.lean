/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Finite scalar restriction preserves pro-etale constructibility

Source: current Weil blueprint, sec-proetale-coefficients,
`sk-prop-integral-criterion-reductions.proof.md`, second paragraph, last sentence;
Stacks Tags 03DA, 03D2, 093I, 093Q, 09AJ, 010N and 015F
(blueprint: lem-pe-finite-scalar-restriction-constructible).

The coefficient map is arbitrary; no surjectivity or flatness is imposed.
The intrinsic constant-ring module category and its existing exact restriction functor
are used throughout. The witness statements retain each original local trivialization cover.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ S₀ : Cᵒᵖ ⥤ RingCat.{w}} {R S : Sheaf J RingCat.{w}}
  (α : R₀ ⟶ R.obj) (β : S₀ ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  (a₀ : R₀ ⟶ S₀) (a : R ⟶ S) (comm : α ≫ a.hom = a₀ ≫ β)
  (P : _root_.PresheafOfModules.{t} S₀)

end

end AlgebraicGeometry.Scheme
