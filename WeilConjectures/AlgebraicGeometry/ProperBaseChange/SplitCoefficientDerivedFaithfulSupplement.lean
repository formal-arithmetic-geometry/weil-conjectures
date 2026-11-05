/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
/-! # Faithfulness of scalar extension to the condensed algebraic closure

An algebraic linear projection to a finite coefficient field is continuous on every
finite-dimensional subfield and therefore acts on the condensed algebraic closure.
Tensoring its linear retraction splits the scalar-extension unit, also after localization.
-/
@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonObj BraidedCategory Opposite
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

variable (H : C ⥤ D) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
variable {X : Scheme.{u}}
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
  (r : S ⟶ R)
  (hlin : (φ ▷ S ≫ μ[S]) ≫ r = R ◁ r ≫ μ[R])

end AlgebraicGeometry.ProEtale
namespace CategoryTheory
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
open scoped CategoryTheory.Obj

end CategoryTheory

namespace Profinite
open PadicAlgCl
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

end Profinite

namespace AlgebraicGeometry.ProEtale
open PadicAlgCl
end AlgebraicGeometry.ProEtale
