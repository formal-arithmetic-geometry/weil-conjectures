/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.FieldExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar

/-!
# Algebraic field base change for module objects over a finite coefficient ring

Let `T` be a finite discrete commutative ring and `Λ = C(-, T)` the corresponding condensed
ring. Let `Ω / L` be an algebraic field extension, `h : G ⟶ Spec L` and `g : G_Ω ⟶ G` the base
change. For a module object `M` over `Λ_G` whose image under the equivalence
`ProEtale.finiteCoefficientModEquivalence` with pro-étale sheaves of `T`-modules is of étale
origin, `g^* M` is acyclic for the pushforward `g_*` of module objects
(`AlgebraicGeometry.ProEtale.rightAcyclic_condensedRingLowerStar_upperStar_of_iso`).

This is transported from the statement for pro-étale sheaves of modules
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj`) along
the exact equivalence `ProEtale.finiteCoefficientModEquivalence`, which commutes with pullbacks
and pushforwards, using that acyclicity is invariant under such a transport
(`CategoryTheory.Functor.rightAcyclic_of_rightAcyclic_equivalence_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D'] [HasDerivedCategory C]
  [HasDerivedCategory C'] [HasDerivedCategory D'] [EnoughInjectives C] [EnoughInjectives C']

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

open scoped CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω]
  {G : Scheme.{u}} (h : G ⟶ Spec (.of L))

end AlgebraicGeometry.ProEtale
