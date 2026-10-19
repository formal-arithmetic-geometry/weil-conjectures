/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsRightExact
import Sheaf.AlgebraicGeometry.FlatModulePullbackExact
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal

/-! # Construction of the normalized additive comparison map

Source: Stacks Project, Tags 03P2, 03FD and 010S.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.CoherentEtale
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Construct a normalized additive map, without asserting either uniqueness or invertibility.
Source: Stacks Project, Tags 03P2 and 03FD (comparison), and Tag 010S (extension).
(blueprint: lem-pbc-coherent-etale-normalized-additive-map).

Proof: On the abelian category of quasi-coherent modules, take the Zariski
abelian cohomology delta functor and the etale tensor-section cohomology delta
functor. Exactness of tensor-section descent gives the latter's connecting maps;
these are composition with the short exact sequence's Ext class. A finite affine
open cover gives acyclic quasi-coherent embeddings, so the source delta functor
is effaceable and hence universal by Tag 010T. In degree zero the tensor-pullback
unit to the terminal etale object identifies the section groups, followed by
ULift.up on coefficients. Naturality of the adjunction unit makes this a natural
additive transformation. Extend it by the universal property. Evaluate the
resulting delta-functor morphism at every module and degree. Its naturality,
degree-zero component, and boundary axiom give the three asserted conditions.
The prescribed components of m determine its coefficient morphisms uniquely,
so the construction applies to the supplied m. No bijectivity or uniqueness of
the resulting family is used in this construction. -/
theorem exists_normalized_map {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (m : Maps X)
    (hm : ∀ (F G : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.map (((tensorPullback U.hom).map φ).app ⊤)) :
    ∃ c : Family X, IsNormalized X m c := by sorry

end
end AlgebraicGeometry.Scheme.Modules.CoherentEtale
