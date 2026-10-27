/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.ContinuousRepresentationCondensation
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.RepresentationTheory.LAdic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Additive
import Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients
import Sheaf.Topology.TopologicalBasisLiftSection
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Exact continuous realizations and restriction triangles

Source: current blueprint, direct-image stability proof, paragraph (3), agent-extracted
continuous-subquotient auxiliary; Stacks Tag 0152 for the short-exact triangle
(blueprint: lem-sfb-continuous-section-exact-triangles).

The two predicates only package the clauses of this node. All coefficient rings,
continuous-section realizations, tensor extensions, action categories, restrictions and
short-exact triangles are the existing constructions. The coefficient cases E and Omega
are stated together; Omega is not assumed complete.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
open Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction
open ContinuousRepresentation PrimeToEll

/-- The restriction clause of this node, with the three actual b_u components. A triangle
morphism includes its connecting-arrow square, with the canonical functor shift comparisons.
Source: direct-image proof paragraph (3), continuous-subquotient auxiliary
(blueprint: lem-sfb-continuous-section-exact-triangles). -/
def RestrictionTriangleCompatible (F : Type u) [NormedField F]
    (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (T : Triangle (DerivedCategory.{u + 1}
      (CondensedBar.Equivariant (coefficientRing F) P))) : Prop :=
  (derived (coefficientRing F) P).mapTriangle.obj T ∈
      distTriang (DerivedCategory.{u + 1} (CondensedBar.Modules (coefficientRing F))) ∧
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (v : H →ₜ* P),
    (groupDerived (coefficientRing F) v ⋙ derived (coefficientRing F) H).mapTriangle.obj T ∈
        distTriang (DerivedCategory.{u + 1} (CondensedBar.Modules (coefficientRing F))) ∧
    ∃ φ : (derived (coefficientRing F) P).mapTriangle.obj T ⟶
        (groupDerived (coefficientRing F) v ⋙ derived (coefficientRing F) H).mapTriangle.obj T,
      φ.hom₁ = (groupMap (coefficientRing F) v).app T.obj₁ ∧
      φ.hom₂ = (groupMap (coefficientRing F) v).app T.obj₂ ∧
      φ.hom₃ = (groupMap (coefficientRing F) v).app T.obj₃

/-- The exactness and triangle clauses for the actual scalar-extended subspace sequence.
The two arrows are characterized by postcomposition with the tensor-extended inclusion
and quotient, so no arbitrary replacement of the canonical maps is allowed. A splitting
of the underlying internal short complex is automatically natural in every profinite S.
Source: direct-image proof paragraph (3), continuous-subquotient auxiliary; Stacks 0152
(blueprint: lem-sfb-continuous-section-exact-triangles). -/
def ContinuousSectionExactTriangles (E F : Type u) [Field E] [NormedField F] [Algebra E F]
    (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (V : Type (u + 1)) [AddCommGroup V] [Module E V] (ρ : Representation E P V)
    (U : Submodule E V) (hU : ∀ p : P, U ≤ U.comap (ρ p)) : Prop :=
  ∃ (MU : Realization F P (Extended E F U)
        (extendedRepresentation E F U P (ρ.subrepresentation U hU)))
    (MV : Realization F P (Extended E F V) (extendedRepresentation E F V P ρ))
    (MQ : Realization F P (Extended E F (V ⧸ U))
        (extendedRepresentation E F (V ⧸ U) P (ρ.quotient U hU)))
    (i : MU.object ⟶ MV.object) (q : MV.object ⟶ MQ.object) (hz : i ≫ q = 0),
    RepresentsMap MU MV (U.subtype.baseChange F) i ∧
    RepresentsMap MV MQ (U.mkQ.baseChange F) q ∧
    (ShortComplex.mk (C := CondensedBar.Equivariant (coefficientRing F) P) i q hz).ShortExact ∧
    Nonempty ((ShortComplex.mk
      (C := CondensedBar.Equivariant (coefficientRing F) P) i q hz).map
      (CondensedBar.forgetAction (A := coefficientRing F) (G := P))).Splitting ∧
    ∃ hs : ((ShortComplex.mk
        (C := CondensedBar.Equivariant (coefficientRing F) P) i q hz).map
        (CochainComplex.singleFunctor
          (CondensedBar.Equivariant (coefficientRing F) P) 0)).ShortExact,
      DerivedCategory.triangleOfSES hs ∈
        distTriang (DerivedCategory.{u + 1} (CondensedBar.Equivariant (coefficientRing F) P)) ∧
      RestrictionTriangleCompatible F P (DerivedCategory.triangleOfSES hs)

/-- Continuous scalar realization preserves the subspace short exact sequence for both
permitted coefficient fields and its canonical restriction triangles.

Source: current blueprint, direct-image stability proof, paragraph (3), agent-extracted
continuous-section auxiliary; Stacks Tag 0152
(blueprint: lem-sfb-continuous-section-exact-triangles).

Proof plan:
1. Apply continuousCoefficient_subquotients to U. The induced subspace and quotient
   actions are jointly continuous and inclusion and projection are continuous equivariant
   linear maps. Lift a basis of V/U to V and apply the topological-basis-lift-section lemma
   over E. It gives a continuous linear section s. The formula v - s(q(v)) gives a
   continuous retraction into U. The identities ri=1, qs=1, rs=0 and ir+sq=1 follow.
2. Extend these four maps by tensors to F=E and F=Omega. Choose compatible finite bases
   of U, V and V/U. Their matrices are finite, so the maps are continuous for the recorded
   product module topologies, and their splitting identities persist. Matrix entries of
   the induced group actions are continuous, hence the extended actions are jointly
   continuous. No completeness of Omega is used.
3. Apply exists_realization and exists_unique_map from continuous-representation
   condensation. Postcomposition gives the canonical i and q. The nonequivariant s and r
   give internal-module maps after forgetting the action. Precomposition commutes with
   postcomposition, so this splitting is natural in every profinite parameter. Exactness
   detection in condensed-derived-restriction-calculus gives equivariant short exactness.
4. Place the sequence in degree zero and use triangleOfSES and
   triangleOfSES_distinguished (lem-weil-pbc-complex-ses-triangle). Derived invariants and
   derived restriction are triangulated, so both image triangles are distinguished.
5. Naturality of groupMap at i, q and the actual triangleOfSES connecting arrow, together
   with groupMapShift, gives a morphism of image triangles with the three specified b_u
   components. Its third commutativity equation is the connecting square, for every
   topological H and continuous homomorphism H to P. The splitting is never required
   equivariant, and invariants are never required exact. -/
theorem continuousSection_exact_triangles (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (P : ProfiniteGrp.{u}) (V : Type (u + 1)) [AddCommGroup V] [Module E V]
    (ρ : Representation E P V)
    (_hV : Representation.IsContinuousCoefficient ℓ E P V
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv E V).toMonoidHom.comp ρ.asGroupHom))
    (U : Submodule E V) (hU : ∀ p : P, U ≤ U.comap (ρ p)) :
    ContinuousSectionExactTriangles E E P V ρ U hU ∧
      ContinuousSectionExactTriangles E Ω P V ρ U hU := by
  sorry

end Profinite.CondensedAction
