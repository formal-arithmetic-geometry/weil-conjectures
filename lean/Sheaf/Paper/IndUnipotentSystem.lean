/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ContinuousRepresentationCondensation
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Countable systems of finite unipotent norm representations

Source: main-20261015 direct-image stability proof, paragraph (3), rank-one
ind-unipotent analytic input (blueprint: def-sfb-ind-unipotent-system).

The p-adic integer group is written multiplicatively and lifted to the site universe.
Every finite vector space has its finite-dimensional module topology. Scalar extension
and continuous-section realization are the existing constructions, without completion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction.IndUnipotent

/-- The additive p-adic integer group, with its original topology, in the site universe.
Source: paragraph (3), rank-one input (blueprint: def-sfb-ind-unipotent-system). -/
abbrev IntegerGroup (ℓ : ℕ) [Fact ℓ.Prime] := Multiplicative (ULift.{u} (PadicInt ℓ))

/-- The additive integer 1, as a group element. The multiplicative identity represents 0.
Source: paragraph (3), tau (blueprint: def-sfb-ind-unipotent-system). -/
def generator (ℓ : ℕ) [Fact ℓ.Prime] : IntegerGroup.{u} ℓ :=
  Multiplicative.ofAdd (ULift.up 1)

/-- The universe lift retains total disconnectedness of the ultrametric integer space.
Source: paragraph (3), profinite H (blueprint: def-sfb-ind-unipotent-system). -/
instance integerGroupDisconnected (ℓ : ℕ) [Fact ℓ.Prime] :
    TotallyDisconnectedSpace (IntegerGroup.{u} ℓ) :=
  (Topology.IsEmbedding.isTotallyDisconnected_range
    (Topology.IsEmbedding.uliftDown (X := PadicInt ℓ))).1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E] [Algebra ℚ_[ℓ] E]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The given sequence, nilpotent operators, and commuting continuous actions.
The exponential formula uniquely specifies the second-factor action; its joint
continuity follows from its finite polynomial formula. No common exponent is imposed.
Source: paragraph (3), rank-one input (blueprint: def-sfb-ind-unipotent-system). -/
structure System where
  /-- Vector spaces may have arbitrarily large finite dimensions. -/
  V : ℕ → ModuleCat.{u + 1} E
  /-- Each stage is finite dimensional, including dimension zero. -/
  finite : ∀ n : ℕ, FiniteDimensional E (V n)
  /-- Injective successive linear transitions. -/
  transition : ∀ n : ℕ, V n ⟶ V (n + 1)
  /-- These realize the inclusions in the statement. -/
  injective : ∀ n : ℕ, Function.Injective (transition n)
  /-- The nilpotent infinitesimal operators. -/
  operator : ∀ n : ℕ, Module.End E (V n)
  /-- A separate exponent at each stage. -/
  exponent : ℕ → ℕ
  /-- The exponents are positive. -/
  positive : ∀ n : ℕ, 1 ≤ exponent n
  /-- Finite-stage nilpotence. -/
  nilpotent : ∀ n : ℕ, operator n ^ exponent n = 0
  /-- Operators commute with the transition maps. -/
  compatible : ∀ (n : ℕ) (v : V n),
    transition n (operator n v) = operator (n + 1) (transition n v)
  /-- The action includes the original G action and the uniquely specified exponential. -/
  action : ∀ n : ℕ, Representation E (G × IntegerGroup.{u} ℓ) (V n)
  /-- Joint continuity for the finite-dimensional norm topology. -/
  continuous : ∀ n : ℕ,
    @Continuous ((G × IntegerGroup.{u} ℓ) × V n) (V n)
      (@instTopologicalSpaceProd _ _ inferInstance (moduleTopology E (V n)))
      (moduleTopology E (V n)) (fun x ↦ action n x.1 x.2)
  /-- The operator commutes with the original G action. -/
  commutes : ∀ (n : ℕ) (g : G) (v : V n),
    operator n (action n (g, 1) v) = action n (g, 1) (operator n v)
  /-- Transition maps intertwine both actions. -/
  equivariant : ∀ (n : ℕ) (g : G × IntegerGroup.{u} ℓ) (v : V n),
    transition n (action n g v) = action (n + 1) g (transition n v)
  /-- The second-factor action is exactly the finite exponential, with no convergence claim. -/
  exponential : ∀ (n : ℕ) (h : IntegerGroup.{u} ℓ) (v : V n),
    action n (1, h) v = ∑ j ∈ Finset.range (exponent n),
      ((algebraMap ℚ_[ℓ] E (h.toAdd.down : ℚ_[ℓ])) ^ j / (j.factorial : E)) •
        ((operator n ^ j) v)

attribute [instance] System.finite

end Profinite.CondensedAction.IndUnipotent

namespace Profinite.CondensedAction.IndUnipotent
open AlgebraicGeometry.ProEtale
open ContinuousRepresentation PrimeToEll

variable (ℓ : ℕ) [Fact ℓ.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [Algebra ℚ_[ℓ] E] [Algebra E F]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (T : System ℓ E G)

/-- An actual diagram of continuous-section realizations and its specified tensor
transition maps. The isomorphisms allow every realization of these sheaves, not a choice
of an unspecified object. The colimit is taken separately in the full action category.
Source: paragraph (3), M_n and their transitions (blueprint: def-sfb-ind-unipotent-system). -/
structure Presentation where
  /-- The diagram in the ordinary internal action category. -/
  diagram : ℕ ⥤ ActionModule (normContinuousRing F) (G × IntegerGroup.{u} ℓ)
  /-- Existing realizations use precisely the tensor-product norm topology. -/
  stage : ∀ n : ℕ, Realization F (G × IntegerGroup.{u} ℓ)
    (Extended E F (T.V n))
    (extendedRepresentation E F (T.V n) (G × IntegerGroup.{u} ℓ) (T.action n))
  /-- Identify each diagram object with its specified continuous-section realization. -/
  identify : ∀ n : ℕ, diagram.obj n ≅ (stage n).object
  /-- Each transition is the scalar extension of the original inclusion, on every section. -/
  transition : ∀ (n : ℕ) (S : Profinite.{u})
    (m : sectionModule (normContinuousRing F) (stage n).object.module S) (s : S),
    ((stage (n + 1)).sections S
      ((((identify n).inv ≫ diagram.map (homOfLE (Nat.le_succ n)) ≫
        (identify (n + 1)).hom).val.hom.hom.app (op S)).hom m)).down s =
      ((T.transition n).hom.baseChange F) (((stage n).sections S m).down s)

end Profinite.CondensedAction.IndUnipotent

namespace Profinite.CondensedAction.IndUnipotent

/-- Continuous coefficient inclusions give the specified presentation, so this data
adds no restriction on the finite-stage system. No presentation is chosen from this
existence theorem by any definition in this module.
Source: paragraph (3), definition of M_n (blueprint: def-sfb-ind-unipotent-system).

Proof: at each stage, extend the given representation by the existing algebraic tensor
product. A finite basis identifies its module topology with the finite product topology;
the action matrix entries are continuous by continuity of the original action and of
the coefficient inclusion. Thus the extended joint action is continuous. Apply
ContinuousRepresentation.exists_realization. Extend each transition by F tensor_E -;
it is continuous in finite-dimensional coordinates and intertwines the actions. The
unique morphism supplied by ContinuousRepresentation.exists_unique_map has precisely
the required section formula. Functor.ofSequence makes these successive maps into a
natural-number diagram. Its objects are the chosen realizations, with identity
identifications. Uniqueness of the morphisms gives all composite transition formulas.
Zero-dimensional stages and noncomplete F use exactly the same construction. -/
theorem exists_presentation (ℓ : ℕ) [Fact ℓ.Prime]
    (E F : Type u) [NormedField E] [NormedField F]
    [Algebra ℚ_[ℓ] E] [Algebra E F]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (T : System ℓ E G) (hf : Continuous (algebraMap E F)) :
    Nonempty (Presentation ℓ E F G T) := by
  sorry

end Profinite.CondensedAction.IndUnipotent
