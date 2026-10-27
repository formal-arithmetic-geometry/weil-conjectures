/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # The supported finite scalar model hull

Source: the explicit hull in lem-sfb-supported-hull-proetale-descent, below blueprint
latest det-sf-comp-coherence-cocycle, refinement paragraph. HRS Sections 3--4 give
only the ambient setting (blueprint: def-sfb-supported-model-hull).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite support chains, including the empty chain. A closed edge has quasi-compact
open complement, expressed by compactness of its complementary subset.
Source: explicit support-chain convention in lem-sfb-supported-hull-proetale-descent
(blueprint: def-sfb-supported-model-hull). -/
inductive ScalarModelSupportChain : Scheme.{u} → Scheme.{u} → Type (u + 1)
  | nil (X : Scheme.{u}) : ScalarModelSupportChain X X
  | openStep {X U W : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (tail : ScalarModelSupportChain U W) : ScalarModelSupportChain X W
  | closedStep {X Z W : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (complement : IsCompact ((Set.range i.base)ᶜ))
      (tail : ScalarModelSupportChain Z W) : ScalarModelSupportChain X W

/-- The actual ordinary extension functor of a support chain: open extension by zero,
closed direct image, and the identity for the empty chain.
Source: explicit support-chain convention in lem-sfb-supported-hull-proetale-descent
(blueprint: def-sfb-supported-model-hull). -/
def ScalarModelSupportChain.extension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X W : Scheme.{u}} (p : ScalarModelSupportChain X W) :
    Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  match X, W, p with
  | _, _, .nil _ => 𝟭 _
  | _, _, @ScalarModelSupportChain.openStep _ _ _ j _ _ tail =>
      tail.extension Λ ⋙ CondensedRing.openImmersionLowerShriek Λ j
  | _, _, @ScalarModelSupportChain.closedStep _ _ _ i _ _ tail =>
      tail.extension Λ ⋙ CondensedRing.lowerStar Λ i

/-- The full replete classes used in the supported hull intersection. Products are
ordinary derived products. Filtered colimits are colimits of strict diagrams of
complexes with a common termwise lower bound, not arbitrary derived colimits.
Source: explicit hull convention in lem-sfb-supported-hull-proetale-descent
(blueprint: def-sfb-supported-model-hull). -/
def IsSupportedModelHullClass
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) : Prop :=
  P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
  (∀ (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (i : K ⟶ L) (p : L ⟶ K), i ≫ p = 𝟙 K → P L → P K) ∧
  (∀ (I : Type (u + 1))
    (K : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (c : Cone (Discrete.functor K)), IsLimit c → (∀ i : I, P (K i)) → P c.pt) ∧
  (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (a : ℤ), (∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).X n)) →
      (∀ i : I, P (DerivedCategory.Q.obj (D.obj i))) →
      ∀ c : Cocone D, IsColimit c → P (DerivedCategory.Q.obj c.pt)) ∧
  (∀ (W : Scheme.{u}) (p : ScalarModelSupportChain X W)
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)),
    HasFiniteConstantLocalModel Λ W L →
      P ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L)))

/-- Membership in the intersection of all admissible full replete classes containing
all supported finite scalar local models in degree zero.
Source: explicit hull convention in lem-sfb-supported-hull-proetale-descent
(blueprint: def-sfb-supported-model-hull). -/
def supportedModelHull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  fun K ↦ ∀ P, IsSupportedModelHullClass Λ X P → P K

end AlgebraicGeometry.ProEtale
