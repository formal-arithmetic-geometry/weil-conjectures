/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars

/-! # K-flat invariance for fixed-coefficient sheaf scalar extension

Source: Stacks 06YY and 06XN, clause (1) of the derived change-of-rings lemma
(blueprint: lem-pur-derived-change-of-rings).
This companion retains the existing interface and exposes its K-flat invariance clause.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Sheaf

/-- Countable coproducts are the countable instances of the existing sheaf colimits.
Source: the Grothendieck module-sheaf category in Stacks 06YY
(blueprint: lem-pur-derived-change-of-rings). -/
instance fixedCoefficientCountableCoproducts
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A] :
    HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} A)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0}
    (Sheaf J (ModuleCat.{u + 1} A))).has_colimits_of_shape _⟩

/-- Scalar extension preserves quasi-isomorphisms between K-flat module-sheaf complexes
for every coefficient map. Source: Stacks 06YY, 06XN
(blueprint: lem-pur-derived-change-of-rings).

Proof: give B its A-algebra structure through the specified ring homomorphism.
Restriction of extended sheaves is naturally tensor with the constant B-module,
by extendScalarsCompRestrictScalarsIso. The cone of a quasi-isomorphism between
K-flat complexes is acyclic and K-flat, so tensoring it with that module is acyclic.
Exact faithful restriction reflects acyclicity. Thus the extended morphism is a
quasi-isomorphism. This is the first clause of the node and the existing local
argument inside fixedCoefficientDerivedRestriction_isRightAdjoint. No flatness,
nontriviality, or surjectivity of the coefficient map is required. -/
theorem fixedCoefficientPreservesKFlat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (extendScalars J φ).PreservesKFlatQuasiIso := by
  sorry
end CategoryTheory.Sheaf
