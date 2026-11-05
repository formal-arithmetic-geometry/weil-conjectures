/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-!
# Compatibility of normalized towers with retained étale origins

Source: blueprint, def-weil-pbc-witness-compatibility, order 1352;
Stacks Tags 09C9, 09C2, 06YY and 07A4
(blueprint: def-weil-pbc-witness-compatibility).

All finite coefficient categories use their canonical fixed-ring presentation. The
coefficient realization in def-weil-pbc-proetale-modules identifies them with modules
over the continuous-function coefficient sheaf. All outputs are ambient derived objects.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

-- The kernel need not be finitely generated: each local tensor lift is a finite sum.

-- Elaborate the shared site instances sequentially.
set_option Elab.async false

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

attribute [local irreducible] scalarDerivedAdjunctionData

-- Keep the scalar adjunction data folded when elaborating the chosen left adjoints.
attribute [local irreducible] scalarDerivedAdjunction scalarExtension scalarAdjunction

/-- Derived restriction of scalars has a left adjoint for an arbitrary coefficient map.
Source: Stacks 06YY and 06XN (blueprint: def-weil-pbc-witness-compatibility).
Proof: sheafify sectionwise scalar extension. Its composite with restriction is tensoring
by the constant coefficient module sheaf, so it preserves quasi-isomorphisms between
K-flat complexes. The ordinary adjunction therefore descends to the derived categories.
Exactness identifies derived restriction with the actual induced functor. Neither
flatness of the coefficient map nor boundedness is required. -/
@[instance] theorem pbcRestriction_isRightAdjoint {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (Sheaf.derivedRestrictScalars J φ).IsRightAdjoint := by
  exact (scalarDerivedAdjunction J φ).isRightAdjoint

variable (T : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

-- Restricting the site commutes with the pointwise coextension adjunction.

attribute [local irreducible] pbcComparisonRestrict

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {A : Type (u + 1)} [CommRing A]

/-- A morphism retains both levelwise maps and both normalization compatibilities.
Source: blueprint order 1352 (blueprint: def-weil-pbc-witness-compatibility). -/
@[ext] structure PbcWitnessedTowerHom {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P Q : PbcWitnessedTower T d) where
  /-- The underlying ambient maps. -/
  u : ∀ n : ℕ, P.K n ⟶ Q.K n
  /-- The maps on the retained étale origins. -/
  v : ∀ n : ℕ, (P.origin n).L.obj ⟶ (Q.origin n).L.obj
  /-- Compatibility with pro-étale normalizations. -/
  theta_naturality : ∀ n : ℕ,
    (pbcWitnessReduction T d n).map (u (n + 1)) ≫ (Q.theta n).hom =
      (P.theta n).hom ≫ u n
  /-- Compatibility with étale normalizations. -/
  beta_naturality : ∀ n : ℕ,
    (pbcWitnessEtaleReduction T d n).map (v (n + 1)) ≫ (Q.beta n).hom =
      (P.beta n).hom ≫ v n
  /-- The square involving the two retained comparison isomorphisms commutes. -/
  origin_naturality : ∀ n : ℕ,
    (P.alpha n).hom ≫ u n =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (v n) ≫ (Q.alpha n).hom

end AlgebraicGeometry.ProEtale
