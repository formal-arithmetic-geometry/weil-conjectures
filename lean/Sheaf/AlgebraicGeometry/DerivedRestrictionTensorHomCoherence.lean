/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.Algebra.Homology.HomComplexRestrictOpen
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Coherent derived tensor and Hom restriction
Source: Stacks Project, Tags 08DJ, 08DL and 079U.
(blueprint: lem-sc-derived-restriction-tensor-hom-coherence).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

/-- Exact open restriction has simultaneous tensor and internal-Hom comparisons
compatible with the canonical tensor-Hom bijections.
Source: Stacks Project, Tags 079U, 08DL and 08DJ.
(blueprint: lem-sc-derived-restriction-tensor-hom-coherence).

Proof: compute the tensor comparison on K-flat representatives of its arguments.
Restrict their total tensor termwise and use preservation of K-flatness. The
localization factorization identifies this with restriction of derived tensor.
Naturality on complexes descends through quasi-isomorphisms to arbitrary derived
maps, giving the displayed tensor naturality square. For an open immersion,
ordinary restriction is exact, so it computes derived pullback in Tag 079U.
Common K-flat resolutions identify the comparisons for different representatives;
their inverses give the same square for roofs. Compute internal Hom with
K-injective representatives of the second argument; restriction preserves these
and identifies the Hom complexes termwise. Transport through the over-site
module equivalence, obtaining the Hom comparison. Choose these comparisons from
the same termwise restriction maps. On each total-tensor summand, restricting
uncurrying evaluates the same local linear map as uncurrying after restriction.
Thus their evaluation square commutes on representatives. With a K-flat model
of the second tensor factor, its Hom into a K-injective is K-injective, so every
map from an arbitrary first factor is represented modulo homotopy. Uncurrying
preserves homotopies. The representative characterization and uniqueness of the
canonical tensor-Hom family therefore give the evaluation equation for every
derived map. The construction includes zero objects and the empty open. -/
theorem exists_derivedRestriction_tensorHom_coherence
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))] :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let HU := derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf
    ∃ (t : ∀ K L : schemeDerivedCategory X, R.obj (K ⊗ L) ≅ R.obj K ⊗ R.obj L)
      (h : ∀ L E, R.obj (H.obj (op L, E)) ≅ HU.obj (op (R.obj L), R.obj E)),
      (∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
        R.map (a ⊗ₘ b) ≫ (t K' L').hom =
          (t K L).hom ≫ (R.map a ⊗ₘ R.map b)) ∧
      (∀ K L E (ξ : K ⟶ H.obj (op L, E)),
        (t K L).hom ≫ schemeDerivedTensorHomEquiv U.toScheme
          (R.obj K) (R.obj L) (R.obj E) (R.map ξ ≫ (h L E).hom) =
        R.map (schemeDerivedTensorHomEquiv X K L E ξ)) := by sorry

end AlgebraicGeometry.Scheme
