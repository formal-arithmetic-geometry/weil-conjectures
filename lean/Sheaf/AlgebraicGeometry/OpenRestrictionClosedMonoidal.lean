/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom

import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.Algebra.Homology.HomComplexRestrictOpen
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.AlgebraicGeometry.OpenRestrictionTensorNaturality
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-! # Closed monoidal comparisons for open restriction

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-pc-open-restriction-closed-monoidal).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-open-restriction-closed-monoidal). -/
local instance closedRestrictionStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- Exact restriction carries compatible strong tensor and internal-Hom comparisons.

Source: Stacks Project, cohomology.tex, Tags 06YH, 08DJ and 08DL.
(blueprint: lem-pc-open-restriction-closed-monoidal).

Proof: choose K-flat representatives for both tensor inputs. Exact restriction
preserves their K-flatness, and its termwise sheaf-tensor comparison, summed over
all bidegrees of each total degree, identifies their total tensors. Descend this
natural comparison through localization and the over-site equivalence. Use
`Scheme.Modules.pullbackMonoidal` transported along the ordinary restriction
isomorphism for the termwise coherence, rather than choosing unrelated tensor
comparisons. Restrict
the structure sheaf in degree zero to obtain the unit comparison. Associativity
and both unit laws hold on pure tensors of the sheaf representatives, hence on
complexes and after localization; the inverse tensor comparisons define m.
Resolve each Hom target by the fixed functorial K-injective resolution. Its open
restriction is K-injective. The product Hom-complex comparison restricts each
local map and respects the signed differential. Localize and transport through
the over equivalence to obtain h. Choose h using these same restriction maps.
On each total-tensor summand, restricting an uncurried local map is the same as
uncurrying its restriction. This proves the displayed equation on chain maps.
By `CochainComplex.isKInjective_homComplex_of_isKFlat` (Stacks Tag 0A96),
Hom from a K-flat second argument into a K-injective is K-injective, so every
morphism into this Hom is represented modulo homotopy; uncurrying respects that
homotopy. Common K-flat resolutions and naturality give the equation for all
objects. The universal localization factorizations compare the independently
specified universes. All comparisons and laws apply also to zero complexes and
the empty open. No evaluation map is asserted to be invertible. -/
theorem exists_openRestriction_closedMonoidal (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
    let HU := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    ∃ m : R.Monoidal,
      letI := m
      ∃ h : ∀ K N : schemeDerivedCategory X,
        R.obj (H.obj (op K, N)) ≅ HU.obj (op (R.obj K), R.obj N),
        ∀ A K N (ξ : A ⟶ H.obj (op K, N)),
          schemeDerivedTensorHomEquiv U.toScheme (R.obj A) (R.obj K) (R.obj N)
            (R.map ξ ≫ (h K N).hom) =
          (Functor.Monoidal.μIso R A K).hom ≫
            R.map (schemeDerivedTensorHomEquiv X A K N ξ) := by sorry

end AlgebraicGeometry
