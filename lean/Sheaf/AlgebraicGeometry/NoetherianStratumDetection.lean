/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Detection by pro-etale covers of finitely many locally closed strata

Source: Stacks Project, Tags 09AH and 09AB, followed by finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Module inverse image over its actual inverse-image ring is exact, including for
noncommutative rings. Source: Stacks, Tag 04JC, first assertion, and Tag 03DA
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
Proof: apply sitePullback_abelian_exact to the underlying abelian inverse image.
The module action is the inverse image of the original action under the finite-product
comparison. Module kernels and cokernels have the underlying abelian kernels and
cokernels, so this functor preserves both; its maps preserve addition. No change to
an independently chosen coefficient ring, or flatness assumption, is involved. -/
theorem proEtaleRingModuleInverseImage_exact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (proEtaleRingModuleInverseImage f R).Additive ∧
    PreservesFiniteLimits (proEtaleRingModuleInverseImage f R) ∧
    PreservesFiniteColimits (proEtaleRingModuleInverseImage f R) := by
  sorry

/-- Additivity of inverse image. Source: Stacks, Tag 04JC
(blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleRingModuleInverseImage_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (proEtaleRingModuleInverseImage f R).Additive :=
  (proEtaleRingModuleInverseImage_exact f R).1

/-- Left exactness of inverse image. Source: Stacks, Tag 04JC
(blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleRingModuleInverseImage_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleRingModuleInverseImage f R) :=
  (proEtaleRingModuleInverseImage_exact f R).2.1

/-- Right exactness of inverse image. Source: Stacks, Tag 04JC
(blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleRingModuleInverseImage_preservesFiniteColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleRingModuleInverseImage f R) :=
  (proEtaleRingModuleInverseImage_exact f R).2.2

/-- The ordinary localization at quasi-isomorphisms for modules over any ring sheaf.
Source: Stacks, Tag 05RU (blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleAllRingModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    HasDerivedCategory (ringedSiteModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- The canonical termwise inverse image on the unbounded derived category, with
coefficients the inverse-image ring. This is Mathlib's exact-functor localization.
Source: Stacks, Tag 015F (blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable abbrev proEtaleAllRingDerivedInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :=
  (proEtaleRingModuleInverseImage f R).mapDerivedCategory

/-- Abelian sheaves are detected by the chosen pro-etale covers of all strata.
Source: Stacks, Tags 09AH and 09AB, and finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
Proof: adjunction and the sectionwise base-change formula for direct image identify
successive inverse images with inverse image along the composite, including identities.
For a covering, localization identifies inverse image with slice restriction; the sheaf
separatedness axiom on base-changed covers detects zero sections. Thus covering
restrictions detect zero sheaves. Induct on the number of nonempty strata. The empty
scheme has only zero abelian sheaves by the empty-cover axiom. Factor each stratum as a
closed immersion into an open neighborhood. Those neighborhoods cover X. Their open
complements are Noetherian and their open inclusions are quasi-compact. Base change the
remaining strata to the complement and discard the empty chosen stratum; induction
makes the restriction there zero. The closed restriction is also zero. The exact
open/closed sequence of Tag 09AH gives zero on each neighborhood; covering detection
gives zero globally. Actual immersion structures are retained, also for nonreduced strata.
The constant integer sheaf action allows use of module localization and detection. -/
theorem proEtale_isZero_of_stratum_cover (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : LocallyClosedStratification X)
    (V : ∀ a : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain a))
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (hF : ∀ (a : Fin S.n) (j : (V a).I₀),
      IsZero ((proEtaleSheafInverseImage ((V a).f j ≫ S.immersion a)
        AddCommGrpCat.{u + 1}).obj F)) : IsZero F := by
  sorry

/-- These exact termwise restrictions jointly detect zero objects and isomorphisms
in the unbounded derived category of modules over every ring sheaf.
Source: Stacks, Tags 09AH, 05RU, 015F and 0149, and finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
Proof: exactness identifies the cohomology of each restricted complex with the
restriction of its cohomology. Apply proEtale_isZero_of_stratum_cover to the underlying
abelian cohomology sheaves in every integer degree. A complex with zero cohomology
becomes zero in the localization, because its map from the zero complex is a
quasi-isomorphism. This detects zero without a boundedness condition. For a morphism,
complete it to a distinguished triangle. Exact termwise restriction is triangulated.
If all restricted morphisms are invertible, all restricted cones have zero cohomology
and hence are zero. Joint zero detection makes the global cone zero. Exactness of
Hom(W,-) on this triangle and its rotations makes Hom(W,f) bijective for every W;
taking W to be its target and source supplies a two-sided inverse. Conversely, additive
functors preserve zero objects and all functors preserve isomorphisms. Composite
restrictions agree canonically with successive stratum and cover restrictions by the
adjunction composition formula, so the composite notation includes precisely the
inverse images in the informal statement. -/
theorem proEtale_derived_stratum_cover_detection (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : LocallyClosedStratification X)
    (V : ∀ a : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain a))
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    (∀ K : DerivedCategory (ringedSiteModules.{u + 1} R),
      (∀ (a : Fin S.n) (j : (V a).I₀),
        IsZero ((proEtaleAllRingDerivedInverseImage
          ((V a).f j ≫ S.immersion a) R).obj K)) → IsZero K) ∧
    (∀ (K L : DerivedCategory (ringedSiteModules.{u + 1} R)) (f : K ⟶ L),
      (∀ (a : Fin S.n) (j : (V a).I₀),
        IsIso ((proEtaleAllRingDerivedInverseImage
          ((V a).f j ≫ S.immersion a) R).map f)) → IsIso f) := by
  sorry

end AlgebraicGeometry.Scheme
