/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedSections
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ModuleSheafCoproductLocalSupport
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport
import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Supported sections and flasqueness for a pro-etale open-closed pair

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/def-pur-flasque-support.md;
Stacks Project, Tags 03DA, 09BN and 09AH (blueprint: def-pur-flasque-support).

The existing `finiteSupportedSections` and `finiteClosedUpperShriek` give the kernel functor
and its closed inverse image. Constant-coefficient module sheaves are presented as
sheaves valued in `ModuleCat`, without a constructibility condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A module sheaf is flasque for the pair with open complement `j` when its open
adjunction unit is an epimorphism of sheaves. This is a sheaf condition, with no
objectwise surjectivity assertion. Source: blueprint def-pur-flasque-support, final
paragraph; Stacks Tag 03DA (blueprint: def-pur-flasque-support). -/
def IsFlasqueForOpen (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app I)

/-- The canonical comparison `G_Z ⟶ s_*s^!`, obtained by applying the closed
adjunction unit to the supported kernel. It is defined even when the open complement
is not quasi-compact. Source: blueprint def-pur-flasque-support, comparison paragraph;
Stacks Tag 09AH (blueprint: def-pur-flasque-support). -/
noncomputable def finiteSupportedClosedComparison (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X) :
    finiteSupportedSections Λ j ⟶
      finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s :=
  Functor.whiskerLeft (finiteSupportedSections Λ j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit

/-- Supported sections are exactly the sections whose restriction to `V ×[X] U`
is zero, and the canonical inclusion is injective on sections. The site adjunction's
counit is the projection `V ×[X] U ⟶ V`, regarded as an arrow of `X.ProEt`.
Source: blueprint def-pur-flasque-support, explicit section formula; Stacks Tags 03DA
and 09BN (blueprint: def-pur-flasque-support).

Proof (step 1 of the node): kernels are sectionwise by
`def-weil-sheaf-of-modules-category`. The initial object of the open inverse-image
indexing category identifies `j^*` with restriction; on a skeleton use an isomorphic
representative. The identifications commute with arrows by functoriality. The unit
therefore becomes restriction along the fibre-product projection. Naturality of the
unit induces the kernel maps, preserving the same restrictions. -/
theorem finiteSupportedSections_sections (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (V : X.ProEt) :
    Function.Injective (((finiteSupportedSectionsι Λ j).app M).hom.app (op V)) ∧
    Set.range (((finiteSupportedSectionsι Λ j).app M).hom.app (op V)) =
      {m | M.obj.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
          trivial).counit.app V).op m = 0} := by
  sorry

/-- Both the supported-kernel functor and its closed inverse image are left exact.
Source: blueprint def-pur-flasque-support, left-exactness paragraph; Stacks Tag 03DA
(blueprint: def-pur-flasque-support).

Proof (step 3): a supported section in the kernel of a map lifts uniquely through
any preceding monomorphism, because kernels are sectionwise. Restricting the lift to
the open complement and using injectivity proves that this lift is itself supported.
The zero sheaf maps to zero, and induced kernel maps respect addition. This gives
left exactness of the supported-kernel functor. Apply the exact constant-coefficient
closed inverse image (`prop-weil-pbc-proetale-constant-exact`) to obtain left exactness
of its composite `finiteClosedUpperShriek`. No quasi-compactness is used. -/
theorem finiteSupportedSections_leftExact (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hPair : IsCompl (Set.range s) (Set.range j)) :
    PreservesFiniteLimits (finiteSupportedSections Λ j) ∧
      PreservesFiniteLimits (finiteClosedUpperShriek Λ s j) := by
  sorry

/-- With quasi-compact open complement, the specified natural comparison is an
isomorphism. Source: blueprint def-pur-flasque-support, comparison paragraph;
Stacks Tag 09AH (blueprint: def-pur-flasque-support).

Proof (step 2): step 1 identifies the restriction of the supported kernel to U with
zero, since there the restriction map is an identity. Apply the canonical-unit
clause of `lem-exc-proetale-closed-essential-image` to the supported kernel, with
its quasi-compact-complement hypothesis. This is precisely the displayed comparison,
and its naturality makes the objectwise isomorphisms a natural isomorphism. -/
theorem finiteSupportedClosedComparison_isIso (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X Z U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s) (Set.range j)) :
    IsIso (finiteSupportedClosedComparison Λ s j) := by
  sorry

/-- Pair-flasqueness is equivalent to vanishing of the sheaf cokernel of the open
unit. Source: blueprint def-pur-flasque-support, final paragraph; Stacks Tag 03DA
(blueprint: def-pur-flasque-support).

Proof (step 4): in the abelian module-sheaf category a map is epic exactly when its
cokernel is zero. This uses the sheaf cokernel, which is sheafified; it does not
assert surjectivity of section maps on every site object. -/
theorem isFlasqueForOpen_iff_isZero_cokernel (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    IsFlasqueForOpen Λ j I ↔
      IsZero (cokernel ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app I)) := by
  sorry

/-- The comparison can fail for an affine base and a non-quasi-compact complement,
with any nonzero finite commutative coefficient ring. Source: the counterexample in
steps 5--7 of node def-pur-flasque-support (blueprint: def-pur-flasque-support).

Proof:
5. Take a field k, R = product over positive integers of k, and the ideal J of
finite-support sequences. Set X = Spec R, Z = Spec (R/J), and let U be the union of
the pairwise disjoint clopen coordinate points X_n. This open is not quasi-compact.
Let H_n be the direct image of the constant rank-one sheaf from X_n. In P = product
of H_n let S be tuples locally of finite coordinate support. The sheaf condition
and finite-support gluing identify S with the coproduct. Put F = coker(S ⟶ P).
6. The closed inverse image kills each H_n: every indexing object can be restricted
to the complement of X_n. Closed inverse image preserves products by
`lem-weil-pbc-proetale-immersion-limit-preservation` and preserves coproducts by its
adjunction, so it kills P and S. Its exactness kills F. Open restriction of S ⟶ P
is an isomorphism on each X_n, so j^*F = 0 as well.
7. On an affine object, the finite affine refinement of a pro-etale cover shows
that a section of S has globally finite coordinate support. The tuple (1,1,...)
over X therefore is not in S(X). Sectionwise kernels imply its image in F(X) is
nonzero. Hence G_Z F = F is nonzero whereas s^!F = 0, and the comparison is not
an isomorphism. The module-sheaf product/coproduct facts are
`lem-weil-pbc-module-sheaves-colimits-forgetful`, and inverse-image exactness is
`prop-weil-pbc-proetale-constant-exact`. -/
theorem exists_finiteSupportedClosedComparison_not_isIso (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [Nontrivial Λ] :
    ∃ (X Z U : Scheme.{u}) (s : Z ⟶ X) (j : U ⟶ X),
      IsAffine X ∧ IsClosedImmersion s ∧ IsOpenImmersion j ∧
      IsCompl (Set.range s) (Set.range j) ∧ ¬ QuasiCompact j ∧
      ∃ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
        ¬ IsIso ((finiteSupportedClosedComparison Λ s j).app M) := by
  sorry

end AlgebraicGeometry.ProEtale
