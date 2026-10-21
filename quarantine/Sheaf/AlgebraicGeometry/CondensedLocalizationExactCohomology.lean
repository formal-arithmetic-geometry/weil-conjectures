/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Exact condensed coefficient localization and unbounded cohomology

Source: Stacks Project, sites.tex, Tag 03CE; sites-modules.tex, Tags 04IX, 03CY and
03EK; homology.tex, Tag 010N; derived.tex, Tag 015F.
(blueprint: lem-sfb-condensed-localization-exact-cohomology).

The coefficient ring and ordinary pullback are the existing sectionwise reconstruction
of the internal condensed coefficient operations. Restriction retains every section and
restriction map. Scalar transport uses the inverse coefficient isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wS wV

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale
namespace CondensedLocalization

open InternalModuleOperations

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {S : Scheme.{u}} (V : S.ProEt)

/-- The existing sectionwise ringed-topos pullback, with its source and target made
explicit at the chosen site object. No new pullback construction is chosen.
Source: Stacks 03D7 (blueprint: lem-sfb-condensed-localization-exact-cohomology). -/
noncomputable def pullback :
    SheafOfModules.{u + 1} (ring Λ S) ⥤ SheafOfModules.{u + 1} (ring Λ V.left) :=
  InternalModuleOperations.upperStar Λ V.hom

/-- The restriction of the existing section-ring sheaf to V, by composition of test
objects. Source: Stacks 04IX
(blueprint: lem-sfb-condensed-localization-exact-cohomology). -/
noncomputable abbrev restrictedRing : Sheaf (Scheme.ProEt.topology V.left) RingCat.{u + 1} :=
  (localizationRestriction RingCat.{u + 1} V.hom V.prop).obj (ring Λ S)

/-- Actual sectionwise module restriction to V before changing the coefficient action.
Source: Stacks 04IX (blueprint: lem-sfb-condensed-localization-exact-cohomology). -/
noncomputable def restriction :
    SheafOfModules.{u + 1} (ring Λ S) ⥤ SheafOfModules.{u + 1} (restrictedRing Λ V) :=
  letI := Scheme.ProEt.isContinuous_overMap (V := V.left) (U := S) V.prop
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.map (f := V.hom) ⊤ V.prop) (𝟙 (restrictedRing Λ V))

/-- Change the action through alpha inverse, retaining the underlying sections and maps.
This is Mathlib scalar restriction along the inverse ring-sheaf isomorphism.
Source: Stacks 03CV, 03EK
(blueprint: lem-sfb-condensed-localization-exact-cohomology). -/
noncomputable abbrev actionTransport (e : restrictedRing Λ V ≅ ring Λ V.left) :=
  SheafOfModules.restrictScalars.{u + 1} e.inv

/-- Sectionwise restriction followed by transport of the scalar action.
Source: Stacks 04IX, 03EK
(blueprint: lem-sfb-condensed-localization-exact-cohomology). -/
noncomputable abbrev localizedPullback (e : restrictedRing Λ V ≅ ring Λ V.left) :=
  restriction Λ V ⋙ actionTransport Λ V e

/-- Localized restriction with its transported action is additive: the section maps and
addition of morphisms are unchanged. Source: Stacks 04IX, 03CV
(blueprint: lem-sfb-condensed-localization-exact-cohomology).
Proof: Step 3 transports b acting on m to alpha inverse of b acting on m; on morphisms
this retains the same additive map. Restriction is sectionwise, so both preserve sums. -/
@[instance]
theorem localizedPullback_additive (e : restrictedRing Λ V ≅ ring Λ V.left) :
    (localizedPullback Λ V e).Additive := by
  sorry

/-- The actual ringed-topos pullback is additive.
Source: Stacks 03EK, 04IX (blueprint: lem-sfb-condensed-localization-exact-cohomology).
Proof: Steps 1--4 identify inverse image with localization, reconstruct alpha on section
rings, and identify tensor extension with action transport by b tensor m mapping to
alpha inverse of b times m. This is natural in module maps and preserves their sums. -/
@[instance]
theorem pullback_additive : (pullback Λ V).Additive := by
  sorry

/-- The actual ringed-topos pullback preserves finite limits.
Source: Stacks 04IX, 03EK (blueprint: lem-sfb-condensed-localization-exact-cohomology).
Proof: Steps 1--4 give sectionwise restriction followed by the coefficient-action
equivalence. Step 5 applies lem-pur-site-restriction-module-adjunction-exact to restriction,
lem-galois-equivalence-preserves-limits to transport, and
lem-sfb-finite-exactness-nat-iso to the comparison with actual pullback. -/
@[instance]
theorem pullback_preservesFiniteLimits :
    PreservesFiniteLimits (pullback Λ V) := by
  sorry

/-- The actual ringed-topos pullback preserves finite colimits.
Source: Stacks 04IX, 03EK (blueprint: lem-sfb-condensed-localization-exact-cohomology).
Proof: Steps 1--4 give sectionwise restriction followed by the coefficient-action
equivalence. Step 5 applies lem-pur-site-restriction-module-adjunction-exact to restriction,
lem-galois-equivalence-preserves-limits to transport, and
lem-sfb-finite-exactness-nat-iso to the comparison with actual pullback. Cokernels are
sheafified sectionwise cokernels, so this does not assert sectionwise surjectivity of epis. -/
@[instance]
theorem pullback_preservesFiniteColimits :
    PreservesFiniteColimits (pullback Λ V) := by
  sorry

/-- Localization, coefficient identification, action equivalence and the canonically
normalized sectionwise comparison for the actual ringed-topos pullback.
The site equivalence is the existing concrete composition functor `sliceEquiv.inverse`.
The equation for e identifies its additive map with the actual alpha after the canonical
inverse-image/restriction comparison. Being a ring-sheaf isomorphism includes all
restriction and multiplication compatibilities. The inverse of rho is the tensor-unit
map m to 1 tensor m: the module adjunction unit evaluated at the composite test object,
then restricted along the graph of W over V. Thus rho is fixed canonically.
Source: Stacks 03CE, 04IX, 03CY, 03EK
(blueprint: lem-sfb-condensed-localization-exact-cohomology).
Proof: Step 1 uses lem-weil-proetale-weakly-etale-localization and the coefficient-free
clause of lem-sfb-proetale-object-inverse-image-restriction. Step 2 reconstructs alpha
using lem-sfb-internal-module-operations-transport; its naturality and ring equations give
all section compatibilities. Step 3 transports the action by alpha inverse, with inverse
transport by alpha. Step 4 sends b tensor m to alpha inverse of b times m; balancing and
restriction compatibility extend it uniquely through sheafification. Its inverse sends
m to 1 tensor m. Both composites are identities on the tensor generators, hence after
sheafification; the same formula proves naturality. Step 5 transfers additivity and
finite exactness from restriction and the action equivalence. -/
theorem localization_comparison :
    (∀ (W : V.left.ProEt) (R : Sieve W),
      R ∈ Scheme.ProEt.topology V.left W ↔
        R.functorPushforward (Scheme.ProEt.sliceEquiv S V).inverse ∈
          (Scheme.ProEt.topology S).over V
            ((Scheme.ProEt.sliceEquiv S V).inverse.obj W)) ∧
    Nonempty (ProEtale.upperStar Ab.{u + 1} V.hom ≅
      localizationRestriction Ab.{u + 1} V.hom V.prop) ∧
    ∃ (e : restrictedRing Λ V ≅ ring Λ V.left),
      (∀ (W : V.left.ProEt) (a : (restrictedRing Λ V).obj.obj (op W)),
        (e.hom.hom.app (op W)).hom a =
          ((condensedPullbackHom Λ V.hom).hom.app (op W)).hom
            (((upperStarIsoLocalizationRestriction Ab.{u + 1} V.hom V.prop).inv.app
              (condensedRingObj Λ S)).hom.app (op W) a)) ∧
      (actionTransport Λ V e).IsEquivalence ∧
      ∃ rho : pullback Λ V ≅ localizedPullback Λ V e,
        ∀ (F : SheafOfModules.{u + 1} (ring Λ S)) (W : V.left.ProEt)
          (m : F.val.obj
            (op ((MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj W))),
          (rho.inv.app F).val.app (op W) m =
            ((pullback Λ V).obj F).val.map
              ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop
                trivial).unit.app W).op
              (((adjunction Λ V.hom).unit.app F).val.app
                (op ((MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj W)) m) := by
  sorry

variable [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (ring Λ S))]
  [HasDerivedCategory.{wV} (SheafOfModules.{u + 1} (ring Λ V.left))]

/-- The termwise restricted and action-transported complex represents the unbounded
derived pullback, for every representative of Q.
Source: Stacks 015F (blueprint: lem-sfb-condensed-localization-exact-cohomology).
Proof: Step 6 applies lem-weil-pbc-exact-functor-derived-factorization to the additive
exact pullback. Its factorization computes the derived image on every complex.
Naturality of rho with respect to each differential gives a complex isomorphism to the
termwise localized complex. Apply Q to that isomorphism, compose with the factorization,
and apply the derived functor to the chosen representation of Q. No resolution or
boundedness condition enters. -/
theorem localized_complex_represents
    (e : restrictedRing Λ V ≅ ring Λ V.left)
    (rho : pullback Λ V ≅ localizedPullback Λ V e)
    (K : CochainComplex (SheafOfModules.{u + 1} (ring Λ S)) ℤ)
    (Q : DerivedCategory.{wS} (SheafOfModules.{u + 1} (ring Λ S)))
    (a : DerivedCategory.Q.{wS}.obj K ≅ Q) :
    Nonempty ((pullback Λ V).mapDerivedCategory.{wS, wV}.obj Q ≅
      DerivedCategory.Q.{wV}.obj (((localizedPullback Λ V e).mapHomologicalComplex (.up ℤ)).obj
        K)) := by
  sorry

/-- The natural unbounded cohomology comparison, normalized on every complex by the
canonical kernel/image quotient comparison. The displayed equation says that the path
through derived cohomology and the termwise factorization is precisely the inverse of
`ShortComplex.mapHomologyIso`, after the source cohomology factorization.
Source: Stacks 010N, 015F and 04VG
(blueprint: lem-sfb-condensed-localization-exact-cohomology).
Proof: Step 7 inverts lem-weil-pbc-exact-functor-complex-cohomology. Its cycle, image and
quotient normalization gives the displayed equation. Both functors invert
quasi-isomorphisms, by exactness of pullback and the definition of cohomology. Apply
lem-weil-pbc-localization-universal-property (2) to descend the natural isomorphism.
This also proves naturality for arbitrary derived arrows, not only complex maps.
The construction works independently in every integer degree. -/
theorem cohomology_comparison (q : ℤ) :
    ∃ c : DerivedCategory.homologyFunctor.{wS} (SheafOfModules.{u + 1} (ring Λ S)) q ⋙
        pullback Λ V ≅
      (pullback Λ V).mapDerivedCategory.{wS, wV} ⋙
        DerivedCategory.homologyFunctor.{wV} (SheafOfModules.{u + 1} (ring Λ V.left)) q,
      ∀ K : CochainComplex (SheafOfModules.{u + 1} (ring Λ S)) ℤ,
        c.hom.app (DerivedCategory.Q.{wS}.obj K) ≫
          (DerivedCategory.homologyFunctor.{wV} _ q).map
            ((pullback Λ V).mapDerivedCategoryFactors.{wS, wV}.hom.app
              K) ≫
          (DerivedCategory.homologyFunctorFactors.{wV} _ q).hom.app
            (((pullback Λ V).mapHomologicalComplex
              (.up ℤ)).obj K) =
        (pullback Λ V).map
            ((DerivedCategory.homologyFunctorFactors.{wS} _ q).hom.app K) ≫
          ((K.sc q).mapHomologyIso (pullback Λ V)).inv := by
  sorry

end CondensedLocalization
end AlgebraicGeometry.ProEtale
