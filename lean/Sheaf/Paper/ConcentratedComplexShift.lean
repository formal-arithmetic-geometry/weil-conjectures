/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Complexes with cohomology in a single degree

Source: the blueprint of the Weil conjectures, chapter `sec-smooth-purity`, unit
`sk-thm-dnc`, node `lem-pur-concentrated-complex-shift`
(blueprint: lem-pur-concentrated-complex-shift).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The canonical uncompleted derived pullback for the constant coefficient ring.
It is the derived functor of the specified pro-etale inverse-image module construction,
using the canonical coefficient comparison. Its invertibility is the existing
`finiteCoefficientCommRingMap_isIso`; no coefficient map or equivalence is chosen.
Source: Stacks Project, Tags 0H7J and 09A5; blueprint `sk-thm-dnc`,
node `lem-pur-concentrated-complex-shift`
(blueprint: lem-pur-concentrated-complex-shift). -/
noncomputable def proEtaleConstantDerivedPullback (P : WeilConjectures.PurityFiniteSetting.{u})
    {U T : Scheme.{u}} (u : U ⟶ T) :
    proEtaleDerivedCategory T P.Ring ⥤ proEtaleDerivedCategory U P.Ring :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : TopologicalSpace (ULift.{u + 1, u} P.Ring) := ⊥
  letI := discreteTopology_bot (ULift.{u + 1, u} P.Ring)
  letI := AlgebraicGeometry.ProEtale.finiteCoefficientCommRingMap_isIso u
    (ULift.{u + 1, u} P.Ring)
  proEtaleRingDerivedPullback u (proEtaleConstantRing T P.Ring)
    (proEtaleConstantRing U P.Ring) (asIso (proEtaleCoefficientInverseImageMap u P.Ring))

/-- The two independent assertions of the single-degree concentration lemma.
The first isomorphism is normalized to the identity on degree-`r` cohomology, using
`singleFunctors.shiftIso` and `singleFunctorCompHomologyFunctorIso`. This determines it
uniquely and records the canonical truncation isomorphism, rather than mere existence.

Source: blueprint `sec-smooth-purity/sk-thm-dnc/lem-pur-concentrated-complex-shift.md`,
Proof Steps 1-2 (blueprint: lem-pur-concentrated-complex-shift).

Proof: (1) Choose a cochain representative. The canonical inclusion from its truncation
at `r` induces cohomology isomorphisms at and below `r`, and both complexes have zero
cohomology above `r` (lem-weil-pbc-truncation-cohomology). The truncation triangle's
cycles-to-cohomology quotient is also a cohomology isomorphism: at `r` it is the canonical
quotient and away from `r` both sides vanish (lem-weil-pbc-truncation-triangle).
(2) Both maps are isomorphisms by lem-weil-pbc-unbounded-derived-iso-cohomology.
Compose the inverse of the inclusion with the quotient. Its map on `H^r` is the identity;
full faithfulness of the single-degree embedding makes this normalization unique.
(3) For the independent descent assertion, the finite coefficient ring is finite by
def-weil-l-adic-coefficient-extension. A surjective etale map is a pro-etale singleton
cover (lem-pur-etale-proetale-cover). Exact inverse image commutes with kernels, images
and their quotients, so computes derived pullback and commutes with cohomology
(prop-weil-pbc-proetale-constant-exact). The shifted sheaf has no other cohomology;
covering-family conservativity gives vanishing downstairs (lem-cbc-proetale-stalk-conservative).
(4) The localization equivalence of lem-weil-proetale-weakly-etale-localization identifies
inverse image with localized restriction: the inverse-image indexing category for an
object over U has its graph as initial object, so its opposite colimit evaluates at
that object. The identification preserves constant scalars and module actions.
(5) Choose a pro-etale trivializing cover of L. Localization identifies its constant
models with those over T, and composition with U to T is again a cover. Iterated
restriction therefore trivializes H^r(K) (def-weil-proetale-locally-constant-sheaf).
(6) Lift a geometric point of T to U (lem-weil-pbc-etale-cover-geometric-point-lift).
The stalk restriction comparison is surjective by pulling a neighbourhood back to U.
It is injective by a common pointed refinement followed by equalization of its two
maps to U (def-weil-proetale-geometric-stalk and the localization lemma). It is linear,
so the stalk of H^r(K) is isomorphic to the finite stalk of L. No uniform bound is used. -/
theorem concentratedComplexShift (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (K : proEtaleDerivedCategory T P.Ring)
    (hK : WeilConjectures.finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos T K)
    (r : ℤ) :
    ((∀ i : ℤ, i ≠ r →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) i).obj K)) →
      ∃! e : K ≅
      ((DerivedCategory.singleFunctor
        (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) 0).obj
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K))⟦-r⟧,
        (DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).map
          (e.hom ≫
            (((DerivedCategory.singleFunctors
              (proEtaleRingModules T (proEtaleConstantRing T P.Ring))).shiftIso
                (-r) r 0 (neg_add_cancel r)).hom.app
              ((DerivedCategory.homologyFunctor
                (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K))) =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).inv.app
              ((DerivedCategory.homologyFunctor
                (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K)) ∧
    ∀ (U : Scheme.{u}) (u : U ⟶ T) [Surjective u] [Etale u],
      ∀ (L : proEtaleRingModules U (proEtaleConstantRing U P.Ring)),
        Nonempty ((proEtaleConstantDerivedPullback P u).obj K ≅
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules U (proEtaleConstantRing U P.Ring)) 0).obj L)⟦-r⟧) →
        IsLocallyConstantProEtaleModuleSheaf U P.Ring L ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ U),
          Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing U P.Ring) L)) →
        (∀ i : ℤ, i ≠ r →
          IsZero ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) i).obj K)) ∧
        IsLocallyConstantProEtaleModuleSheaf T P.Ring
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ T),
          Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring)
            ((DerivedCategory.homologyFunctor
              (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
