/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Paper.ExternalRHomConePairing
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Scheme

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.EtaleKFlatCriteria
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined
import WeilConjectures.Algebra.Homology.HomComplexGlobalCochains
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.ConstantModuleKFlat
import Sheaf.CategoryTheory.ConstantModuleFlat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.Paper.KFlatMapFactorization
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.KFlatRingedToposPullback

/-! # Flat K-flat lifts of global Hom evaluations

Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 08J9, 0G7D and 0G7E
(blueprint: lem-pur-global-hom-evaluation-flat-lift).

The existing ordinary-etale cochains, pure-tensor evaluation identity and normalized
Hom comparison are reused from `ExternalRHom`. The two predicates below only bundle
K-flatness with termwise flatness in the recorded scalar realization.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.ExternalRHom

variable (A : Type (u + 1)) [CommRing A]

/-- K-flatness and flat terms, tested in the canonical ringed-site realization of an
ordinary constant-coefficient module complex. This bundles the two recorded predicates.
Source: Stacks 06YN and 03ER (blueprint: lem-pur-global-hom-evaluation-flat-lift). -/
def IsFlatKFlatEtaleComplex (X : Scheme.{u}) (P : Complexes A X) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
    ((ringedComplex A X).obj P) ∧
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
    ((ringedRealization A X).obj (P.X n))

/-- K-flatness and flat terms for an ordinary coefficient complex, using its existing
realization on the one-object site, where module sheaves are ordinary modules.
Source: Stacks 06YN and 06YS (blueprint: lem-pur-global-hom-evaluation-flat-lift). -/
def IsFlatKFlatCoefficientComplex (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
    (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
    ((pointComplex A).obj U) ∧
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
    (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
    ((pointRealization A).obj (U.X n))

/-- The derived transpose of the localized chain evaluation is the localized resolution
map followed by the canonical Hom-model comparison. Since alpha is a quasi-isomorphism,
this says precisely that the chain map is the derived global evaluation after the
specified source and target identifications. Any representative isomorphism to K
transports this same equality to K.
Source: Stacks 07A6, 08J9 and 08JA
(blueprint: lem-pur-global-hom-evaluation-flat-lift). -/
@[no_expose] def IsResolvedGlobalEvaluation {X : Scheme.{u}} (E I : Complexes A X)
    (m : HomModel A E I) (U : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (alpha : U ⟶ homComplex A E I) (t : chainEvaluationSource A X U E ⟶ I) : Prop :=
  chainModelTransposeOf (siteQ A X) (constant A X) (globalHom A X)
    (transpose A (X := X)) ((moduleQ A).obj U) E I ((constantComplex A X).obj U)
    (constantModel A X U) t = (moduleQ A).map alpha ≫ m.iso.hom

/-- Resolved global Hom evaluations have flat K-flat sources and flat K-flat target lifts,
with their canonical derived evaluation and arbitrary inverse-image identifications.

Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 08J9, 0G7D and 0G7E
(blueprint: lem-pur-global-hom-evaluation-flat-lift).

Proof:
1. Choose a K-injective representative of K by `prop-pur-kinjective-resolutions-exist`.
   Bounded flat E is K-flat by `lem-kun-kflat-criteria`.
2. Its internal Hom into I is K-injective by `lem-pur-hom-kflat-into-kinjective`.
   Derived sections are therefore computed by ordinary sections. The differential-compatible
   A-linear identification `lem-pur-hom-complex-global-cochains` identifies these with the
   displayed global Hom complex, canonically in D(A), using
   `lem-kun-rgamma-unbounded-well-defined`.
3. Apply `lem-pc-kflat-resolution` on the one-object site to get U and alpha.
   Constants preserve flatness and K-flatness by `lem-sfb-constant-module-flat` and
   `lem-sfb-constant-module-kflat`.
4. The ordinary constant/sections adjunction sends alpha to a chain map into internal Hom,
   by `lem-weil-pbc-termwise-adjunction-homotopy` and the preceding cochain identification.
5. Evaluate it on tensor summands. The Hom differential gives
   d(alpha(w)(e)) = alpha(dw)(e) + (-1)^degree(w) alpha(w)(de),
   so the unsigned formula is a chain map also in negative degrees.
6. `lem-pur-kflat-total-tensor-model` gives K-flatness, flat terms and the canonical
   derived-tensor identification of its source.
7. `lem-sfb-resolving-derived-adjunction-normalization` identifies the localized ordinary
   transpose with the derived constant/sections counit.
8. `lem-sfb-hom-kflat-chain-transpose` then identifies the localized evaluation with
   the derived tensor/Hom evaluation, for every representative and every alpha.
9. Apply `lem-pur-kflat-map-factorization` to t. Its flat-source clause gives N with
   flat terms. Localization through the homotopy category turns the homotopy into
   the asserted equality of localized chain maps.
10. The exact module inverse image of `prop-weil-pbc-inverse-image-modules-exact`,
    with the ring identification from `lem-weil-pbc-etale-inverse-image-algebraic-structures`,
    satisfies `lem-weil-pbc-ringed-topos-kflat-pullback`. Apply it to all four complexes.
    Exactness preserves quasi-isomorphisms, so the ordinary pullbacks compute derived
    pullbacks through the canonical left-derived counit, for every scheme morphism. -/
theorem globalHom_evaluation_flat_lift
    (X : Scheme.{u}) (E : Complexes A X) (K : DerivedCategoryModule A X)
    (hE : IsBoundedFlat A E) (hK : IsPlus A K) :
    (∃ I : Complexes A X, I.IsKInjective ∧ Nonempty ((siteQ A X).obj I ≅ K)) ∧
    ∀ (I : Complexes A X) [I.IsKInjective] (_i : (siteQ A X).obj I ≅ K),
      ∃ m : HomModel A E I,
        (∃ (U : CochainComplex (ModuleCat.{u + 1} A) ℤ)
          (alpha : U ⟶ homComplex A E I),
          QuasiIso alpha ∧ IsFlatKFlatCoefficientComplex A U) ∧
        ∀ (U : CochainComplex (ModuleCat.{u + 1} A) ℤ)
          (alpha : U ⟶ homComplex A E I),
          QuasiIso alpha → IsFlatKFlatCoefficientComplex A U →
          (∃ t : chainEvaluationSource A X U E ⟶ I, IsChainEvaluation A E I U alpha t) ∧
          ∀ (t : chainEvaluationSource A X U E ⟶ I), IsChainEvaluation A E I U alpha t →
            IsFlatKFlatEtaleComplex A X ((constantComplex A X).obj U) ∧
            IsFlatKFlatEtaleComplex A X E ∧
            IsFlatKFlatEtaleComplex A X (chainEvaluationSource A X U E) ∧
            IsResolvedGlobalEvaluation A E I m U alpha t ∧
            ∃ (N : Complexes A X) (v : chainEvaluationSource A X U E ⟶ N) (c : N ⟶ I),
              IsFlatKFlatEtaleComplex A X N ∧ QuasiIso c ∧
              Nonempty (Homotopy (v ≫ c) t) ∧
              (siteQ A X).map v ≫ (siteQ A X).map c = (siteQ A X).map t ∧
              ∀ (Z : Scheme.{u}) (f : Z ⟶ X) (P : Complexes A X),
                P ∈ [((constantComplex A X).obj U), E, chainEvaluationSource A X U E, N] →
                IsFlatKFlatEtaleComplex A Z ((pullComplex A f).obj P) ∧
                  IsIso (pullModel A f P) := by
  sorry

end AlgebraicGeometry.Etale.ExternalRHom
