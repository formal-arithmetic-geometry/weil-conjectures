/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Unbounded derived Zariski–étale quasi-coherent comparison

Source: Stacks Project, spaces-perfect.tex, Tags 071Q and 08GH; derived.tex, Tag 08BJ
(blueprint: lem-sfb-scheme-derived-etale-qcoh-comparison).

The equivalence witnesses are the already recorded canonical equivalence data. The
additional record states the global-sections comparison. Its
representative equations specify the canonical maps, rather than arbitrary isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option genInjectivity false

universe u w a

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable [∀ T : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
  [∀ T : Scheme.{u}, HasDerivedCategory.{w} (SmallEtaleModules T)]

/-- The canonical direct-image comparison, as the counit mate of the recorded derived
pullback square. This is the very arrow in `pushforward_comparison_iso` of that square.
Source: Stacks 08GH (blueprint: lem-sfb-scheme-derived-etale-qcoh-comparison). -/
def DerivedEtaleZariskiSquareData.directImageComparison
    {Z W : Scheme.{u}} {v : Z ⟶ W}
    {dZ : DerivedEtaleZariskiEquivalenceData Z}
    {dW : DerivedEtaleZariskiEquivalenceData W}
    (s : DerivedEtaleZariskiSquareData v dZ dW) :
    schemeDerivedDirectImage v ⋙ dW.extension ⟶ dZ.extension ⋙ s.pushforward :=
  Functor.whiskerLeft (schemeDerivedDirectImage v ⋙ dW.extension) s.adjunction.unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (schemeDerivedDirectImage v) s.comparison.inv) s.pushforward ≫
    Functor.whiskerRight
      (Functor.whiskerRight (canonicalSchemeDerivedAdjunction v).counit dZ.extension)
        s.pushforward

/-- Terminal sections of a small étale structure-module sheaf, with its actual coefficient
universe. Evaluation is the usual Hom from the structure module, without a universe lift.
Source: Stacks, Cohomology on Sites, 07A5
(blueprint: lem-sfb-scheme-derived-etale-qcoh-comparison). -/
def smallEtaleModuleTerminalSections (T : Scheme.{u}) :
    SmallEtaleModules T ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (smallEtaleModuleRing T) ⋙
    sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation T.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op (Etale.mk (𝟙 T)))

/-- Derived terminal sections on both sites, including their universal properties,
K-injective computation, and the canonical comparison. The ordinary comparison is fixed
by the actual identification of the final open subscheme with T. The last equation says
that the derived comparison is the same map on every representative.
Source: Stacks 071Q and derived.tex 08BJ
(blueprint: lem-sfb-scheme-derived-etale-qcoh-comparison). -/
structure SchemeEtaleZariskiDerivedSectionsData (T : Scheme.{u})
    (d : DerivedEtaleZariskiEquivalenceData T)
    [HasDerivedCategory.{a} AddCommGrpCat.{u}] where
  [etale_additive : (smallEtaleModuleTerminalSections T).Additive]
  [restriction_additive : d.context.restriction.Additive]
  [zariski_additive : (RingedSpace.globalSectionsFunctor T.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).Additive]
  zariski : schemeDerivedCategory T ⥤ DerivedCategory AddCommGrpCat.{u}
  etale : DerivedCategory (SmallEtaleModules T) ⥤ DerivedCategory AddCommGrpCat.{u}
  zariski_unit : (RingedSpace.globalSectionsFunctor T.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh.{a} ⟶ DerivedCategory.Qh.{w} ⋙ zariski
  zariski_derived : zariski.IsRightDerivedFunctor zariski_unit
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ))
  zariski_injective :
    ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings T.toRingedSpace)) ℤ, I.IsKInjective →
    IsIso (zariski_unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
  etale_unit : (smallEtaleModuleTerminalSections T).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh.{a} ⟶ DerivedCategory.Qh.{w} ⋙ etale
  etale_derived : etale.IsRightDerivedFunctor etale_unit
    (HomotopyCategory.quasiIso (SmallEtaleModules T) (.up ℤ))
  etale_injective : ∀ I : CochainComplex (SmallEtaleModules T) ℤ, I.IsKInjective →
    IsIso (etale_unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
  ordinary : d.context.restriction ⋙ RingedSpace.globalSectionsFunctor T.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u} ≅
    smallEtaleModuleTerminalSections T
  ordinary_sections : ∀ (G : SmallEtaleModules T),
    ordinary.hom.app G =
      G.val.presheaf.map (MorphismProperty.Over.homMk T.topIso.inv (Scheme.toIso_inv_ι T)).op
  comparison : d.restriction ⋙ zariski ≅ etale
  comparison_representatives : ∀ I : HomotopyCategory (SmallEtaleModules T) (.up ℤ),
    zariski_unit.app ((d.context.restriction.mapHomotopyCategory (.up ℤ)).obj I) ≫
      zariski.map (d.restriction_unit.app I) ≫
      comparison.hom.app (DerivedCategory.Qh.obj I) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ordinary.hom (.up ℤ)).app I) ≫
      etale_unit.app I

/-- Every scheme has the unbounded quasi-coherent comparison, preserving the structure
module, with canonical qcqs direct-image and derived-global-sections comparisons.
Quasi-coherence concerns all cohomology sheaves, with no restriction on complex terms.

Source: Stacks Project, spaces-perfect.tex, Tags 071Q and 08GH; derived.tex, Tag 08BJ
(blueprint: lem-sfb-scheme-derived-etale-qcoh-comparison).

Proof:
1. Apply lem-sfb-derived-etale-zariski-equivalence to every scheme. Its exact module
   pullback induces the unbounded equivalence on the full cohomological QCoh
   subcategories. Its inverse is R epsilon_*, and its actual adjunction unit and
   counit are the equivalence maps. The structure-module map is multiplication
   b tensor a mapped to ba, with inverse b mapped to b tensor 1.
2. For a qcqs morphism v use the direct-image clause of that same node. The ordinary
   right square is restriction along gabberPreimageEtaleIso. Derive this square and
   insert the equivalence unit and counit to obtain comparison. Both right derived
   functors preserve quasi-coherence; the canonical comparison is invertible on
   every quasi-coherent unbounded object. No separatedness or boundedness is used.
3. Choose a K-injective representative E to I by prop-pur-kinjective-resolutions-exist.
   Restriction epsilon_* I remains K-injective: maps from acyclic A correspond,
   including homotopies, to maps from the acyclic epsilon^* A to I, hence are null
   homotopic (def-pur-kinjective-complex and exactness from step 1). The section
   complexes on the two sites are canonically identical, using the final-object
   identification. This identity commutes with maps of representatives. It gives
   the normalized natural comparison R Gamma_Zar R epsilon_* ≅ R Gamma_et.
   Compose with the equivalence unit to identify R Gamma_Zar F with
   R Gamma_et epsilon^* F for every unbounded quasi-coherent F. Taking zeroth
   homology recovers def-pur-ringed-site-zeroth-hypercohomology. -/
theorem scheme_derived_etale_qcoh_comparison [HasDerivedCategory.{a} AddCommGrpCat.{u}] :
    ∃ d : ∀ T : Scheme.{u}, DerivedEtaleZariskiEquivalenceData T,
      (∀ (Z W : Scheme.{u}) (v : Z ⟶ W), QuasiCompact v → QuasiSeparated v →
        ∃ s : DerivedEtaleZariskiSquareData v (d Z) (d W),
          ∀ K : schemeDerivedCategory Z, schemeDerivedQCohProperty Z K →
            IsIso (s.directImageComparison.app K)) ∧
      ∀ T : Scheme.{u}, Nonempty (SchemeEtaleZariskiDerivedSectionsData T (d T)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
