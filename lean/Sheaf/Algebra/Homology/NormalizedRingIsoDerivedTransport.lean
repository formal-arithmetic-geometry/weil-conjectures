/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Homology.RingIsoNativeTensor
import Sheaf.Algebra.Homology.RingIsoBraidedDerived
import Sheaf.Algebra.Homology.RingIsoTransportComparisons
import Sheaf.Algebra.Homology.RingIsoDerivedCocycle
import Sheaf.Algebra.Homology.RingIsoDerivedMonoidal

/-! # Normalized derived transport along ring-sheaf isomorphisms

Source: Stacks Project, sites-modules.tex, Tag 03D7; derived.tex, Tag 015F;
main-20261015 blueprint, def-pur-section-invariant, finite-clopen coefficient transport
(blueprint: lem-pur-ring-iso-derived-transport).

The functor is Mathlib's exact termwise derived functor of restriction along the inverse
ring isomorphism. Its localization comparison is the existing canonical factorization.
The data below specify identity, composition and tensor coherence for these functors.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)]

variable [∀ R : Sheaf J CommRingCat.{r},
    MonoidalCategory (DerivedCategory (scalarModules J R))]
  [∀ R : Sheaf J CommRingCat.{r},
    SymmetricCategory (DerivedCategory (scalarModules J R))]

/-- Comparison data for normalized transport, using existing scalar restriction and
its canonical exact termwise derived functor. All comparison maps are normalized by
the predicates below, rather than chosen as arbitrary equivalences.
Source: Stacks 03D7, 015F, 06YU and 0FPT; blueprint def-pur-section-invariant,
finite-clopen coefficient transport (blueprint: lem-pur-ring-iso-derived-transport). -/
structure NormalizedRingIsoDerivedData where
  /-- The existing ordinary normalized tensor transport. -/
  ordinary : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S),
    RingIsoTensorTransport a.symm
  /-- The exact termwise derived functor is an equivalence. -/
  equivalence : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S),
    (scalarRestriction a.inv).mapDerivedCategory.IsEquivalence
  /-- Lax braided localization presents the derived tensor. -/
  localization : ∀ R : Sheaf J CommRingCat.{r},
    (DerivedCategory.Q (C := scalarModules J R)).LaxBraided
  /-- The tensor bifunctor is the published K-flat tensor, on objects and maps. -/
  tensor_eq : ∀ R : Sheaf J CommRingCat.{r},
    Functor.uncurry.obj (curriedTensor (DerivedCategory (scalarModules J R))) =
      siteDerivedTensorIndependentCoefficients J R
  /-- Strong braided derived transport. -/
  braided : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S),
    (scalarRestriction a.inv).mapDerivedCategory.Braided
  /-- Identity comparison on complexes. -/
  identityChain : ∀ R : Sheaf J CommRingCat.{r},
    (scalarRestriction (Iso.refl R).inv).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (scalarModules J R) ℤ)
  /-- Composition comparison on complexes. -/
  compositionChain : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ≅ S) (b : S ≅ T),
    (scalarRestriction a.inv).mapHomologicalComplex (.up ℤ) ⋙
      (scalarRestriction b.inv).mapHomologicalComplex (.up ℤ) ≅
        (scalarRestriction (a ≪≫ b).inv).mapHomologicalComplex (.up ℤ)
  /-- Identity comparison on derived categories. -/
  identity : ∀ R : Sheaf J CommRingCat.{r},
    (scalarRestriction (Iso.refl R).inv).mapDerivedCategory ≅
      𝟭 (DerivedCategory (scalarModules J R))
  /-- Composition comparison on derived categories. -/
  composition : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ≅ S) (b : S ≅ T),
    (scalarRestriction a.inv).mapDerivedCategory ⋙
      (scalarRestriction b.inv).mapDerivedCategory ≅
        (scalarRestriction (a ≪≫ b).inv).mapDerivedCategory

/-- Localization identifies the coefficient unit and all K-flat tensor models.
Source: Stacks 03D7, 015F, 04VG, 06YU and 0FPT
(blueprint: lem-pur-ring-iso-derived-transport). -/
def NormalizedRingIsoLocalizationTensorSpec (d : NormalizedRingIsoDerivedData (J := J)) : Prop :=
  (∀ R : Sheaf J CommRingCat.{r},
    IsIso (d.localization R).toLaxMonoidal.ε) ∧
  (∀ (R : Sheaf J CommRingCat.{r})
  (P Q : CochainComplex (scalarModules J R) ℤ),
    P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
      IsIso ((d.localization R).toLaxMonoidal.μ P Q))

/-- Identity and composition comparisons fix every local section in every degree.
Source: Stacks 03D7, 015F, 04VG, 06YU and 0FPT
(blueprint: lem-pur-ring-iso-derived-transport). -/
def NormalizedRingIsoChainSpec (d : NormalizedRingIsoDerivedData (J := J)) : Prop :=
  (∀ (R : Sheaf J CommRingCat.{r})
  (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (U : Cᵒᵖ)
  (x : (P.X n).val.obj U),
  (((d.identityChain R).hom.app P).f n).val.app U x = x) ∧
  (∀ {R S T : Sheaf J CommRingCat.{r}}
  (a : R ≅ S) (b : S ≅ T) (P : CochainComplex (scalarModules J R) ℤ)
  (n : ℤ) (U : Cᵒᵖ) (x : (P.X n).val.obj U),
  (((d.compositionChain a b).hom.app P).f n).val.app U x = x)

/-- Derived comparisons are descents of the specified identity maps on complexes.
Source: Stacks 03D7, 015F, 04VG, 06YU and 0FPT
(blueprint: lem-pur-ring-iso-derived-transport). -/
def NormalizedRingIsoLocalizationSpec (d : NormalizedRingIsoDerivedData (J := J)) : Prop :=
  (∀ (R : Sheaf J CommRingCat.{r})
  (P : CochainComplex (scalarModules J R) ℤ),
  (d.identity R).hom.app (DerivedCategory.Q.obj P) =
      (scalarRestriction (Iso.refl R).inv).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((d.identityChain R).hom.app P)) ∧
  (∀ {R S T : Sheaf J CommRingCat.{r}}
  (a : R ≅ S) (b : S ≅ T) (P : CochainComplex (scalarModules J R) ℤ),
  (d.composition a b).hom.app (DerivedCategory.Q.obj P) ≫
        (scalarRestriction (a ≪≫ b).inv).mapDerivedCategoryFactors.hom.app P =
      (scalarRestriction b.inv).mapDerivedCategory.map
          ((scalarRestriction a.inv).mapDerivedCategoryFactors.hom.app P) ≫
        (scalarRestriction b.inv).mapDerivedCategoryFactors.hom.app
          (((scalarRestriction a.inv).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((d.compositionChain a b).hom.app P))

/-- Both identity laws and the three-isomorphism cocycle, including ring-map reassociation.
Source: Stacks 03D7, 015F, 04VG, 06YU and 0FPT
(blueprint: lem-pur-ring-iso-derived-transport). -/
def NormalizedRingIsoCocycleSpec (d : NormalizedRingIsoDerivedData (J := J)) : Prop :=
  (∀ {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S)
  (X : DerivedCategory (scalarModules J R)),
  (d.composition (Iso.refl R) a).hom.app X ≫
        (eqToIso (congrArg (fun c : R ≅ S ↦
          (scalarRestriction c.inv).mapDerivedCategory) (Iso.refl_trans a))).hom.app X =
      (scalarRestriction a.inv).mapDerivedCategory.map ((d.identity R).hom.app X)) ∧
  (∀ {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S)
  (X : DerivedCategory (scalarModules J R)),
  (d.composition a (Iso.refl S)).hom.app X ≫
        (eqToIso (congrArg (fun c : R ≅ S ↦
          (scalarRestriction c.inv).mapDerivedCategory) (Iso.trans_refl a))).hom.app X =
      (d.identity S).hom.app ((scalarRestriction a.inv).mapDerivedCategory.obj X)) ∧
  (∀ {R S T V : Sheaf J CommRingCat.{r}}
  (a : R ≅ S) (b : S ≅ T) (c : T ≅ V) (X : DerivedCategory (scalarModules J R)),
  (scalarRestriction c.inv).mapDerivedCategory.map ((d.composition a b).hom.app X) ≫
        (d.composition (a ≪≫ b) c).hom.app X ≫
        (eqToIso (congrArg (fun d : R ≅ V ↦
          (scalarRestriction d.inv).mapDerivedCategory) (Iso.trans_assoc a b c))).hom.app X =
      (d.composition b c).hom.app ((scalarRestriction a.inv).mapDerivedCategory.obj X) ≫
        (d.composition a (b ≪≫ c)).hom.app X)

/-- Identity and composition comparisons respect tensor products and units.
Source: Stacks 03D7, 015F, 04VG, 06YU and 0FPT
(blueprint: lem-pur-ring-iso-derived-transport). -/
def NormalizedRingIsoMonoidalSpec (d : NormalizedRingIsoDerivedData (J := J)) : Prop :=
  (∀ R : Sheaf J CommRingCat.{r},
    letI := d.braided (Iso.refl R)
    NatTrans.IsMonoidal (d.identity R).hom) ∧
  (∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ≅ S) (b : S ≅ T),
    letI := d.braided a
    letI := d.braided b
    letI := d.braided (a ≪≫ b)
    NatTrans.IsMonoidal (d.composition a b).hom)

/-- The canonical localization comparison respects the actual ordinary tensor and unit maps.
Source: Stacks 03D7, 015F, 04VG, 06YU and 0FPT
(blueprint: lem-pur-ring-iso-derived-transport). -/
def NormalizedRingIsoNormalizationSpec (d : NormalizedRingIsoDerivedData (J := J)) : Prop :=
  (∀ {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S),
    letI : (scalarRestriction a.inv).Monoidal := (d.ordinary a).monoidal.toMonoidal
    letI : (scalarRestriction a.inv).IsEquivalence :=
      (d.ordinary a).functor_eq ▸ (d.ordinary a).equivalence.isEquivalence_functor
    letI := d.localization R
    letI := d.localization S
    letI := d.braided a
    letI := Functor.mapCochainComplexMonoidal (scalarRestriction a.inv)
    NatTrans.IsMonoidal (scalarRestriction a.inv).mapDerivedCategoryFactors.hom)

/-- Normalized coefficient transport, including its identity, cocycle and tensor laws.
Source: Stacks 03D7, 015F, 04VG, 06YU and 0FPT; blueprint def-pur-section-invariant,
finite-clopen coefficient identifications (blueprint: lem-pur-ring-iso-derived-transport).

Proof:
1. Apply lem-sfb-ring-isomorphism-tensor-transport to alpha inverse. Its restriction
   is T_alpha, its inverse is restriction along alpha, its unit map is alpha and its
   two tensor maps fix pure tensors. It preserves flat modules and K-flat complexes.
2. Use lem-weil-pbc-exact-functor-derived-factorization: the exact termwise functor
   gives mapDerivedCategory with its canonical mapDerivedCategoryFactors. Naturality
   identifies localized chain maps, and inverting its equation for a denominator
   identifies roofs. Its existing shift comparison makes it triangulated.
3. Localize the ordinary inverse equivalence. The identity comparisons before
   localization descend by lem-weil-pbc-localization-universal-property. Faithfulness
   after precomposition proves both triangle identities, giving the derived equivalence.
4. The two successive actions agree with the composite inverse ring map, so identity
   on abelian complexes gives compositionChain. Descend it with the two canonical
   factorization isomorphisms. On three factors they cancel, leaving the same identity
   chain map; localization faithfulness proves the cocycle and both identity equations.
5. Use lem-weil-pbc-site-derived-tensor-descent to extend the total-tensor comparison
   on flat-term K-flat pairs. Transport the monoidal structure onto its published
   bifunctor, obtaining tensor_eq. Its normalization is the ordinary pure-tensor comparison
   summed over bidegrees. The associators, unitors and signed symmetry of
   lem-sf-ringed-derived-closed-symmetric-monoidal are identified on these models.
6. For two transports both compositor tensor pastings fix each pure tensor; on the
   unit both maps are beta(alpha(r)). These equalities descend from K-flat pairs by
   full faithfulness of restriction. The one-variable unit assertion descends by the
   localization universal property. This proves monoidality of the comparisons and
   their normalization, with arbitrary unbounded complexes throughout. -/
theorem normalized_ringIso_derived_transport
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] :
    ∃ m : ∀ R : Sheaf J CommRingCat.{r},
      MonoidalCategory (DerivedCategory (scalarModules J R)),
    ∃ b : ∀ R : Sheaf J CommRingCat.{r},
      @SymmetricCategory (DerivedCategory (scalarModules J R)) _ (m R),
    ∃ d : @NormalizedRingIsoDerivedData.{u, v, r, w} C _ _ J _ _ _ _ m b,
      NormalizedRingIsoLocalizationTensorSpec d ∧ NormalizedRingIsoChainSpec d ∧
      NormalizedRingIsoLocalizationSpec d ∧ NormalizedRingIsoCocycleSpec d ∧
      NormalizedRingIsoMonoidalSpec d ∧ NormalizedRingIsoNormalizationSpec d := by
  classical
  choose m b q hε hμ ht using fun R : Sheaf J CommRingCat.{r} ↦
    ringIso_published_tensor J R
  let := m
  let := b
  let o {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S) : RingIsoTensorTransport a.symm :=
    (ringIso_tensor_transport a.symm).some
  have hb {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S) :=
    ringIso_normalized_derived_braided a (o a) (q R) (q S) (hε R) (hε S) (hμ R) (hμ S)
  choose db hdb using @hb
  let d : NormalizedRingIsoDerivedData (J := J) :=
    { ordinary := o
      equivalence := fun a ↦ by
        let : (scalarRestriction a.inv).IsEquivalence :=
          (o a).functor_eq ▸ (o a).equivalence.isEquivalence_functor
        infer_instance
      localization := q
      tensor_eq := ht
      braided := db
      identityChain := RingIsoTransport.chainId
      compositionChain := RingIsoTransport.chainComp
      identity := RingIsoTransport.derivedId
      composition := RingIsoTransport.derivedComp }
  refine ⟨m, b, d, ⟨hε, fun R P Q _ hQ ↦ hμ R P Q hQ⟩,
    ⟨RingIsoTransport.chainId_sections, RingIsoTransport.chainComp_sections⟩,
    ⟨RingIsoTransport.derivedId_fac, RingIsoTransport.derivedComp_fac⟩, ?_, ?_, ?_⟩
  · exact ⟨RingIsoTransport.derived_left_unit, RingIsoTransport.derived_right_unit,
      RingIsoTransport.derived_assoc⟩
  · constructor
    · intro R
      exact RingIsoTransport.derivedId_monoidal R (o (Iso.refl R)) (q R)
        (db (Iso.refl R)) (hε R) (hμ R) (hdb (Iso.refl R))
    · intro R S T a b
      exact RingIsoTransport.derivedComp_monoidal a b (o a) (o b) (o (a ≪≫ b))
        q (db a) (db b) (db (a ≪≫ b)) hε hμ (hdb a) (hdb b) (hdb (a ≪≫ b))
  · exact hdb

end SheafOfModules
