/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.RingIsoChainCoherence
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import Sheaf.CategoryTheory.Monoidal.MonoidalDescent

/-! # Normalized braided derived coefficient restriction

Source: Stacks Project, Tags 03D7, 06YS and 06YT.

(blueprint: lem-pur-u2-derived-restriction-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.cochainModulesMonoidal HomologicalComplex.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapCochainComplexMonoidal
namespace SheafOfModules.RingIsoTransport
attribute [local irreducible] derivedId derivedComp chainId chainComp cochainMonoidal
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)]
  [∀ R : Sheaf J CommRingCat.{r},
    MonoidalCategory (DerivedCategory (scalarModules J R))]
  [∀ R : Sheaf J CommRingCat.{r},
    SymmetricCategory (DerivedCategory (scalarModules J R))]
  {R S : Sheaf J CommRingCat.{r}}

/-- Monoidality of the identity derived comparison descends from the normalized
factorization and the identity comparison on complexes. The K-flat model criterion
reflects monoidality after localization.
Source: literature/stacks-project/sites-cohomology.tex; literature/stacks-project/categories.tex;
Tags 06YS, 06YT, 06YU, 04VG and 04VK; monoidal equations on K-flat representatives and
localization normalization.
(blueprint: lem-pur-u2-derived-restriction-monoidal). -/
theorem derivedId_monoidal (R : Sheaf J CommRingCat.{r})
    (o : RingIsoTensorTransport (Iso.refl R).symm)
    (q : (DerivedCategory.Q (C := scalarModules J R)).LaxBraided)
    (b : (scalarRestriction (Iso.refl R).inv).mapDerivedCategory.Braided)
    (hε : IsIso q.toLaxMonoidal.ε)
    (hμ : ∀ P Q : CochainComplex (scalarModules J R) ℤ,
      Q.IsKFlatIndependentCoefficients → IsIso (q.toLaxMonoidal.μ P Q))
    (hf : let : (scalarRestriction (Iso.refl R).inv).Monoidal := o.monoidal.toMonoidal
      let : (scalarRestriction (Iso.refl R).inv).IsEquivalence :=
        o.functor_eq ▸ o.equivalence.isEquivalence_functor
      let := q
      let := b
      let := cochainMonoidal (Iso.refl R) o
      NatTrans.IsMonoidal (scalarRestriction (Iso.refl R).inv).mapDerivedCategoryFactors.hom) :
    let := b
    NatTrans.IsMonoidal (derivedId R).hom := by
  let F := scalarRestriction (Iso.refl R).inv
  let Q : CochainComplex (scalarModules J R) ℤ ⥤ DerivedCategory (scalarModules J R) :=
    DerivedCategory.Q
  let : F.Monoidal := o.monoidal.toMonoidal
  let : (scalarRestriction (Iso.refl R).inv).IsEquivalence :=
    o.functor_eq ▸ o.equivalence.isEquivalence_functor
  let := cochainMonoidal (Iso.refl R) o
  let := q
  let := b
  have : IsIso (Functor.LaxMonoidal.ε Q) := hε
  let : NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom := hf
  let : NatTrans.IsMonoidal (chainId R).hom := chainId_monoidal R o
  have : NatTrans.IsMonoidal (Functor.whiskerLeft Q (derivedId R).hom) :=
    monoidal_identity_of_factors Q (F.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategory
      F.mapDerivedCategoryFactors (chainId R) (derivedId R) (derivedId_fac R)
  apply monoidal_of_tensor_models Q
    CochainComplex.IsKFlatIndependentCoefficients hμ
  intro X
  let K := Q.objPreimage X
  obtain ⟨P, f, hP, _, hf', _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  exact ⟨P, hP, ⟨Localization.isoOfHom Q
    (HomologicalComplex.quasiIso (scalarModules J R) (.up ℤ)) f hf' ≪≫
      Q.objObjPreimageIso X⟩⟩

/-- The derived compositor is monoidal, since its localization formula is a
composite of monoidal factorizations and the monoidal compositor on complexes.
The tensor-model criterion then reflects the assertion from K-flat models.
Source: literature/stacks-project/sites-cohomology.tex; literature/stacks-project/categories.tex;
Tags 06YS, 06YT, 06YU, 04VG and 04VK; monoidal equations on K-flat representatives and
localization normalization.
(blueprint: lem-pur-u2-derived-restriction-monoidal). -/
theorem derivedComp_monoidal {R S T : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T)
    (oa : RingIsoTensorTransport a.symm) (ob : RingIsoTensorTransport b.symm)
    (oc : RingIsoTensorTransport (a ≪≫ b).symm)
    (q : ∀ R : Sheaf J CommRingCat.{r},
      (DerivedCategory.Q (C := scalarModules J R)).LaxBraided)
    (ba : (scalarRestriction a.inv).mapDerivedCategory.Braided)
    (bb : (scalarRestriction b.inv).mapDerivedCategory.Braided)
    (bc : (scalarRestriction (a ≪≫ b).inv).mapDerivedCategory.Braided)
    (hε : ∀ R, IsIso (q R).toLaxMonoidal.ε)
    (hμ : ∀ R (P Q : CochainComplex (scalarModules J R) ℤ),
      Q.IsKFlatIndependentCoefficients → IsIso ((q R).toLaxMonoidal.μ P Q))
    (ha : let : (scalarRestriction a.inv).Monoidal := oa.monoidal.toMonoidal
      let : (scalarRestriction a.inv).IsEquivalence :=
        oa.functor_eq ▸ oa.equivalence.isEquivalence_functor
      let := q R
      let := q S
      let := ba
      let := cochainMonoidal a oa
      NatTrans.IsMonoidal (scalarRestriction a.inv).mapDerivedCategoryFactors.hom)
    (hb : let : (scalarRestriction b.inv).Monoidal := ob.monoidal.toMonoidal
      let : (scalarRestriction b.inv).IsEquivalence :=
        ob.functor_eq ▸ ob.equivalence.isEquivalence_functor
      let := q S
      let := q T
      let := bb
      let := cochainMonoidal b ob
      NatTrans.IsMonoidal (scalarRestriction b.inv).mapDerivedCategoryFactors.hom)
    (hc : let : (scalarRestriction (a ≪≫ b).inv).Monoidal := oc.monoidal.toMonoidal
      let : (scalarRestriction (a ≪≫ b).inv).IsEquivalence :=
        oc.functor_eq ▸ oc.equivalence.isEquivalence_functor
      let := q R
      let := q T
      let := bc
      let := cochainMonoidal (a ≪≫ b) oc
      NatTrans.IsMonoidal (scalarRestriction (a ≪≫ b).inv).mapDerivedCategoryFactors.hom) :
    let := ba
    let := bb
    let := bc
    NatTrans.IsMonoidal (derivedComp a b).hom := by
  let F := scalarRestriction a.inv
  let G := scalarRestriction b.inv
  let H := scalarRestriction (a ≪≫ b).inv
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let QR : CochainComplex (scalarModules J R) ℤ ⥤ DerivedCategory (scalarModules J R) :=
    DerivedCategory.Q
  let QS : CochainComplex (scalarModules J S) ℤ ⥤ DerivedCategory (scalarModules J S) :=
    DerivedCategory.Q
  let QT : CochainComplex (scalarModules J T) ℤ ⥤ DerivedCategory (scalarModules J T) :=
    DerivedCategory.Q
  let : F.Monoidal := oa.monoidal.toMonoidal
  let : G.Monoidal := ob.monoidal.toMonoidal
  let : H.Monoidal := oc.monoidal.toMonoidal
  let : (scalarRestriction a.inv).IsEquivalence :=
    oa.functor_eq ▸ oa.equivalence.isEquivalence_functor
  let : (scalarRestriction b.inv).IsEquivalence :=
    ob.functor_eq ▸ ob.equivalence.isEquivalence_functor
  let : (scalarRestriction (a ≪≫ b).inv).IsEquivalence :=
    oc.functor_eq ▸ oc.equivalence.isEquivalence_functor
  let := cochainMonoidal a oa
  let := cochainMonoidal b ob
  let := cochainMonoidal (a ≪≫ b) oc
  let := q R
  let := q S
  let := q T
  let := ba
  let := bb
  let := bc
  let : NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom := ha
  let : NatTrans.IsMonoidal G.mapDerivedCategoryFactors.hom := hb
  let : NatTrans.IsMonoidal H.mapDerivedCategoryFactors.hom := hc
  let : NatTrans.IsMonoidal (chainComp a b).hom := chainComp_monoidal a b oa ob oc
  have : NatTrans.IsMonoidal (Functor.whiskerLeft QR (derivedComp a b).hom) :=
    monoidal_compositor_of_factors QR QS QT Fc Gc Hc
      F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory
      F.mapDerivedCategoryFactors G.mapDerivedCategoryFactors H.mapDerivedCategoryFactors
      (chainComp a b) (derivedComp a b) (derivedComp_fac a b)
  have : IsIso (Functor.LaxMonoidal.ε QR) := hε R
  apply monoidal_of_tensor_models QR
    CochainComplex.IsKFlatIndependentCoefficients (hμ R)
  intro X
  let K := QR.objPreimage X
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  exact ⟨P, hP, ⟨Localization.isoOfHom QR
    (HomologicalComplex.quasiIso (scalarModules J R) (.up ℤ)) f hf ≪≫
      QR.objObjPreimageIso X⟩⟩

end SheafOfModules.RingIsoTransport
