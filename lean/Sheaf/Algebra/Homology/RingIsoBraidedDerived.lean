/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import Sheaf.CategoryTheory.Monoidal.NormalizedBraidedLocalization

/-! # Normalized braided derived coefficient restriction

Source: Stacks Project, Tags 03D7, 06YS and 06YT.

(blueprint: lem-pur-u2-normalized-braided-derived).
-/

@[expose] public noncomputable section
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
  [∀ R : Sheaf J CommRingCat.{r},
    MonoidalCategory (DerivedCategory (scalarModules J R))]
  [∀ R : Sheaf J CommRingCat.{r},
    SymmetricCategory (DerivedCategory (scalarModules J R))]
  {R S : Sheaf J CommRingCat.{r}}

/-- The canonical derived restriction comparison is monoidal, for any simultaneous
normalized tensor localizations. K-flat resolutions provide models, restriction
preserves K-flatness, and the braided localization square constructs the required
strong structure together with monoidality of its factorization.
Source: literature/stacks-project/sites-cohomology.tex; Tags 03D7, 06YS and 06YT; exact
restriction, K-flat models and normalized tensor descent.
(blueprint: lem-pur-u2-normalized-braided-derived). -/
theorem ringIso_normalized_derived_braided (a : R ≅ S)
    (o : RingIsoTensorTransport a.symm)
    (qR : (DerivedCategory.Q (C := scalarModules J R)).LaxBraided)
    (qS : (DerivedCategory.Q (C := scalarModules J S)).LaxBraided)
    (hεR : IsIso qR.toLaxMonoidal.ε) (hεS : IsIso qS.toLaxMonoidal.ε)
    (hμR : ∀ P Q : CochainComplex (scalarModules J R) ℤ,
      Q.IsKFlatIndependentCoefficients → IsIso (qR.toLaxMonoidal.μ P Q))
    (hμS : ∀ P Q : CochainComplex (scalarModules J S) ℤ,
      Q.IsKFlatIndependentCoefficients → IsIso (qS.toLaxMonoidal.μ P Q)) :
    ∃ b : (scalarRestriction a.inv).mapDerivedCategory.Braided,
      letI : (scalarRestriction a.inv).Monoidal := o.monoidal.toMonoidal
      letI : (scalarRestriction a.inv).IsEquivalence :=
        o.functor_eq ▸ o.equivalence.isEquivalence_functor
      letI := qR
      letI := qS
      letI := b
      letI := Functor.mapCochainComplexMonoidal (scalarRestriction a.inv)
      NatTrans.IsMonoidal (scalarRestriction a.inv).mapDerivedCategoryFactors.hom := by
  let F := scalarRestriction a.inv
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let G := F.mapDerivedCategory
  let QR : CochainComplex (scalarModules J R) ℤ ⥤ DerivedCategory (scalarModules J R) :=
    DerivedCategory.Q
  let QS : CochainComplex (scalarModules J S) ℤ ⥤ DerivedCategory (scalarModules J S) :=
    DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (scalarModules J R) (.up ℤ)
  let : (scalarRestriction a.symm.hom).Braided := o.monoidal
  let : (scalarRestriction a.symm.hom).IsEquivalence :=
    o.functor_eq ▸ o.equivalence.isEquivalence_functor
  let : Fc.Braided := scalarComplexBraided a.symm
  let := scalarCochainSymmetric R
  let := scalarCochainSymmetric S
  let := qR
  let := qS
  have : IsIso (Functor.LaxMonoidal.ε QR) := hεR
  have : IsIso (Functor.LaxMonoidal.ε QS) := hεS
  let : W.localizerMorphismKFlat.IsLeftDerivabilityStructure := scalarDerivability R
  apply normalizedBraidedLocalization QR QS Fc G F.mapDerivedCategoryFactors W
  · intro X
    let K := QR.objPreimage X
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
    exact ⟨P, (scalar_kflat_test R P).1 hP,
      ⟨Localization.isoOfHom QR W f hf ≪≫ QR.objObjPreimageIso X⟩⟩
  · intro P Q hQ
    exact hμR P Q ((scalar_kflat_test R Q).2 hQ)
  · intro P Q hQ
    exact hμS P (Fc.obj Q) (o.kflat_iff Q |>.2 ((scalar_kflat_test R Q).2 hQ))

end SheafOfModules
