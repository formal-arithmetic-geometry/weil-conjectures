/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Ringed.RingedHomComplexTransport
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedHomTransport
import WeilConjectures.CategoryTheory.NativeRingedRestrictionEquivalence
import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Scalar.ScalarIsoInternalHom

/-! # Derived Hom under a site equivalence and coefficient identification

Source: Stacks Project, Tags 03CR, 03D7, 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-site-equivalence-hom-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c d vc vd r w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

private def scalarRoundTrip {C : Type c} [Category.{vc} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (a : R ≅ S) :
    SheafOfModules.restrictScalars.{r} a.hom ⋙
      SheafOfModules.restrictScalars a.inv ≅ 𝟭 (SheafOfModules.{r} S) :=
  SheafOfModules.pushforwardComp (F := 𝟭 C) (G := 𝟭 C) a.inv a.hom ≪≫
    SheafOfModules.pushforwardCongr a.inv_hom_id ≪≫ SheafOfModules.pushforwardId S

private def scalarEquivalence {C : Type c} [Category.{vc} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (a : R ≅ S) :
    SheafOfModules.{r} S ≌ SheafOfModules.{r} R where
  functor := SheafOfModules.restrictScalars a.hom
  inverse := SheafOfModules.restrictScalars a.inv
  unitIso := (scalarRoundTrip a).symm
  counitIso := scalarRoundTrip a.symm
  functor_unitIso_comp M := by ext V x; rfl

set_option maxHeartbeats 1800000 in
-- The unbounded derived comparisons require elaborating several functor structures.
/-- A site equivalence with an identified coefficient sheaf gives a module
 equivalence compatible with the actual derived internal Hom.
Source: Stacks Project, Tags 03CR, 03D7, 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-site-equivalence-hom-transport).

Proof: take direct restriction along the inverse site equivalence, followed by
scalar restriction along the given ring isomorphism. Both are additive
equivalences. The first preserves sheaf Hom by equivalence on every slice, and
the second by scalar surjectivity. Compose their ordinary comparisons and their
naturality squares. Countable products give the natural Hom-complex comparison;
functorial K-injective resolutions then give the natural derived comparison.
The composite module functor is the actual structural pushforward: its section
modules, scalar action, restriction maps, and morphism maps agree. -/
theorem siteCoefficientEquivalence_derivedHom
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J CommRingCat.{max c d vc vd r})
    (S : Sheaf K CommRingCat.{max c d vc vd r})
    (a : S ≅ (e.inverse.sheafPushforwardContinuous CommRingCat K J).obj R)
    [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, c, vc} R)]
    [HasDerivedCategory.{w'} (NativeModules.{max c d vc vd r, d, vd} S)] :
    ∃ E : NativeModules.{max c d vc vd r, c, vc} R ≌
        NativeModules.{max c d vc vd r, d, vd} S,
      ∃ ha : E.functor.Additive,
        Nonempty (E.functor ≅ SheafOfModules.pushforward.{max c d vc vd r}
          ((sheafCompose K
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).map a.hom)) ∧
        letI := ha
        Nonempty (derivedInternalHomOfUniverses.{c, vc, max d vd r, w} J R ⋙
          E.functor.mapDerivedCategory ≅
          (E.functor.mapDerivedCategory.op.prod E.functor.mapDerivedCategory) ⋙
            derivedInternalHomOfUniverses.{d, vd, max c vc r, w'} K S) := by
  let R' := restrictedCommRing.{d, c, vd, vc, r} (K := K) e.inverse R
  let T := restrictModules.{d, c, vd, vc, r} (K := K) e.inverse R
  have : T.IsEquivalence := restrictModules_isEquivalence.{c, d, vc, vd, r} e R
  have : T.Additive := restrictModules_additive.{d, c, vd, vc, r} e.inverse R
  let a' := (sheafCompose K
    (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).mapIso a
  let G := scalarEquivalence a'
  have : G.functor.Additive :=
    inferInstanceAs (SheafOfModules.restrictScalars a'.hom).Additive
  let E := T.asEquivalence.trans G
  have ha : E.functor.Additive := by
    change (T ⋙ G.functor).Additive
    infer_instance
  obtain ⟨δ, hδ⟩ := scalarIso_internalHom.{d, vd, max c vc r} R' S a
  have hF (X : D) : (Over.post (X := X) e.inverse).IsEquivalence := inferInstance
  let γ (M N : NativeModules.{max c d vc vd r, c, vc} R) :
      E.functor.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := S) (E.functor.obj M) (E.functor.obj N) :=
    G.functor.mapIso (sheafHomIso.{d, c, vd, vc, r} e.inverse R hF M N) ≪≫
      δ (T.obj M) (T.obj N)
  have hγ {M M' N N' : NativeModules.{max c d vc vd r, c, vc} R}
      (f : M' ⟶ M) (g : N ⟶ N') :
      E.functor.map (SheafOfModules.homObjMap (R := R) f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ SheafOfModules.homObjMap (R := S)
          (E.functor.map f) (E.functor.map g) := by
    let β (M N : NativeModules.{max c d vc vd r, c, vc} R) :
        T.obj (SheafOfModules.homObj (R := R) M N) ≅
          SheafOfModules.homObj (R := R') (T.obj M) (T.obj N) :=
      sheafHomIso.{d, c, vd, vc, r} e.inverse R hF M N
    have ht : T.map (SheafOfModules.homObjMap (R := R) f g) ≫ (β M' N').hom =
        (β M N).hom ≫ SheafOfModules.homObjMap (R := R') (T.map f) (T.map g) :=
      sheafHomIso_naturality.{d, c, vd, vc, r} e.inverse R hF f g
    have hs : G.functor.map (SheafOfModules.homObjMap (R := R') (T.map f) (T.map g)) ≫
        (δ (T.obj M') (T.obj N')).hom = (δ (T.obj M) (T.obj N)).hom ≫
          SheafOfModules.homObjMap (R := S) (G.functor.map (T.map f))
            (G.functor.map (T.map g)) := hδ (T.map f) (T.map g)
    change G.functor.map (T.map (SheafOfModules.homObjMap (R := R) f g)) ≫
        (G.functor.map (β M' N').hom ≫ (δ (T.obj M') (T.obj N')).hom) =
      (G.functor.map (β M N).hom ≫ (δ (T.obj M) (T.obj N)).hom) ≫
        SheafOfModules.homObjMap (R := S) (G.functor.map (T.map f))
          (G.functor.map (T.map g))
    calc
      _ = G.functor.map (T.map (SheafOfModules.homObjMap (R := R) f g) ≫
          (β M' N').hom) ≫ (δ (T.obj M') (T.obj N')).hom :=
        (G.functor.map_comp_assoc _ _ _).symm
      _ = G.functor.map ((β M N).hom ≫
          SheafOfModules.homObjMap (R := R') (T.map f) (T.map g)) ≫
            (δ (T.obj M') (T.obj N')).hom :=
        congrArg (fun k ↦ G.functor.map k ≫ (δ (T.obj M') (T.obj N')).hom) ht
      _ = G.functor.map (β M N).hom ≫
          (G.functor.map (SheafOfModules.homObjMap (R := R') (T.map f) (T.map g)) ≫
            (δ (T.obj M') (T.obj N')).hom) := G.functor.map_comp_assoc _ _ _
      _ = G.functor.map (β M N).hom ≫ ((δ (T.obj M) (T.obj N)).hom ≫
          SheafOfModules.homObjMap (R := S) (G.functor.map (T.map f))
            (G.functor.map (T.map g))) :=
        congrArg (fun k ↦ G.functor.map (β M N).hom ≫ k) hs
      _ = _ := (Category.assoc _ _ _).symm
  obtain ⟨γc⟩ := homComplex_transport.{c, d, vc, vd, r} R S E.functor γ hγ
  refine ⟨E, ha, ⟨?_, derivedHom_transport.{c, d, vc, vd, r, w, w'} R S E γc⟩⟩
  exact ⟨NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso (Iso.refl _))
    (by intro M N f; apply (SheafOfModules.fullyFaithfulForget _).map_injective; rfl)⟩

end CategoryTheory.NativeRestriction
