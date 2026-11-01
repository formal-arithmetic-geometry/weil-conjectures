/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientPullbackIso

/-! # Finite scalar realization of the canonical locally closed extension

Source: blueprint scalar-six-ctf (1), comparison of locally closed extensions.
(blueprint: lem-sfb-finite-scalar-etale-extension-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

private def realizationOpenIso {S T : Scheme.{u}} (j : S ⟶ T)
    [IsOpenImmersion j] :
    finiteComparisonRealization A S eR ⋙
        openImmersionLowerShriek (Profinite.continuousMapRingObj A) j ≅
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j ⋙
        finiteComparisonRealization A T eR := by
  let ES := finiteDiscreteCoefficientEquivalence A eR
    (internalToModule (ULift.{u + 1} A)) rfl S
  let ET := finiteDiscreteCoefficientEquivalence A eR
    (internalToModule (ULift.{u + 1} A)) rfl T
  let i := finiteDiscreteCoefficientProEtalePullbackIso A eR
    (internalToModule (ULift.{u + 1} A)) rfl j
  let k := Iso.isoCompInverse (H := ES) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let adj₁ := ES.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.continuousMapRingObj A) j)
  let adj₂ := (ProEtale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).comp ET.toAdjunction
  exact Functor.isoWhiskerRight (realizedEncodingIso A S eR) _ ≪≫
    adj₁.leftAdjointUniq (adj₂.ofNatIsoRight kr) ≪≫
    Functor.isoWhiskerLeft _ (realizedEncodingIso A T eR).symm

private def realizationPushIso {S T : Scheme.{u}} (f : S ⟶ T) :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        finiteComparisonRealization A T eR ≅
      finiteComparisonRealization A S eR ⋙ lowerStar (Profinite.continuousMapRingObj A) f :=
  Functor.isoWhiskerLeft _ (realizedEncodingIso A T eR) ≪≫
    (finiteDiscreteCoefficientRestrictionIso A eR
      (internalToModule (ULift.{u + 1} A)) rfl f).symm ≪≫
    Functor.isoWhiskerRight (realizedEncodingIso A S eR).symm _

private abbrev realizationHeart (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⥤
      ModuleRingedComparison.internalModules Λ.X T :=
  comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T ⋙
    finiteComparisonRealization A T eR ⋙
      Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (coefficientMap e.hom.hom T)

-- The realization contains three canonical derived-category instance dictionaries.

private def realizationSingleIso (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (sfbFiniteScalarRealization A e eR T).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((realizationHeart A e eR T).obj M) := by
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let H := finiteComparisonRealization A T eR
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.hom.hom T)
  exact U.mapDerivedCategory.mapIso
      (H.mapDerivedCategory.mapIso ((N.mapDerivedCategorySingleFunctor 0).app M) ≪≫
        (H.mapDerivedCategorySingleFunctor 0).app (N.obj M)) ≪≫
    (U.mapDerivedCategorySingleFunctor 0).app (H.obj (N.obj M))

private theorem comparisonExtensionIso {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).obj
        ((flatModelEtaleExtension _ a ha).obj L) ≅
      (by
        let : IsImmersion a := ha
        let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
        exact (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) a.imageι).obj
          ((ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) a.toImage).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).obj L)))) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let := ProEtale.isIso_lowerStarComparisonUpperStarBaseChange a.imageι B
  exact ⟨(asIso (lowerStarComparisonUpperStarBaseChange a.imageι B)).app
      ((Etale.openImmersionLowerShriek B a.toImage).obj L) ≪≫
    (ProEtale.lowerStar B a.imageι).mapIso
      ((openImmersionLowerShriekComparisonUpperStarIso B a.toImage).app L)⟩

private theorem realizationCoefficientExtensionIso {S T X : Scheme.{u}}
    (j : S ⟶ T) [IsOpenImmersion j] (i : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    Nonempty ((finiteComparisonRealization A X eR).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj
          ((ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj M)) ≅
      (lowerStar (Profinite.continuousMapRingObj A) i).obj
        ((openImmersionLowerShriek (Profinite.continuousMapRingObj A) j).obj
          ((finiteComparisonRealization A S eR).obj M))) := by
  exact ⟨(realizationPushIso A eR i).app _ ≪≫
    (lowerStar (Profinite.continuousMapRingObj A) i).mapIso
      ((realizationOpenIso A eR j).symm.app M)⟩

private theorem realizationTransportExtensionIso
    {R R' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj R'] [IsCommMonObj R']
    (c : R ⟶ R') [IsMonHom c] {S T X : Scheme.{u}}
    (j : S ⟶ T) [IsOpenImmersion j] (i : T ⟶ X)
    (M : ModuleRingedComparison.internalModules R' S) :
    Nonempty ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap c X)).obj
      ((lowerStar R' i).obj ((openImmersionLowerShriek R' j).obj M)) ≅
      (lowerStar R i).obj ((openImmersionLowerShriek R j).obj
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (coefficientMap c S)).obj M))) := by
  exact ⟨(comapLowerStarIso c i).app _ ≪≫
    (lowerStar R i).mapIso ((comapOpenImmersionLowerShriekIso c j).app M)⟩

private theorem realizationExtensionIso {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    Nonempty ((realizationHeart A e eR X).obj ((flatModelEtaleExtension _ a ha).obj L) ≅
      (by
        let : IsImmersion a := ha
        let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
        exact (lowerStar Λ.X a.imageι).obj
          ((openImmersionLowerShriek Λ.X a.toImage).obj
            ((realizationHeart A e eR S).obj L)))) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S
  let H (T : Scheme.{u}) := finiteComparisonRealization A T eR
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.hom.hom X)
  obtain ⟨n⟩ := comparisonExtensionIso A a ha L
  obtain ⟨h⟩ := realizationCoefficientExtensionIso A eR a.toImage a.imageι (N.obj L)
  obtain ⟨t⟩ := realizationTransportExtensionIso
    (R := Λ.X) (R' := Profinite.continuousMapRingObj A) e.hom.hom
    a.toImage a.imageι ((H S).obj (N.obj L))
  exact ⟨U.mapIso ((H X).mapIso n ≪≫ h) ≪≫ t⟩

private theorem realizationClosedExact {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a) :
    PreservesFiniteColimits (lowerStar Λ.X a.imageι) := by
  obtain ⟨hu, hJlim, hJcolim, hPlim, hPcolim, hrest⟩ :=
    ((coefficientHeart_locallyClosedExtension Λ.X X).2 S a ha).2.2.2.2.2
  exact hPcolim

/-- On a sheaf in degree zero, finite scalar realization commutes with the canonical
locally closed extension through the scheme-theoretic image.

Source: blueprint scalar-six-ctf (1), ordinary/internal compactification comparison and
coefficient-isomorphism transport.
(blueprint: lem-sfb-finite-scalar-etale-extension-iso).

Proof: Factor a through its scheme-theoretic image as an open immersion followed by
its closed image inclusion. The sheaf-level étale/pro-étale direct-image comparison
and open-extension comparison identify the two ordinary extensions. The specified
finite coefficient realization is isomorphic to the canonical module encoding;
restriction compatibility gives its closed-pushforward comparison, while pullback
compatibility and uniqueness of left adjoints give its open-extension comparison.
The two coefficient-restriction isomorphisms transport this identification along e.
Thus the heart realization commutes with the specified extension. Each of its three
exact functors commutes with the degree-zero single functor. Finally the closed
internal pushforward is exact by coefficientHeart_locallyClosedExtension, so its
right derived functor also agrees with the single functor on this input. Composing
these isomorphisms gives the result. Zero rings and empty strata need no exclusions. -/
theorem sfbFiniteScalarEtaleExtensionIso
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsNoetherian X.left]
    (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    Nonempty ((sfbFiniteScalarRealization A e eR X.left).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension (ULift.{u + 1} A) a ha).obj L)) ≅
      (sfbLocallyClosedDerivedExtension Λ a ha).obj
        ((sfbFiniteScalarRealization A e eR S).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let R (T : Scheme.{u}) := realizationHeart A e eR T
  let J := openImmersionLowerShriek Λ.X a.toImage
  let P := lowerStar Λ.X a.imageι
  have : PreservesFiniteColimits P := realizationClosedExact (Λ := Λ) a ha
  let F := sfbLocallyClosedDerivedExtension Λ a ha
  let z : F.obj ((sfbFiniteScalarRealization A e eR S).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (P.obj (J.obj ((R S).obj L))) :=
    F.mapIso (realizationSingleIso A e eR S L) ≪≫
      P.rightDerivedFunctor.mapIso ((J.mapDerivedCategorySingleFunctor 0).app _) ≪≫
      P.rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (P.mapDerivedCategorySingleFunctor 0).app _
  obtain ⟨h⟩ := realizationExtensionIso A e eR a ha L
  exact ⟨realizationSingleIso A e eR X.left _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso h ≪≫
    z.symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing
