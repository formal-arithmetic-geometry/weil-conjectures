/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer
import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# Homology of sections of prescribed injective resolutions

Source: Stacks Project, Tags 0A50 and 03F3.
The Hom-complex construction follows `Sheaf.resolution_section_cohomology`, with a
representing object supplied explicitly so that it also handles larger coefficient universes.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

open CochainComplex HomComplex in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def representedSectionComplexIso
    {X : Scheme.{u}} (W : X.Etale)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      (A ⟶ F) ≃+ F.obj.obj (op W))
    (he : ∀ {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (f : F ⟶ G) (a : A ⟶ F), e G (a ≫ f) = f.hom.app (op W) (e F a))
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj A) K ≅
      (((etaleSectionFunctor W ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).mapHomologicalComplex
        (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      ((e (K.X n)).trans AddEquiv.ulift.symm)).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
        change ULift.up ((K.d i j).hom.app (op W)
          (e (K.X i)
            (Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk a (zero_add i))))) =
          ULift.up (e (K.X j)
            (Cochain.fromSingleEquiv (zero_add j)
              (δ i j (Cochain.fromSingleMk a (zero_add i)))))
        simp only [Cochain.δ_fromSingleMk, zero_add, Cochain.fromSingleEquiv_fromSingleMk]
        exact congrArg ULift.up (he (K.d i j) a).symm)

private lemma representedSectionHomology
    {X : Scheme.{u}} (W : X.Etale)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      (A ⟶ F) ≃+ F.obj.obj (op W))
    (he : ∀ {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (f : F ⟶ G) (a : A ⟶ F), e G (a ≫ f) = f.hom.app (op W) (e F a))
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (q : ℕ) :
    Nonempty ((((etaleSectionFunctor W).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).homology q ≃+ Abelian.Ext A F q) := by
  let E := etaleSectionFunctor W
  let h := (CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor _ 0).obj A)
    I.cochainComplex (q : ℤ)).homologyIso.symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ (q : ℤ)).mapIso
        (representedSectionComplexIso W A e he I.cochainComplex) ≪≫
      (((E.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc
        (q : ℤ)).mapHomologyIso AddCommGrpCat.uliftFunctor.{u + 1, u + 1}
  let extEquiv := (I.extAddEquivCohomologyClass.trans
    (h.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)).symm
  let c := (HomologicalComplex.homologyFunctor _ _ (q : ℤ)).mapIso
    (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat E)
  let d := ((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := q) rfl
  exact ⟨(d.symm ≪≫ c.symm).addCommGroupIsoToAddEquiv.trans extEquiv⟩

private noncomputable def globalSectionEquiv {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (EtaleOpenComparison.integerSheaf X ⟶ F) ≃+
      F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

private lemma globalSectionEquiv_naturality {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (a : EtaleOpenComparison.integerSheaf X ⟶ F) :
    globalSectionEquiv G (a ≫ f) =
      f.hom.app (op (Scheme.Etale.mk (𝟙 X))) (globalSectionEquiv F a) := by
  dsimp only [globalSectionEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private lemma globalSectionHomology {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (q : ℕ) :
    Nonempty ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homology q ≃+ Sheaf.H F q) := by
  exact representedSectionHomology _ _ globalSectionEquiv
    (fun f a ↦ globalSectionEquiv_naturality f a) I q

private lemma openSectionHomology {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (W : X.Opens) (q : ℕ) :
    Nonempty ((((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homology q ≃+
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q) := by
  obtain ⟨e⟩ := representedSectionHomology (Scheme.Etale.mk W.ι) _
    (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk W.ι))
    (fun f a ↦ EtaleOpenComparison.sectionsEquiv_naturality _ _ f a) I q
  let rho := (upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} W.ι).symm.app F
  let h := (((Abelian.extFunctor q).obj
    (op (EtaleOpenComparison.integerSheaf (W : Scheme.{u})))).mapIso rho)
  exact ⟨e.trans ((etaleCohomologyOverOpenEquiv W.ι F q).trans
    h.addCommGroupIsoToAddEquiv)⟩

set_option linter.unusedVariables false in
/-- The four degreewise additive equivalences underlying the natural comparison.
Source: Stacks Project, Tag 0A50. (blueprint: lem-weil-pbc-etale-resolution-section-homology-data).
Proof: identify the Hom complex computing Ext for each prescribed injective resolution with the
corresponding section complex, using the constant-sheaf/sections adjunction and evaluation at 1;
localization gives the same construction on every open. -/
theorem exists_resolutionSection_homology_data
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0)) :
    ∃ eX : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+ Sheaf.H G q,
    ∃ eOX : ∀ (W : X.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q,
    ∃ eY : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 Y))).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q,
    ∃ eOY : ∀ (W : Y.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj
            ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q, True := by
  classical
  exact ⟨fun q ↦ (globalSectionHomology I q).some,
    fun W q ↦ (openSectionHomology I W q).some,
    fun q ↦ (globalSectionHomology J q).some,
    fun W q ↦ (openSectionHomology J W q).some, trivial⟩
end AlgebraicGeometry.Etale
