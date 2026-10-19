/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.RingedSitePerfectDualLocalModel
import Sheaf.CategoryTheory.RingedSitePerfectBidualModel
import Sheaf.CategoryTheory.RingedSitePerfectEvaluationModel

/-! # Perfect duality on a small ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ,
lemma-dual-perfect-complex (blueprint: lem-sfb-ringed-site-perfect-duality).
The canonical maps are explicit transposes of evaluation in a normalized K-flat
closed tensor-Hom presentation, rather than unspecified isomorphic morphisms.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory


private theorem bidual_isIso_of_iso
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (s : @SymmetricCategory D _ S.monoidal) (O : D)
    {P Q : D} (e : P ≅ Q) (hQ : IsIso (ringedSiteBidual S s O Q)) :
    IsIso (ringedSiteBidual S s O P) := by
  have := hQ
  let d := H.mapIso (Iso.prod e.op (Iso.refl O))
  have hd : IsIso (H.map (Prod.mkHom e.hom.op (𝟙 O))) := d.isIso_hom
  have hdd : IsIso (H.map
      (Prod.mkHom (H.map (Prod.mkHom e.hom.op (𝟙 O))).op (𝟙 O))) :=
    (H.mapIso (Iso.prod d.op (Iso.refl O))).isIso_hom
  have : IsIso (ringedSiteBidual S s O P ≫
      H.map (Prod.mkHom (H.map (Prod.mkHom e.hom.op (𝟙 O))).op (𝟙 O))) := by
    rw [← ringedSiteBidual_naturality S s O e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (H.map (Prod.mkHom (H.map (Prod.mkHom e.hom.op (𝟙 O))).op (𝟙 O)))

private theorem evaluation_isIso_of_iso
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (O : D) (u : S.monoidal.tensorUnit ≅ O)
    {P Q : D} (e : P ≅ Q) (N : D)
    (hQ : IsIso (ringedSiteDualEvaluation S O u Q N)) :
    IsIso (ringedSiteDualEvaluation S O u P N) := by
  have := hQ
  let d := H.mapIso (Iso.prod e.op (Iso.refl O))
  have hd : IsIso (H.map (Prod.mkHom e.hom.op (𝟙 O))) := d.isIso_hom
  have hn : IsIso (H.map (Prod.mkHom e.hom.op (𝟙 N))) :=
    (H.mapIso (Iso.prod e.op (Iso.refl N))).isIso_hom
  have ht : IsIso (S.tensor.map (Prod.mkHom (𝟙 N)
      (H.map (Prod.mkHom e.hom.op (𝟙 O))))) :=
    (S.tensor.mapIso (Iso.prod (Iso.refl N) d)).isIso_hom
  have : IsIso (S.tensor.map (Prod.mkHom (𝟙 N)
      (H.map (Prod.mkHom e.hom.op (𝟙 O)))) ≫ ringedSiteDualEvaluation S O u P N) := by
    rw [ringedSiteDualEvaluation_source_naturality S O u e.hom N]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (S.tensor.map (Prod.mkHom (𝟙 N) (H.map (Prod.mkHom e.hom.op (𝟙 O))))) _

/-- Perfect-complex duality for the specified canonical maps.
The existential is a normalized presentation of the already recorded derived
tensor and Hom: its transposition, unit, associator and symmetry are fixed on
ordinary representatives. It is not a choice of an arbitrary bidual morphism or
an arbitrary isomorphism. The last clause says the actual canonical evaluation
natural transformation is invertible, in the tensor order of the node.
Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex
(blueprint: lem-sfb-ringed-site-perfect-duality).

Proof:
1. Choose the complex representative K recorded by the perfectness hypothesis and
   a normalized closed tensor-Hom model M supplied by the canonical-map theorem.
2. Put L=Hom(K,I(O[0])) and take its fixed outer K-injective replacement I(L).
   On each covering slice the proved ordinary-dual calculation supplies a bounded
   finite-free-retract model. The exact-source Hom comparison and K-injective
   lifting give an actual quasi-isomorphism from that model to I(L) restricted
   to the slice. Thus I(L) is locally strictly perfect.
3. The fixed Hom comparison, the K-injective augmentation of L and source
   naturality identify Q(I(L)) with the coefficient dual of the original P.
   This proves perfectness of that precise derived dual object.
4. For strict-perfect sources, the separate ordinary finite diagonal evaluation
   calculation, K-flatness of the ordinary dual and bounded exact-source Hom
   comparison make the normalized derived evaluation invertible. Exact slice
   restriction and the covering sheaf criterion detect quasi-isomorphisms;
   right-fraction presentations extend this to derived morphisms. Therefore
   canonical evaluation for K is invertible for every unbounded target.
5. In a closed symmetric category, invertibility of these evaluation components
   supplies coevaluation and both pairing triangles. The corresponding Hom-set
   equivalences identify the specified canonical bidual map, so it is invertible.
   This is the proved categorical bidual-model lemma.
6. Source naturality transports biduality and evaluation along P isomorphic to
   QK. The specified symmetry changes the evaluation tensor order, and
   componentwise invertibility makes its canonical natural transformation an
   isomorphism. No global bounds on P or on its dual are imposed. -/
theorem ringedSitePerfectDuality
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (P : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R P) :
    ∃ M : RingedSiteDualityModel.{c, v, r, w} J R,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op P, ringedSiteDualityUnit.{c, v, r, w} J R)) ∧
      IsIso (ringedSiteBidual M.closed M.symmetric
        (ringedSiteDualityUnit.{c, v, r, w} J R) P) ∧
      IsIso (ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric
        (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P) := by
  classical
  obtain ⟨K, hK, ⟨eP⟩⟩ := hP
  obtain ⟨M⟩ := ringedSiteDualityMaps_exists.{c, v, r, w} J R
  let O := ringedSiteDualityUnit.{c, v, r, w} J R
  let O₀ := ringedSiteDualityUnitComplex.{c, v, r} J R
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  let L := homComplex (R := R) K
    ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj O₀)
  let I := WeilConjectures.coefficientHomResolution.{r, c, v} J R
  have hlocal : SheafOfModules.IsLocallyStrictPerfectComplexOfUniverses.{c, v, r} R
      (I.obj L) := ringedSitePerfectDual_localModel.{c, v, r, w} J R K hK
  have : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  have hη : QuasiIso ((ringedSiteHomAugmentation.{c, v, r} J R).app L) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} _ L).2
  have : IsIso (DerivedCategory.Q.map
      ((ringedSiteHomAugmentation.{c, v, r} J R).app L)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hη
  have hbidual : IsIso (ringedSiteBidual M.closed M.symmetric O
      (DerivedCategory.Q.obj K)) :=
    ringedSitePerfectBidual_model.{c, v, r, w} J R K hK M
  have heval : ∀ N, IsIso (ringedSiteDualEvaluation M.closed O M.unitIso
      (DerivedCategory.Q.obj K) N) :=
    fun N ↦ ringedSitePerfectEvaluation_model.{c, v, r, w} J R K hK M N
  refine ⟨M, ?_, ?_, ?_⟩
  · refine ⟨_, hlocal, ?_⟩
    exact ⟨H.mapIso (Iso.prod eP.symm.op (Iso.refl O)) ≪≫
      WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R K O₀ ≪≫
        asIso (DerivedCategory.Q.map
          ((ringedSiteHomAugmentation.{c, v, r} J R).app L))⟩
  · exact bidual_isIso_of_iso M.closed M.symmetric O eP hbidual
  · have hcomponents (N) : IsIso
        ((ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric O M.unitIso P).app N) := by
      have : IsIso (ringedSiteDualEvaluation M.closed O M.unitIso P N) :=
        evaluation_isIso_of_iso M.closed O M.unitIso eP N (heval N)
      change IsIso (ringedSiteDualEvaluationLeft M.closed M.symmetric O M.unitIso P N)
      dsimp only [ringedSiteDualEvaluationLeft]
      infer_instance
    exact NatIso.isIso_of_isIso_app _

end CategoryTheory
