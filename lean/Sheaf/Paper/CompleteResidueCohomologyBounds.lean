/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IntegralReductionFlatFiltration
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.Algebra.Homology.Monoidal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic

/-! # Cohomological bounds from complete residue Tor amplitude

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1) and (2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

The completion is the inverse limit of constant quotient ring sheaves, not the
constant sheaf of the valuation ring. Level zero of the reduction API means the
positive exponent one, hence the residue field. No characteristic, constructibility,
or local constancy condition is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem abSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

private theorem abLocallyBijective (Y : Scheme.{u}) :
    (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

attribute [local instance] abSheafify abLocallyBijective

open Opposite CategoryTheory.Pretriangulated


open MonoidalCategory

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  proEtaleRingModules_hasDerivedCategory
  integralCoefficientRingSheafify integralCoefficientAbSheafify
  integralCoefficientAbLocallyBijective
  integralTowerHasDerivedCategory integralReductionSourceHasDerivedCategory
  integralReductionTargetHasDerivedCategory scalarReductionSourceDerived
  scalarReductionTargetDerived integralReductionSiteEssentiallySmall scalarReductionSiteSmall in
private theorem tor_vanishes
    (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory.{u} Y A) (a b : ℤ)
    (hK : HasProEtaleTorAmplitude.{u} Y A K a b) (j : ℤ) (hj : j < a ∨ b < j) :
    IsZero ((@DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules.{u} Y (proEtaleConstantRing.{u} Y A)) _
      (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ inferInstance (ProEt.topology Y)
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y A))
        (integralCoefficientAbSheafify.{u, u} Y)
        (integralCoefficientAbLocallyBijective.{u, u} Y))
      (HasDerivedCategory.standard.{u + 1, u + 2} _) j).obj K) := by
  classical
  let R := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} A))
  let C := SheafOfModules.{u + 1} ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let : MonoidalCategory C := SheafOfModules.monoidalCategory R
  let := HasDerivedCategory.standard C
  have : (DerivedCategory.Q (C := C)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso _ (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e := (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u} (R := R) L
  have hz := hK.2 L P ⟨e⟩ f hf hP (𝟙_ C) j hj
  have : QuasiIso f := hf
  let ep : derivedTensor Y A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (𝟙_ C)) P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  exact hz.of_iso ((DerivedCategory.homologyFunctor.{u + 2} C j).mapIso ep.symm)


private theorem limit_bounds
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasCountableProducts C]
    [∀ q : ℤ, PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor C q)]
    (F : ℕᵒᵖ ⥤ DerivedCategory C)
    [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (K : DerivedCategory C) (p : K ⟶ ∏ᶜ (fun n : ℕ ↦ F.obj (op n)))
    (δ : (∏ᶜ (fun n : ℕ ↦ F.obj (op n))) ⟶ K⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op) K p δ)
    (a b : ℤ)
    (hz : ∀ n : ℕ, ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor C j).obj (F.obj (op n))))
    (hb : ∀ n : ℕ, Epi ((DerivedCategory.homologyFunctor C b).map
      (F.map (homOfLE n.le_succ).op)))
    (hML : ∀ M : ℕᵒᵖ ⥤ C, (∀ n : ℕ, Epi (M.map (homOfLE n.le_succ).op)) →
      Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
        (fun n ↦ M.map (homOfLE n.le_succ).op))) :
    ∀ j : ℤ, j < a ∨ b < j → IsZero ((DerivedCategory.homologyFunctor C j).obj K) := by
  classical
  let T := Triangle.mk p (towerTransitionEndomorphism
    (fun n ↦ F.map (homOfLE n.le_succ).op)) δ
  have hT : T ∈ distTriang _ := hlim
  have hprod (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor C q).obj
        (∏ᶜ (fun n : ℕ ↦ F.obj (op n)))) := by
    let H := DerivedCategory.homologyFunctor C q
    let hc := isLimitOfPreserves H
      (limit.isLimit (Discrete.functor (fun n : ℕ ↦ F.obj (op n))))
    exact (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun ⟨n⟩ ↦ (hz n q hq).eq_of_tgt _ _)
  intro j hj
  have hnext := hprod j hj
  have hepi : Epi ((DerivedCategory.homologyFunctor C (j - 1)).map T.mor₂) := by
    by_cases htop : j - 1 = b
    · let H := DerivedCategory.homologyFunctor C b
      let M := F ⋙ H
      have hM : ∀ n : ℕ, Epi (M.map (homOfLE n.le_succ).op) := hb
      have := hML M hM
      let e := asIso (piComparison H (fun n : ℕ ↦ F.obj (op n)))
      have he : H.map T.mor₂ ≫ e.hom = e.hom ≫
          towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
        (fun n ↦ M.map (homOfLE n.le_succ).op) := by
        apply Pi.hom_ext
        intro n
        simp only [Category.assoc, e, asIso_hom, piComparison_comp_π]
        rw [← H.map_comp]
        change H.map (towerTransitionEndomorphism _ ≫ Pi.π _ n) = _
        rw [(towerTransitionEndomorphism_eq_iff _ _).mp rfl n]
        simp [Functor.map_sub, Functor.map_comp, towerTransitionEndomorphism,
          towerProductShift, M]
      have hmap : Epi (H.map T.mor₂) := by
        have : Epi (H.map T.mor₂ ≫ e.hom) := by rw [he]; infer_instance
        exact (epi_comp_iff_of_isIso _ e.hom).mp inferInstance
      rw [htop]
      exact hmap
    · have hprev : j - 1 < a ∨ b < j - 1 := by omega
      exact ⟨fun _ _ _ ↦ (hprod (j - 1) hprev).eq_of_src _ _⟩
  have hsurj := (DerivedCategory.HomologySequence.exact₁ T hT
    (j - 1) j (by omega)).epi_f (hnext.eq_of_tgt _ _)
  have hzero := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT
    (j - 1) j (by omega)).mp hepi
  dsimp only at hsurj hzero
  rw [hzero] at hsurj
  exact @IsZero.of_epi_zero _ _ _ _ _ hsurj


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  proEtaleRingModules_hasDerivedCategory
  integralCoefficientRingSheafify integralCoefficientAbSheafify
  integralCoefficientAbLocallyBijective
  integralTowerHasDerivedCategory integralReductionSourceHasDerivedCategory
  integralReductionTargetHasDerivedCategory scalarReductionSourceDerived
  scalarReductionTargetDerived integralReductionSiteEssentiallySmall scalarReductionSiteSmall in
/-- A derived-complete complex has the same cohomological bounds as a Tor interval
of its residue reduction, tested after restriction to every small-site object.

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1),(2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

Proof:
1. Test residue Tor amplitude with the coefficient sheaf itself on X. The tensor
unit identity gives vanishing of residue cohomology outside [a,b].
2. Choose one flat-term K-flat resolution P by lem-pc-kflat-resolution. By
lem-pur-derived-change-of-rings its reductions compute every K_n. Their actual
chain maps 1_P tensor (C_(n+1) to C_n) give the canonical quotient transitions.
3. The DVR coefficient sequence 0 to k_X to C_(n+1) to C_n to 0 is short exact:
the first map sends r to varpi^n r; cancellation proves injectivity and identifies
its image with the quotient kernel. Surjectivity and these identities pass to
constant sheaves locally. Compatibility of the limit projections makes the maps
B_X-linear (def-weil-l-adic-coefficient-extension, def-weil-pbc-constant-sheaf).
4. Flatness of each term of P preserves this exact sequence
(def-pc-flat-sheaf-modules). Apply lem-weil-pbc-complex-ses-triangle and
lem-sf-derived-homology-long-exact to obtain the cohomology exact sequences.
5. Induction gives cohomology in [a,b] for all K_n. The exact sequence in degree b
also makes each canonical transition on H^b epimorphic.
6. Apply det-pe-milnor-sequence to this strict tower. By det-pe-products-derived,
its termwise product represents the product in D(Mod(B_X)), and localization
identifies 1-T with the tower transition endomorphism. Rotating the cone triangle
gives a Roos triangle (def-weil-abstract-derived-category,
def-weil-triangulated-category, def-weil-derived-limit). Completeness and the
uniqueness clause of lem-weil-derived-limit-existence identify K up to isomorphism
with this Milnor middle term.
7. For j<a and j>b+1 both outer Milnor terms vanish. At j=b+1, the right term is
zero and det-pe-milnor-epimorphic kills R^1 lim H^b(K_n), since its transitions are
epimorphic. Exactness gives the asserted vanishing in every remaining degree. -/
theorem complete_residue_cohomology_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X]
    (K : @DerivedCategory (integralTowerModules.{u, u} l E X) _
      (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
        (completedIntegralCoefficientSheafUnrestricted l E X)
        (integralCoefficientAbSheafify.{u, u} X)
        (integralCoefficientAbLocallyBijective.{u, u} X))
      (integralTowerHasDerivedCategory.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) a b) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj K) := by
  classical
  obtain ⟨D, hl, P, G, q, hq, e, hprod, δ, hlim⟩ := _hcomplete
  let F := integralReductionTower.{0, u, u} l E X D hl P
  let := hprod
  let : Abelian (integralTowerModules.{u, u} l E X) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ inferInstance _ _
      (integralCoefficientAbSheafify.{u, u} X)
      (integralCoefficientAbLocallyBijective.{u, u} X)
  let : HasDerivedCategory.{u + 2} (integralTowerModules.{u, u} l E X) :=
    integralTowerHasDerivedCategory.{u, u} l E X
  let : HasDerivedCategory.{u + 2} (completedIntegralModuleSheaves l E X D hl) :=
    integralTowerHasDerivedCategory.{u, u} l E X
  have hzero : ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj
        (F.obj (op 0))) := by
    intro j hj
    let : HasDerivedCategory.{u + 2} (scalarReductionTarget.{u, u} l E X 0) :=
      scalarReductionTargetDerived.{u, u} l E X 0
    let A := Padic.coefficientExtensionRing l E 1
    let R := proEtaleConstantRing X A
    let V : X.ProEt := ProEt.mk (𝟙 X)
    let T := AlgebraicGeometry.ProEtale.StrictTower.modulePullback
      (ULift.{u + 1, u} A) (𝟙 X)
    let : HasDerivedCategory (proEtaleRingModules X R) := HasDerivedCategory.standard _
    let eT : T ≅ 𝟭 _ := Adjunction.leftAdjointIdIso
      (proEtaleRingModuleAdjunction (𝟙 X) R R
        (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso (ULift.{u + 1, u} A) (𝟙 X)))
      (AlgebraicGeometry.ProEtale.StrictTower.moduleRId (ULift.{u + 1, u} A) X)
    let eD : T.mapDerivedCategory ≅ 𝟭 _ :=
      Functor.mapDerivedCategoryNatIso eT ≪≫ Functor.mapDerivedCategoryIdIso _
    have ht := tor_vanishes X A _ a b (_hTor V) j hj
    have hred : IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) :=
      ht.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
        (eD.app ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)).symm)
    let S := completedIntegralRestrictScalars l E X D hl 0
    let : PreservesFiniteLimits S := integralTowerRestrictionLimits l E X D hl 0
    let : PreservesFiniteColimits S := integralTowerRestrictionColimits l E X D hl 0
    have hs := S.isZero_homologyFunctor_mapDerivedCategory_obj hred
    let efin : (scalarReductionDerivedExtension.{u, u} l E X 0).obj K ≅
        DerivedCategory.Q.obj (integralTowerFiniteComplex l E X D hl 0 P) :=
      (scalarReductionDerivedExtension.{u, u} l E X 0).mapIso e.symm ≪≫
        integralTowerResolutionIso l E X D hl 0 q hq
    let ez : S.mapDerivedCategory.obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) ≅ F.obj (op 0) :=
      S.mapDerivedCategory.mapIso efin ≪≫ S.mapDerivedCategoryFactors.app _
    exact hs.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso ez.symm)
  have htri : ∀ n : ℕ,
      ∃ (i : F.obj (op 0) ⟶ F.obj (op (n + 1)))
        (d : F.obj (op n) ⟶
          (shiftFunctor (completedIntegralDerivedCategory.{0, u, u} l E X D hl)
            (1 : ℤ)).obj (F.obj (op 0))),
        Triangle.mk i (F.map (homOfLE n.le_succ).op) d ∈
          distTriang (completedIntegralDerivedCategory.{0, u, u} l E X D hl) := by
    intro n
    obtain ⟨P', q', hP', hflat, hq', _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheaf l E X D hl) G
    have hr : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheaf l E X D hl) q' := ⟨hq', hP'⟩
    obtain ⟨i, w, hs⟩ := integralReductionFlatFiltration l E X D hl P' hflat n
    let S := ShortComplex.mk i (integralTowerTransition l E X D hl P' n) w
    let T := DerivedCategory.triangleOfSES (S := S) hs
    let e₁ := integralTowerComparison l E X D hl 0 q q' hq hr
    let e₂ := integralTowerComparison l E X D hl (n + 1) q q' hq hr
    let e₃ := integralTowerComparison l E X D hl n q q' hq hr
    let i' := e₁.hom ≫ T.mor₁ ≫ e₂.inv
    let d' := e₃.hom ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁.inv
    refine ⟨i', d', ?_⟩
    apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hs) _
    refine Triangle.isoMk _ T e₁ e₂ e₃ ?_ ?_ ?_
    · simp [i', Category.assoc]
    · change F.map (homOfLE n.le_succ).op ≫ e₃.hom =
        e₂.hom ≫ DerivedCategory.Q.map (integralTowerTransition l E X D hl P' n)
      dsimp only [F, integralReductionTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (integralReductionTowerWellDefined l E X D hl q q' hq hr).2 n
    · simp [d', Category.assoc]
  have hz : ∀ n : ℕ, ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj
        (F.obj (op n))) := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
      obtain ⟨i, d, hd⟩ := htri n
      intro j hj
      exact (DerivedCategory.HomologySequence.exact₂
        (C := integralTowerModules.{u, u} l E X) _ hd j).isZero_X₂
        ((hzero j hj).eq_of_src _ _) ((ih j hj).eq_of_tgt _ _)
  have hb : ∀ n : ℕ, Epi
      ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) b).map
        (F.map (homOfLE n.le_succ).op)) := by
    intro n
    obtain ⟨i, d, hd⟩ := htri n
    exact (DerivedCategory.HomologySequence.exact₃
      (C := integralTowerModules.{u, u} l E X) _ hd b (b + 1)).epi_f
      ((hzero (b + 1) (Or.inr (by omega))).eq_of_tgt _ _)
  let C := integralTowerModules.{u, u} l E X
  let : HasExactLimitsOfShape (Discrete ℕ) C :=
    AlgebraicGeometry.Scheme.ProEt.products_exact.{u, u, 0} X
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) ℕ
  let : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  let : CountableAB4Star C := ⟨fun I _ ↦
    AlgebraicGeometry.Scheme.ProEt.products_exact.{u, u, 0} X
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) I⟩
  obtain ⟨hp, _, hH, _⟩ := derivedCategory_countableProducts_and_towerLimit.{0} C
  let := hp
  let (j : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor.{u + 2} C j) := hH ℕ j
  apply limit_bounds (C := C) F K _ δ hlim a b hz hb
  intro M ht
  exact (AlgebraicGeometry.ProEtale.milnor_epimorphic.{u, u, u + 2} X
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) M ht).1

end WeilConjectures
