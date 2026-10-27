/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.SourceSectionStalkConeData
import Sheaf.Paper.SourceSectionRestrictionModel
import Sheaf.Paper.SourceSectionIdentityModel
import Sheaf.Paper.SourceSectionAutomorphismModel
import Sheaf.Paper.IsomorphismComparisonNatural

/-! # Source sections in both stalk-cone coordinates

Source: Stacks Project, sites.tex, Tags 0F4F and 05V1; blueprint
thm-trf-l-function-euler-product, Step 1, Local powers (b)
(blueprint: lem-trf-source-section-stalk-cone-comparison).

## Main definitions

* `trfSourceSectionConeLift`: the specified strict restriction-insertion representative.
* `trfSourceSectionJ`, `trfSourceSectionC`: the specified derived comparison arrows.
* `TrfSourceSectionData`, `TrfSourceSectionNormalized`: the comparison families and
  their full chain-coordinate and derived normalization.

## Main statements

* `trfSourceSectionStalkConeComparison`: the normalized comparison exists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit trfSourceSectionConeLift integralOperationsRoosMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (D : FiniteFieldDatum.{u})

private theorem sourceSectionC_eq_id
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    (I : IntegralComparisonSystem.{u} l)
    (hI : IntegralComparisonRealizationCoherence l E E (AlgHom.id ℚ_[l] E) I)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k))
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    trfSourceSectionC l E D I g N = 𝟙 _ := by
  unfold trfSourceSectionC
  rw [← (hI.composition E).unitSource g N]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  exact (pointFibreIntegralAmbient D l E).map_id _

private theorem sourceSectionDerivedNaturality
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    (hS : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x))
    (α : D.k ≃+* D.k) (B : TrfSourceSectionData l E D α)
    (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (h : N ⟶ N') :
    (pointFibreIntegralAmbient D l E).map h.hom ≫
        trfSourceSectionJ l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) hS B.ρ N'.obj ≫
        trfSourceSectionC l E D B.I (Spec.map (CommRingCat.ofHom α.toRingHom)) N' =
      trfSourceSectionJ l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) hS B.ρ N.obj ≫
        trfSourceSectionC l E D B.I (Spec.map (CommRingCat.ofHom α.toRingHom)) N ≫
        (trfCompletedPointFibre l E D (Spec.map (CommRingCat.ofHom α.toRingHom))).map h.hom := by
  rw [sourceSectionC_eq_id l E D B.I B.hI, sourceSectionC_eq_id l E D B.I B.hI]
  simp only [Category.id_comp, Category.comp_id]
  obtain ⟨κ, hκ, _, _, _⟩ := inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0}
    l E (Spec.map (CommRingCat.ofHom α.toRingHom)) hS hS
  let η := B.ρ.hom ≫ Functor.whiskerRight κ (pointFibreIntegralAmbient D l E)
  have hn := η.naturality h.hom
  simpa only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map, hκ,
    trfSourceSectionJ, trfCompletedPointFibre, Category.assoc] using hn

/-- Restriction-insertion on source sections agrees in both strict cone coordinates
with reparametrization of the actual completion unit. The comparison data are
existentially provided, never added as hypotheses. All representatives are allowed.

Source: Stacks sites.tex, Tags 0F4F (point functor), 05V1 (points under inverse image);
blueprint thm-trf-l-function-euler-product, Step 1, Local powers (b)
(blueprint: lem-trf-source-section-stalk-cone-comparison).

Proof:
1. Identify restriction-insertion with the restriction-natural transformation of
lem-weil-point-automorphism-restriction-natural. The site arrow g is invertible,
so inverse restriction gives its inverse. Its naturality applies also to P and q.
2. lem-trf-completion-unit-strict-quotient-model identifies the actual unit on P
with z to (0,(bar z_n)). Apply exact point sections and identity germs. The
bounded-quotient-stalk realization acts separately on both coordinates.
3. In the specified chosen-resolution kappa, the inverse of G(q) cancels G(q)
from restriction naturality. The remaining map is exactly trfSourceSectionConeLift.
4. At finite level restrict a along g, insert into inverse image and tensor with 1.
The finite stalk comparison gives [V,id,a|g]=[s,g,a] by the pointed arrow g.
5. lem-trf-quotient-tensor-insertion makes the tuple compatible with transitions.
The signed differential therefore sends (0,A(z)) to (0,A(dz)). The specified
compositor is the realization of this entire finite comparison, by
lem-trf-stalk-compositor-tower-realization, giving the left representative.
6. lem-trf-germ-reparametrization-derived-descent sends [s,id,a] to [s,g,a]
on each product separately. Thus its composite with the identity lift has the
same unshifted coordinate and the same zero shifted coordinate. The biproduct
coordinate projections determine the whole chain map, proving the strict equality.
7. The representative equations hold for every q, hence also after any canonical
change of resolution. All finite maps are natural for chain maps. Invert squares
for quasi-isomorphisms and compose for roofs to obtain naturality for every
derived arrow. The normalization theorem makes kappa invertible on the complete
constructible domain. No detection of arbitrary derived maps by reductions is used. -/
theorem trfSourceSectionStalkConeComparison (_hl : l ≠ D.p)
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    (hS : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x))
    (α : D.k ≃+* D.k) :
    ∃ B : TrfSourceSectionData l E D α, TrfSourceSectionNormalized l E D hS α B := by
  have hc := trfStalkCompositorTowerRealization l E D _hl
  let I := hc.choose
  let S := hc.choose_spec.choose
  have hI := hc.choose_spec.choose_spec.1
  have hC := hc.choose_spec.choose_spec.2.1
  have hQ := hc.choose_spec.choose_spec.2.2
  have hs := trfSourceSectionRestrictionModel l E D _hl α
  let σ := hs.choose
  let ρ := hs.choose_spec.choose
  have hσ := hs.choose_spec.choose_spec.1
  have hρ := hs.choose_spec.choose_spec.2
  have hg := trfGermReparametrizationDerivedDescent l E D _hl (Spec (.of D.k))
  let R := hg.choose
  let e := hg.choose_spec.choose
  have he := hg.choose_spec.choose_spec.choose_spec.1
  have hR := hg.choose_spec.choose_spec.choose_spec.2.1
  have hreal := hg.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1
  have reparamAt (g' : Spec (.of D.k) ⟶ Spec (.of D.k))
      (hg : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ 𝟙 (Spec (.of D.k)) = g') :
      ∃ R₀ : trfQuotientStalkTower l E (𝟙 (Spec (.of D.k))) ≅
          trfQuotientStalkTower l E g',
        ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
          (n : ℕ) (i : ℤ),
          HEq (((R₀.hom.app P).app (op n)).f i).hom.toFun
            ((proEtaleStalkReparam (Padic.coefficientExtensionRing l E (n + 1))
              (𝟙 (Spec (.of D.k))) α).hom.app
                (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
              ).hom.toFun := by
    subst g'
    exact ⟨R (𝟙 (Spec (.of D.k))) α, hR (𝟙 (Spec (.of D.k))) α⟩
  obtain ⟨R₀, hR₀⟩ := reparamAt (Spec.map (CommRingCat.ofHom α.toRingHom))
    (Category.comp_id _)
  have hi := trfSourceSectionIdentityModel l E D _hl I hI S hC hQ e he
  let a₀ := hi.choose
  have ha := hi.choose_spec.1
  have hz := hi.choose_spec.2.1
  have hid := hi.choose_spec.2.2
  let B : TrfSourceSectionData l E D α :=
    { I := I, hI := hI, σ := σ, ρ := ρ, e := e, R := R₀, a₀ := a₀ }
  have hm := trfSourceSectionAutomorphismModel l E D _hl hS α B
    S hC hQ hσ hρ he hR₀ ha hz
  have hfin := hm.1
  have hrep := hm.2.1
  have hstrict := hm.2.2
  refine ⟨B, {
    restriction := hσ
    restrictionDerived := hρ
    germNormalization := he
    finiteGerm := hfin
    reparamGerm := hR₀
    identityCoordinate := ha
    identityShifted := hz
    chainNaturality := ?_
    derivedNaturality := sourceSectionDerivedNaturality l E D hS α B
    realizations := hreal
    representatives := ?_ }⟩
  · intro P P' h
    rw [hstrict P', hstrict P]
    let η := B.a₀ ≫ Functor.whiskerRight B.R.hom integralOperationsRoosFunctor
    have hn := η.naturality h
    simpa only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map,
      integralOperationsRoosFunctor] using hn
  · intro N P q
    obtain ⟨hj, hs⟩ := hrep N P q
    exact ⟨hj, hid N P q, hs, hstrict P.obj⟩

end WeilConjectures
