/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.RefinementComparisonFixedWitness
public import Sheaf.Paper.ProEtaleProperOpenComparison
public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization
import Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility

/-! # Witnessed proper/open mate normalization

Source: blueprint latest, sec-six-functors/sk-prop-sf-pf-coherence,
prop-sf-pf-coherence.proof.md, compactification-independence sentence;
finite-site normalization argument of lem-pur-pf-refinement-compatibility
(blueprint: lem-pur-pf-witnessed-mate-normalization).The
 helpers retain the specified witness and insert only canonical identity and
bounded-below inclusion comparisons. All categories are ordinary and uncompleted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the actual positive-level quotient, including its standard size lift.
Source: finite coefficient convention and coefficientExtensionFinite
(blueprint: lem-pur-pf-witnessed-mate-normalization). -/
instance purityNormalizationCoefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient := by
  let : Finite (Padic.coefficientExtensionRing
      P.coefficients.l P.extension P.level) :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  change Finite (ULift.{u + 1} (Padic.coefficientExtensionRing
    P.coefficients.l P.extension P.level))
  infer_instance

/-- The specified clopen mate for a refinement, with the left identity direct image
identified using the conjugate of the canonical identity pullback comparison.
Quasi-compactness of the opens follows from the compactification factorization.
Source: proper/open projection mate, refinement square (j1,j2,1,v)
(blueprint: lem-pur-pf-witnessed-mate-normalization). -/
def purityRefinementMate (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂) :
    ProperOpenShriek P.Coefficient c₂.i ⟶
      ProperOpenShriek P.Coefficient c₁.i ⋙ ProperOpenPush P.Coefficient v.hom :=
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  Functor.whiskerRight
    ((conjugateIsoEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) (𝟙 X))
      Adjunction.id) (leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X).symm).inv
    (ProperOpenShriek P.Coefficient c₂.i) ≫
    properOpenMate P.Coefficient c₁.i (𝟙 X) v.hom c₂.i
      (v.i_hom.trans (Category.id_comp c₂.i).symm)

/-- The resolution-normalized etale comparison for the refinement square, after
identifying the direct image of the left identity with the identity functor.
Source: proper-open-interchange-coherence, refinement specialization
(blueprint: lem-pur-pf-witnessed-mate-normalization). -/
def purityEtaleRefinementComparison (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :=
  let J₂ := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c₂.i
  J₂.mapDerivedCategoryPlus.map
      ((Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} P.Coefficient) X).inv.app H) ≫
        (Etale.ClopenMateNormalization.normalizedComparison P.Coefficient c₁.i (𝟙 X)
          v.hom c₂.i (v.i_hom.trans (Category.id_comp c₂.i).symm)).hom.app H

/-- The four specified factors e2 inverse, nu*(gamma^e), b_v, and Rv_*(e1).
Source: the explicit finite-site transport formula in this node
(blueprint: lem-pur-pf-witnessed-mate-normalization). -/
def purityRefinementSiteWordPlus (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :=
  let N := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) c₂.Z
  let J₁ := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c₁.i
  let R := (lowerStar (ModuleCat.{u + 1} P.Coefficient) v.hom).rightDerivedFunctorPlus
  (properOpenSiteExtensionIso P.Coefficient c₂.i).inv.app H ≫
    N.mapDerivedCategoryPlus.map (purityEtaleRefinementComparison P v H) ≫
    (fixedComparisonDirectImageMatePlus P.Coefficient v.hom).app (J₁.mapDerivedCategoryPlus.obj H) ≫
    R.map ((properOpenSiteExtensionIso P.Coefficient c₁.i).hom.app H)

/-- Include the four-factor word in the unbounded category, with precisely the
canonical source and target comparisons used by properOpenProEtaleIso.
Source: bounded-below inclusion compatibility in the proper/open construction
(blueprint: lem-pur-pf-witnessed-mate-normalization). -/
def purityRefinementSiteWord (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :=
  let N := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X
  let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c₁.i
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c₂.i
  let R₀ := lowerStar (ModuleCat.{u + 1} P.Coefficient) v.hom
  let R := R₀.rightDerivedFunctor
  J₂.mapDerivedCategory.map (N.mapDerivedCategoryPlusCompatibility.inv.app H) ≫
    J₂.mapDerivedCategoryPlusCompatibility.inv.app (N.mapDerivedCategoryPlus.obj H) ≫
    DerivedCategory.Plus.ι.map (purityRefinementSiteWordPlus P v H) ≫
    R₀.rightDerivedFunctorPlusCompatibility.hom.app
        (J₁.mapDerivedCategoryPlus.obj (N.mapDerivedCategoryPlus.obj H)) ≫
          R.map (J₁.mapDerivedCategoryPlusCompatibility.hom.app
            (N.mapDerivedCategoryPlus.obj H)) ≫
          R.map (J₁.mapDerivedCategory.map (N.mapDerivedCategoryPlusCompatibility.hom.app H))

attribute [local irreducible] properOpenMate properOpenAlpha

private theorem refinementSiteWordPlus_eq (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    let N := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X
    let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c₂.i
    let d := Functor.rightDerivedFunctorPlusNatIso
      (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X) ≪≫
        Functor.rightDerivedFunctorPlusIdIso _
    haveI := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
    haveI := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
    J₂.mapDerivedCategoryPlus.map (d.inv.app (N.mapDerivedCategoryPlus.obj H)) ≫
      (cbcClopenMatePlus P.Coefficient c₁.i c₂.i (𝟙 X) v.hom
        (v.i_hom.trans (Category.id_comp c₂.i).symm)).app
          (N.mapDerivedCategoryPlus.obj H) = purityRefinementSiteWordPlus P v H := by
  have := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  have := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let N := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus
  let J₂ := (openImmersionLowerShriek
    (ModuleCat.{u + 1} P.Coefficient) c₂.i).mapDerivedCategoryPlus
  let E₂ := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} P.Coefficient) c₂.i).mapDerivedCategoryPlus
  let N₂ := (comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) c₂.Z).mapDerivedCategoryPlus
  let d := Functor.rightDerivedFunctorPlusNatIso
    (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X) ≪≫
      Functor.rightDerivedFunctorPlusIdIso _
  let e := Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} P.Coefficient) X
  let b := fixedComparisonDirectImageMatePlus P.Coefficient (𝟙 X)
  let o := properOpenSiteExtensionIso P.Coefficient c₂.i
  have hid : N.map (e.inv.app H) ≫ b.app H = d.inv.app (N.obj H) := by
    apply (cancel_mono (d.hom.app (N.obj H))).1
    rw [Category.assoc]
    have hb := comparisonDirectImagePlus_id P.Coefficient X H
    change b.app H ≫ d.hom.app (N.obj H) = N.map (e.hom.app H) at hb
    rw [hb, ← N.map_comp, e.inv_hom_id_app, N.map_id, d.inv_hom_id_app]
    rfl
  have ht := (finiteClopenMateSiteTransport P.Coefficient c₁.i c₂.i (𝟙 X) v.hom
    (v.i_hom.trans (Category.id_comp c₂.i).symm)).2.2.2.2.2 H
  have htransport := ht.2.1
  rw [ht.1] at htransport
  have ho := o.hom.naturality (e.inv.app H)
  change N₂.map (E₂.map (e.inv.app H)) ≫ o.hom.app _ =
    o.hom.app H ≫ J₂.map (N.map (e.inv.app H)) at ho
  change J₂.map (d.inv.app (N.obj H)) ≫ _ = _
  rw [← hid, J₂.map_comp, Category.assoc]
  apply (cancel_epi (o.hom.app H)).1
  erw [← Category.assoc, ← ho]
  simp only [Category.assoc]
  erw [htransport]
  dsimp only [o, N₂, E₂, e]
  simp only [purityRefinementSiteWordPlus, purityEtaleRefinementComparison,
    Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]

private theorem etaleRefinementComparison_eq (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    purityEtaleRefinementComparison P v H =
      Etale.properOpenComparison P.Coefficient v.hom c₁.i c₂.i v.i_hom H := by
  exact (Etale.properOpenInterchangeCoherence P.Coefficient).choose_spec.choose_spec.2.2.1
    v.hom c₁.i c₂.i v.i_hom H

private theorem refinementSiteWord_eq (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    purityRefinementSiteWord P v H =
      (properOpenProEtaleIso P.Coefficient v.hom c₁.i c₂.i v.i_hom H).hom := by
  have hp : purityRefinementSiteWordPlus P v H =
      (properOpenProEtaleIsoPlus P.Coefficient v.hom c₁.i c₂.i v.i_hom H).hom := by
    simp only [purityRefinementSiteWordPlus, etaleRefinementComparison_eq,
      properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, asIso_hom, fixedComparisonDirectImageMatePlus]
  simp only [purityRefinementSiteWord, hp, properOpenProEtaleIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Iso.app_inv]

private theorem mateTransport
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (γ : F ⟶ G) {K M : C} (a : K ≅ M) :
    F.map a.inv ≫ γ.app K ≫ G.map a.hom = γ.app M := by
  rw [← γ.naturality a.hom, ← Category.assoc, ← F.map_comp,
    a.inv_hom_id, F.map_id, Category.id_comp]

private theorem refinementMate_eq_siteWord (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    (purityRefinementMate P v).app
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          H.obj) = purityRefinementSiteWord P v H := by
  have := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  have := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let N := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X
  let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c₁.i
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c₂.i
  let R := (lowerStar (ModuleCat.{u + 1} P.Coefficient) v.hom).rightDerivedFunctor
  have hc := properOpenRefinementMate_plus_compatibility P.Coefficient
    v.hom c₁.i c₂.i v.i_hom (N.mapDerivedCategoryPlus.obj H)
  have ht := mateTransport (purityRefinementMate P v)
    (N.mapDerivedCategoryPlusCompatibility.app H)
  change J₂.mapDerivedCategory.map _ ≫
    (purityRefinementMate P v).app (N.mapDerivedCategoryPlus.obj H).obj ≫
      R.map (J₁.mapDerivedCategory.map _) = _ at ht
  erw [← ht]
  change J₂.mapDerivedCategory.map _ ≫ (_ ≫ _) ≫ _ = _
  erw [hc]
  rw [refinementSiteWordPlus_eq P v H]
  simp only [purityRefinementSiteWord, J₁, J₂, R, N, Iso.app_inv, Iso.app_hom,
    Category.assoc]

private theorem refinementWitness_eq_mate (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂)
    (M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (w : X.FixedEtaleOriginWitness P.Coefficient M) :
    (refinementProperOpenIsoFixed P.Coefficient v M w).hom =
      (purityRefinementMate P v).app M.obj := by
  have hs := (refinementMate_eq_siteWord P v w.complex).trans
    (refinementSiteWord_eq P v w.complex)
  simp only [refinementProperOpenIsoFixed, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, ← hs]
  exact mateTransport (purityRefinementMate P v) w.iso

/-- Witness transport agrees with the actual clopen-projection mate; its value on
nu*H is the specified four-factor etale/pro-etale word, and the transported arrow
is natural for all arrows between witnessed inputs. Applying the same assertion
to a witnessed bounded-below tensor input requires no extra hypothesis.
Source: blueprint latest prop-sf-pf-coherence.proof.md, compactification independence;
finite-site normalization argument of lem-pur-pf-refinement-compatibility
(blueprint: lem-pur-pf-witnessed-mate-normalization).

Proof:
1. Part (a) of def-sf-refinement-comparison-isomorphism gives the displayed witness
transport. The compactification schemes are Noetherian and the opens quasi-compact.
2. Apply lem-cbc-finite-clopen-mate-site-transport to (j1,j2,1,v). Its clopen
projection is the specified projection onto (j1,1). The counit equation of
lem-weil-pbc-comparison-direct-image-canonical-mate makes b_1 the identity.
This gives the explicit four-factor formula, with the canonical D+ inclusions.
3. The refinement clause of lem-cbc-proper-open-interchange-coherence identifies
gamma^e with alpha^e. Lem-sf-proper-open-comparison-site-normalization identifies
alpha^p with that same transported arrow; cancel e2 to obtain equality at nu*H.
4. Naturality of the proper mate at the retained isomorphism a and cancellation
of J2(a) with its inverse give equality at M. Naturality at any t gives the last
clause, independently of the witnesses. Repeat for any witnessed tensor input;
no tensor-preservation, constructibility, or Tor-amplitude assertion is used. -/
theorem purityWitnessedMateNormalization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂)
    (M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (w : X.FixedEtaleOriginWitness P.Coefficient M) :
    (refinementProperOpenIsoFixed P.Coefficient v M w).hom = (purityRefinementMate P v).app M.obj ∧
    (purityRefinementMate P v).app
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          w.complex.obj) =
      purityRefinementSiteWord P v w.complex ∧
    (∀ (M' : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (w' : X.FixedEtaleOriginWitness P.Coefficient M') (t : M.obj ⟶ M'.obj),
      (refinementProperOpenIsoFixed P.Coefficient v M w).hom ≫
          (ProperOpenPush P.Coefficient v.hom).map
            ((ProperOpenShriek P.Coefficient c₁.i).map t) =
        (ProperOpenShriek P.Coefficient c₂.i).map t ≫
          (refinementProperOpenIsoFixed P.Coefficient v M' w').hom) := by
  refine ⟨refinementWitness_eq_mate P v M w, refinementMate_eq_siteWord P v w.complex, ?_⟩
  intro M' w' t
  rw [refinementWitness_eq_mate P v M w, refinementWitness_eq_mate P v M' w']
  exact ((purityRefinementMate P v).naturality t).symm

end AlgebraicGeometry.ProEtale
