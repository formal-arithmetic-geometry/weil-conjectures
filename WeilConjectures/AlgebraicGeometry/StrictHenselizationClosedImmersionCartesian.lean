/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedLift
import WeilConjectures.AlgebraicGeometry.StrictLocalClosedChartMap
import WeilConjectures.RingTheory.IndEtaleQuotientTwoBaseInverse
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Strict localization along a closed immersion

Source: Stacks Project, Tag 05WS
(blueprint: lem-trf-closed-immersion-strict-localization-cartesian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

-- Use the small model of the pointed category for the ind-etale presentation.
private theorem presentation_indEtale
    (R K C : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} R K C) :
    RingHom.IndEtaleAcrossUniverses (algebraMap R C) := by
  classical
  let T : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Algebra.Etale R X.left
  obtain ⟨hs, hf⟩ := Algebra.pointedEtale_small_filtered R K
  let : EssentiallySmall.{u} T.FullSubcategory := hs
  let : IsFiltered T.FullSubcategory := hf
  let e := equivSmallModel.{u} T.FullSubcategory
  let : IsFiltered (SmallModel.{u} T.FullSubcategory) := IsFiltered.of_equivalence e
  let c := P.cocone.whisker e.inverse
  have hc : IsColimit c := P.isColimit.whiskerEquivalence e.symm
  let Q : ColimitPresentation (SmallModel.{u} T.FullSubcategory) c.pt :=
    { diag := _
      ι := c.ι
      isColimit := hc }
  have hi : Algebra.IndEtale R C :=
    ⟨_, inferInstance, inferInstance, Q.ofIso P.identification,
      fun j ↦ (e.inverse.obj j).property⟩
  have hr : (algebraMap R C).IndEtale :=
    (RingHom.IndEtale.algebraMap_iff R C).mpr hi
  have hres : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  exact hres.1 _ (ULift.ringEquiv.symm : C ≃+* ULift.{u} C)
    (hres.2 _ (ULift.ringEquiv : ULift.{u} R ≃+* R) hr)

-- The inverse theorem determines the original factor through its kernel and surjectivity.
private theorem chart_desc_bijective
    (A : Type u) [CommRing A] (I p : Ideal A) [p.IsPrime]
    (R C D K Ω : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing C] [CommRing D] [Field K] [Field Ω]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    (α : A →+* C) (β : A ⧸ I →+* D) (ι : K →+* Ω)
    (εC : C →+* Ω) (εD : D →+* Ω) (uCD : C →+* D)
    (d : StrictLocalClosedChartRingData A I p R
      (R ⧸ I.map (algebraMap A R)) C D K Ω
      (Ideal.Quotient.mk (I.map (algebraMap A R))) α β ι εC εD uCD) :
    Function.Bijective d.desc := by
  let J := I.map (algebraMap A R)
  let S := R ⧸ J
  let := d.localS
  let := d.localC
  let := d.localD
  let := d.baseC
  let := d.baseD
  let := d.closureR
  let := d.towerR
  let := d.closureS
  let := d.residueS
  let := d.separableS
  let := d.towerS
  have := d.strictC
  have := d.strictD
  have := d.baseC_local
  have := d.baseD_local
  have := d.map_local
  let : Algebra R D :=
    ((algebraMap S D).comp (Ideal.Quotient.mk J)).toAlgebra
  have : IsScalarTower R S D := IsScalarTower.of_algebraMap_eq' rfl
  let u : C →ₐ[R] D := { uCD with commutes' := fun r ↦ DFunLike.congr_fun d.map_base r }
  have : IsLocalHom u.toRingHom := d.map_local
  have hJ : J ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
  have hbase :
      (d.residueC.toRingHom.comp (IsLocalRing.residue C)).comp (algebraMap R C) =
      (d.residueD.toRingHom.comp (IsLocalRing.residue D)).comp (algebraMap R D) := by
    rw [d.residueC_eq, d.residueD_eq, d.residueC_base]
    change algebraMap R K =
      (d.presentationD.residueMap.comp (algebraMap S D)).comp (Ideal.Quotient.mk J)
    rw [d.residueD_base, d.closureS_eq]
  have hker : RingHom.ker
      ((d.residueC.toRingHom.comp (IsLocalRing.residue C)).comp (algebraMap R C)) =
      IsLocalRing.maximalIdeal R := by
    rw [d.residueC_eq, d.residueC_base,
      IsScalarTower.algebraMap_eq R (IsLocalRing.ResidueField R) K,
      RingHom.ker_comp_of_injective _ (RingHom.injective _),
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hu : (d.residueD.toRingHom.comp (IsLocalRing.residue D)).comp u.toRingHom =
      d.residueC.toRingHom.comp (IsLocalRing.residue C) := by
    rw [d.residueC_eq, d.residueD_eq]
    exact d.map_residue
  obtain ⟨_, _, _, _, _, _, f, hf, _, hbij, v, _, _, _, _, _, _, hsurj, hk⟩ :=
    Algebra.ind_etale_quotient_two_base_inverse R J hJ C D
      (presentation_indEtale R K C d.presentationC)
      (presentation_indEtale S K D d.presentationD) K d.residueC d.residueD hbase hker u hu
  have hI : J.map (algebraMap R C) = I.map α := by
    rw [Ideal.map_map, d.baseC_eq]
  have hk' : RingHom.ker uCD = I.map α := hk.trans hI
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply sub_eq_zero.mp
    rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← hk']
    apply RingHom.mem_ker.mpr
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact (DFunLike.congr_fun d.desc_eq x).symm.trans
      (hxy.trans (DFunLike.congr_fun d.desc_eq y))
  · intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk (I.map α) x, (DFunLike.congr_fun d.desc_eq x).trans hx⟩

-- Transport the quotient pushout along the specified bijective factor.
private theorem quotient_isPullback
    (A C D : CommRingCat.{u}) (I : Ideal A) (α : A →+* C)
    (β : (A ⧸ I) →+* D) (uCD : C →+* D)
    (d : (C ⧸ I.map α) →+* D) (hd : Function.Bijective d)
    (hq : d.comp (Ideal.Quotient.mk (I.map α)) = uCD)
    (hβ : d.comp (Ideal.quotientMap (I.map α) α Ideal.le_comap_map) = β) :
    IsPullback (Spec.map (CommRingCat.ofHom β)) (Spec.map (CommRingCat.ofHom uCD))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom α)) := by
  let e := (RingEquiv.ofBijective d hd).toCommRingCatIso
  apply isPullback_SpecMap_of_isPushout
  refine (CommRingCat.isPushout_quotient (CommRingCat.ofHom α) I).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact CommRingCat.hom_ext hβ
  · exact CommRingCat.hom_ext hq

-- Pasting the affine quotient square recovers the prescribed structural square.
private theorem closed_chart_isPullback
    {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{u}) (I : Ideal A)
    (j : Spec A ⟶ W) [IsOpenImmersion j]
    (k : Spec (.of (A ⧸ I)) ⟶ Z) [IsOpenImmersion k]
    (hsquare : IsPullback k (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) i j)
    (x : Spec (.of Ω) ⟶ Spec (.of (A ⧸ I))) (p : Spec A)
    [Algebra p.asIdeal.ResidueField Ω]
    (hx : x ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map ((Spec.residueFieldIso A p).hom ≫
        CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField Ω)) ≫
          (Spec A).fromSpecResidueField p) :
    IsPullback (strictHenselizationStructuralMap (x ≫ k))
      (strictHenselizationMap i (x ≫ k)) i
      (strictHenselizationStructuralMap ((x ≫ k) ≫ i)) := by
  obtain ⟨α, β, hα, hβ, ⟨d⟩⟩ := strictLocalClosedChartMap i A I j k hsquare x p hx
  let := d.localS
  let := d.baseC
  let := d.baseD
  let := d.chartS
  let := d.quotientAlgebra
  have hd := chart_desc_bijective A I p.asIdeal _ _ _ _ _ α β _ _ _ _ d
  have hbase :
      (Spec.preimage (strictHenselizationMap i (x ≫ k))).hom.comp α =
      β.comp (Ideal.Quotient.mk I) := by
    rw [← d.baseC_eq, ← RingHom.comp_assoc, d.map_base, RingHom.comp_assoc,
      ← d.chartS_eq, ← RingHom.comp_assoc, d.baseD_eq]
  have hdesc : d.desc.toRingHom.comp
      (Ideal.quotientMap (I.map α) α Ideal.le_comap_map) = β := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    exact (DFunLike.congr_fun d.desc_eq (α a)).trans (DFunLike.congr_fun hbase a)
  have hs := quotient_isPullback A _ _ I α β _ d.desc.toRingHom hd d.desc_eq hdesc
  have ht := hs.paste_horiz hsquare
  simpa only [hα, hβ, CommRingCat.ofHom_hom, Spec.map_preimage] using ht

/-- The strict localization of a closed subscheme is the base change of the ambient
strict localization. Source: Stacks Project, Tag 05WS
(blueprint: lem-trf-closed-immersion-strict-localization-cartesian).

Proof: Choose an affine neighbourhood of the geometric image and present the inverse
image as a quotient chart. Apply `lem-trf-strict-local-closed-chart-map` to obtain
compatible strict-local presentations and the factor map from the actual ideal quotient.
By `lem-sc-pointed-etale-small-filtered`, reindexing these presentations by their small
models exhibits the two local-base structure maps as ind-etale. The chart residue
compatibilities give the hypotheses of `lem-trf-ind-etale-quotient-two-base-inverse`;
its surjectivity and kernel conclusions make the specified quotient factor bijective.
The quotient pushout, after applying Spec and this ring isomorphism, is a pullback.
Paste it with the quotient-chart pullback and use the structural chart equations to
identify its legs. Its comparison isomorphism is the stated lift, by its two projections.
-/
theorem isIso_strictHenselizationClosedImmersionCartesian
    {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ Z) :
    IsIso (pullback.lift (f := i)
      (g := strictHenselizationStructuralMap (a ≫ i))
      (strictHenselizationStructuralMap a)
      (strictHenselizationMap i a)
      (by exact (strictHenselizationMap_over i a).symm)) := by
  classical
  obtain ⟨U, hU, haU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := W) (x := (a ≫ i) (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  let A := Γ(W, U)
  let j : Spec A ⟶ W := hU.fromSpec
  have hj : Set.range (a ≫ i) ⊆ Set.range j := by
    rw [show Set.range j = U from hU.range_fromSpec]
    rintro _ ⟨t, rfl⟩
    have ht : t = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst t
    exact haU
  let b := IsOpenImmersion.lift j (a ≫ i) hj
  have hb : b ≫ j = a ≫ i := IsOpenImmersion.lift_fac j (a ≫ i) hj
  let z : Spec (.of Ω) ⟶ pullback i j := pullback.lift a b hb.symm
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff
    (f := pullback.snd i j)).mp inferInstance
  let k : Spec (.of (A ⧸ I)) ⟶ Z := e.inv ≫ pullback.fst i j
  have hk : IsOpenImmersion k := inferInstanceAs
    (IsOpenImmersion (e.inv ≫ pullback.fst i j))
  have hsquare : IsPullback k
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) i j := by
    refine (IsPullback.of_hasPullback i j).of_iso e (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [k]
    · simpa using he
    · simp
    · simp
  let x := z ≫ e.hom
  have ha : x ≫ k = a := by simp [x, k, z]
  let g := x ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let p : Spec A := g (IsLocalRing.closedPoint Ω)
  let ρ := (Spec A).descResidueField (Scheme.stalkClosedPointTo g)
  let : Algebra p.asIdeal.ResidueField Ω :=
    ((Spec.residueFieldIso A p).inv ≫ ρ).hom.toAlgebra
  have hx : g = Spec.map ((Spec.residueFieldIso A p).hom ≫
        CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField Ω)) ≫
      (Spec A).fromSpecResidueField p := by
    have hρ : (Spec.residueFieldIso A p).hom ≫
        CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField Ω) = ρ := by
      change (Spec.residueFieldIso A p).hom ≫
        ((Spec.residueFieldIso A p).inv ≫ ρ) = ρ
      simp
    rw [hρ]
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω (Spec A) g).symm
  have hcart := closed_chart_isPullback i A I j k hsquare x p hx
  rw [ha] at hcart
  have hcomp : pullback.lift (strictHenselizationStructuralMap a)
      (strictHenselizationMap i a) (strictHenselizationMap_over i a).symm =
      hcart.isoPullback.hom := by
    apply pullback.hom_ext <;> simp
  rw [hcomp]
  infer_instance

end AlgebraicGeometry.Scheme
