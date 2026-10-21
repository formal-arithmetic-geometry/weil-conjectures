/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.DivisibleExtensionDerivedReduction
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Modulus change of normalized derived reduction

Source: blueprint main-20261015, sk-lem-geo-cartier, proof paragraph 4 and its
auxiliary exponent comparison; Stacks Tags 06YY, 0D6D, 07A6 and 0152
(blueprint: lem-geo-cartier-exponent-independence).

The coefficient comparison is constructed by uniqueness of normalized left adjoints.
Its composite-unit characterization is the one of successive derived quotient
normalization. Kernel and quotient presentations and their normalized identifications
are the recorded DivisibleReduction constructions. The extension in a presentation
is auxiliary: for arbitrary B and F one may always take the split extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v r wZ wM wN
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ChangeOfRings
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace SheafOfModules.GeoCartierExponent

open DivisibleReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {m n : ℕ}

/-- The constant coefficient map induced by reduction from Z/m to Z/n.
Source: Cartier exponent comparison, Stacks 0D6D
(blueprint: lem-geo-cartier-exponent-independence). -/
def residueProjection (h : n ∣ m) : residues J m ⟶ residues J n :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom h (ZMod n)).comp ULift.ringEquiv.toRingHom)))

set_option linter.unusedSectionVars false in
/-- The actual constant coefficient projections form the required triangle.
Source: Stacks 0D6D, Cartier exponent comparison
(blueprint: lem-geo-cartier-exponent-independence).
Proof: both ring homomorphisms send each integer to its residue modulo n.
Integer casts determine homomorphisms out of Z. ULift transports that equality,
and functoriality of constant sheafification preserves the composite. -/
theorem projection_comp (h : n ∣ m) :
    projection J m ≫ residueProjection (J := J) h = projection J n := by
  unfold projection residueProjection
  rw [← Functor.map_comp]
  congr 1
  ext x
  rcases x with ⟨x⟩
  change (ZMod.castHom h (ZMod n)) (x : ZMod m) = (x : ZMod n)
  exact map_intCast _ _

/-- Scalar restriction along the modulus map, retaining the underlying sections.
Source: Stacks 03D7 and 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
abbrev residueRestriction (h : n ∣ m) : Residue J n ⥤ Residue J m :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
    (residueProjection (J := J) h))

/-- The identity-on-sections composition comparison for ordinary restriction.
Source: Stacks 03D7 and 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
def restrictionComp (h : n ∣ m) :
    residueRestriction (J := J) h ⋙ restriction J m ≅ restriction J n :=
  NatIso.ofComponents (fun M ↦
    (fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App
          ((projection J m).hom.app U).hom
          ((residueProjection (J := J) h).hom.app U).hom
          ((projection J n).hom.app U).hom
          (congrArg (fun a ↦ (a.hom.app U).hom) (projection_comp (J := J) h)).symm
          (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

variable [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wM} (Residue J m)] [HasDerivedCategory.{wN} (Residue J n)]

/-- The canonical composition comparison for termwise derived restriction.
Source: Stacks 0D6D (blueprint: lem-geo-cartier-exponent-independence). -/
def derivedRestrictionComp (h : n ∣ m) :
    (residueRestriction (J := J) h).mapDerivedCategory ⋙ derivedRestriction m ≅
      derivedRestriction n :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionComp (J := J) h)

/-- The canonical transitivity isomorphism. Normalized adjunctions determine it by
sending the composite scalar-extension unit to the direct scalar-extension unit.
This is exactly the unit characterization of
lem-sfb-successive-derived-quotient-normalization, not a chosen objectwise isomorphism.
Source: Stacks 0D6D and 07A6 (blueprint: lem-geo-cartier-exponent-independence). -/
def transitivity (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h)) :
    Dm.T ⋙ Dmn.T ≅ Dn.T :=
  Adjunction.leftAdjointUniq
    (((sheafScalarDerivedAdjunction (projection J m) Dm).comp
      (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn)).ofNatIsoRight
        (derivedRestrictionComp (J := J) h))
    (sheafScalarDerivedAdjunction (projection J n) Dn)

/-- The canonical K-flat computation on a degree-zero flat module, written as a morphism
so that no flatness proof is hidden in its data. It is invertible for flat M.
Source: Stacks 06YY and 06YQ (blueprint: lem-geo-cartier-exponent-independence). -/
def ordinarySingle (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) :
    Dmn.T.obj ((DerivedCategory.singleFunctor (Residue J m) 0).obj M) ⟶
      (DerivedCategory.singleFunctor (Residue J n) 0).obj
        (changeOfRings (residueProjection (J := J) h) M) :=
  Dmn.ε.app ((CochainComplex.singleFunctor (Residue J m) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex Dmn.E (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctor (Residue J n) 0).map (eqToHom (Dmn.obj_eq M))

-- The candidate torsion map is first constructed over the integer sheaf by a kernel lift.
private def betaIntegral (h : n ∣ m) (Pm : Presentation (J := J) m)
    (Pn : Presentation (J := J) n) (hB : Pm.S.X₁ = Pn.S.X₁) :
    (restriction J m).obj Pm.H ⟶ (restriction J n).obj Pn.H := by
  have := Pn.kummer.mono_f
  apply Pn.kummer.exact.lift (((m / n) • Pm.i) ≫ eqToHom hB)
  have he : eqToHom hB ≫ (n • 𝟙 Pn.S.X₁) =
      (n • 𝟙 Pm.S.X₁) ≫ eqToHom hB := by simp
  rw [Category.assoc, he, ← Category.assoc]
  simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.comp_id]
  rw [smul_smul, Nat.mul_div_cancel' h]
  simpa using congrArg (fun f ↦ f ≫ eqToHom hB) Pm.wi

private theorem betaIntegral_i (h : n ∣ m) (Pm : Presentation (J := J) m)
    (Pn : Presentation (J := J) n) (hB : Pm.S.X₁ = Pn.S.X₁) :
    betaIntegral h Pm Pn hB ≫ Pn.i = ((m / n) • Pm.i) ≫ eqToHom hB := by
  have := Pn.kummer.mono_f
  dsimp only [betaIntegral]
  exact Pn.kummer.exact.lift_f _ _

-- A flat single complex has flat terms: all terms away from zero are zero objects.
private theorem single_kflat {R : Sheaf J CommRingCat.{r}}
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (hM : IsFlatOnSite (R := R) M) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((CochainComplex.singleFunctor _ 0).obj M) := by
  let P := (CochainComplex.singleFunctor _ 0).obj M
  apply isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P 0
  intro i
  by_cases hi : i = 0
  · subst hi
    change IsFlatOnSite (R := R)
      (((HomologicalComplex.single _ (.up ℤ) 0).obj M).X 0)
    rw [HomologicalComplex.single_obj_X_self]
    exact hM
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    let := tensorPreadditive R
    have h := ObjectProperty.flat_of_isZero hz
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R (P.X i)).symm h.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem betaIntegral_boundary (h : n ∣ m) (Pm : Presentation (J := J) m)
    (Pn : Presentation (J := J) n) (hB : Pm.S.X₁ = Pn.S.X₁) :
    Pm.kummer.singleδ ≫
      ((DerivedCategory.singleFunctor (Integral J) 0).map
        (betaIntegral h Pm Pn hB))⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hB) ≫
        Pn.kummer.singleδ := by
  let f : ShortComplex.mk Pm.i (m • 𝟙 Pm.S.X₁) Pm.wi ⟶
      ShortComplex.mk Pn.i (n • 𝟙 Pn.S.X₁) Pn.wi := {
    τ₁ := betaIntegral h Pm Pn hB
    τ₂ := (m / n) • eqToHom hB
    τ₃ := eqToHom hB
    comm₁₂ := by simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul] using
      (betaIntegral_i h Pm Pn hB)
    comm₂₃ := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.comp_id, Category.id_comp, smul_smul]
      rw [Nat.mul_div_cancel' h] }
  exact (ShortComplex.ShortExact.singleTriangle.map Pm.kummer Pn.kummer f).comm₃

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kummer_killed (h : n ∣ m) (Pn : Presentation (J := J) n) :
    m • 𝟙 ((restriction J n).obj Pn.H) = 0 := by
  have := Pn.kummer.mono_f
  have hn : n • 𝟙 ((restriction J n).obj Pn.H) = 0 := by
    apply (cancel_mono Pn.i).1
    simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
      Category.comp_id, zero_comp] using Pn.wi
  obtain ⟨d, rfl⟩ := h
  rw [mul_comm n d, mul_smul, hn, smul_zero]

-- The exact Hom sequence makes this boundary injective on maps to m-torsion:
-- every map from the m-divisible middle object to that target vanishes.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kummer_boundary_injective (Pm : Presentation (J := J) m)
    (N : Integral J) (hN : m • 𝟙 N = 0)
    (f g : (restriction J m).obj Pm.H ⟶ N)
    (hfg : Pm.kummer.singleδ ≫
        ((DerivedCategory.singleFunctor (Integral J) 0).map f)⟦(1 : ℤ)⟧' =
      Pm.kummer.singleδ ≫
        ((DerivedCategory.singleFunctor (Integral J) 0).map g)⟦(1 : ℤ)⟧') : f = g := by
  let F := DerivedCategory.singleFunctor (Integral J) 0
  let S := shiftFunctor (DerivedCategory (Integral J)) (1 : ℤ)
  let T := Pm.kummer.singleTriangle
  have hzero : Pm.kummer.singleδ ≫ (F ⋙ S).map (f - g) = 0 := by
    change Pm.kummer.singleδ ≫ (F.map (f - g))⟦(1 : ℤ)⟧' = 0
    simp only [Functor.map_sub, Preadditive.comp_sub]
    rw [hfg, sub_self]
  obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ T.rotate.rotate
    (rot_of_distTriang _ (rot_of_distTriang _ Pm.kummer.singleTriangle_distinguished))
    ((F ⋙ S).map (f - g)) hzero
  let b' : Pm.S.X₁ ⟶ N := (F ⋙ S).preimage b
  have hb' : b' = 0 := by
    have := Pm.kummer.epi_g
    apply (cancel_epi (m • 𝟙 Pm.S.X₁)).1
    rw [comp_zero]
    calc
      (m • 𝟙 Pm.S.X₁) ≫ b' = b' ≫ (m • 𝟙 N) := by simp
      _ = 0 := by rw [hN, comp_zero]
  have hbzero : b = 0 := by
    rw [← (F ⋙ S).map_preimage b]
    change (F ⋙ S).map b' = 0
    rw [hb', Functor.map_zero]
  rw [hbzero, comp_zero] at hb
  have hz : f - g = 0 := (F ⋙ S).map_injective (hb.trans ((F ⋙ S).map_zero _ _).symm)
  exact sub_eq_zero.mp hz

private theorem ordinarySingle_isIso (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (hM : IsFlatOnSite (R := residues J m) M) :
    IsIso (ordinarySingle h Dmn M) := by
  have := Dmn.computes ((CochainComplex.singleFunctor _ 0).obj M) (single_kflat M hM)
  unfold ordinarySingle
  infer_instance

-- Unfolding the single-complex comparison leaves definitionally equal identity maps.
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinarySingle_unit (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (hM : IsFlatOnSite (R := residues J m) M) :
    (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).unit.app
        ((DerivedCategory.singleFunctor (Residue J m) 0).obj M) ≫
      (residueRestriction (J := J) h).mapDerivedCategory.map (ordinarySingle h Dmn M) ≫
      ((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app
        (changeOfRings (residueProjection (J := J) h) M) =
    (DerivedCategory.singleFunctor (Residue J m) 0).map
      ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app M ≫
        (residueRestriction (J := J) h).map (eqToHom (Dmn.obj_eq M))) := by
  let R := residueRestriction (J := J) h
  let G := DerivedCategory.singleFunctor (Residue J m) 0
  let a := sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn
  let ad := sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn
  let P := (CochainComplex.singleFunctor (Residue J m) 0).obj M
  have hu := (Classical.choose_spec
    (Classical.choose_spec (sheafDerivedScalarAdjunction_exists
      (residueProjection (J := J) h) Dmn)).2) P (single_kflat M hM)
  let e := (HomologicalComplex.singleMapHomologicalComplex Dmn.E (.up ℤ) 0).hom.app M
  let eR := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app
    (Dmn.E.obj M)
  have hc : (R.mapDerivedCategorySingleFunctor 0).hom.app (Dmn.E.obj M) =
      R.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor _ 0).obj (Dmn.E.obj M)) ≫
      DerivedCategory.Q.map eR := by
    simp [Functor.mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, eR]
    erw [Category.id_comp]
  have he := R.mapDerivedCategoryFactors.hom.naturality e
  have hcochain :
      (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫
        (R.mapHomologicalComplex (.up ℤ)).map e ≫ eR =
      (CochainComplex.singleFunctor (Residue J m) 0).map (a.unit.app M) := by
    ext i : 1
    by_cases hi : i = 0
    · subst hi
      change a.unit.app M ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ a.unit.app M ≫ 𝟙 _
      simp
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).eq_of_src _ _
  unfold ordinarySingle
  simp only [Functor.map_comp, Category.assoc]
  erw [(R.mapDerivedCategorySingleFunctor 0).hom.naturality (eqToHom (Dmn.obj_eq M))]
  erw [hc]
  simp only [Category.assoc]
  erw [reassoc_of% he]
  erw [reassoc_of% hu]
  have hfin := congrArg DerivedCategory.Q.map hcochain
  have hfin' := congrArg
    (fun z ↦ z ≫ G.map (R.map (eqToHom (Dmn.obj_eq M)))) hfin
  simp only [Functor.map_comp, Category.assoc] at hfin'
  convert hfin' using 1 <;> rfl



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transitivity_unit (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (X : DerivedCategory (Integral J)) :
    (sheafScalarDerivedAdjunction (projection J m) Dm).unit.app X ≫
      (derivedRestriction m).map
        ((sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).unit.app
          (Dm.T.obj X)) ≫
      (derivedRestrictionComp (J := J) h).hom.app (Dmn.T.obj (Dm.T.obj X)) ≫
      (derivedRestriction n).map ((transitivity h Dm Dn Dmn).hom.app X) =
    (sheafScalarDerivedAdjunction (projection J n) Dn).unit.app X := by
  simpa only [transitivity, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc] using
    Adjunction.unit_leftAdjointUniq_hom_app
      (((sheafScalarDerivedAdjunction (projection J m) Dm).comp
        (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn)).ofNatIsoRight
          (derivedRestrictionComp (J := J) h))
      (sheafScalarDerivedAdjunction (projection J n) Dn) X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private local instance restrictionComp_CommShift (h : n ∣ m) :
    NatTrans.CommShift (derivedRestrictionComp (J := J) h).hom ℤ := by
  dsimp only [derivedRestrictionComp, Iso.trans_hom, Iso.symm_hom]
  infer_instance

-- Transport the defining composite-unit equation across the normalized identifications.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_adjunct (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    {X X' : DerivedCategory (Integral J)} {Y : DerivedCategory (Residue J m)}
    {Z : DerivedCategory (Residue J n)} (im : Dm.T.obj X ≅ Y)
    (t : X ⟶ X') (a : Dn.T.obj X' ⟶ Z) (g : Dmn.T.obj Y ⟶ Z)
    (hg : Dmn.T.map im.inv ≫ (transitivity h Dm Dn Dmn).hom.app X ≫
      Dn.T.map t ≫ a = g) :
    (sheafScalarDerivedAdjunction (projection J m) Dm).unit.app X ≫
      (derivedRestriction m).map im.hom ≫
      (derivedRestriction m).map
        ((sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).unit.app Y ≫
          (residueRestriction (J := J) h).mapDerivedCategory.map g) ≫
      (derivedRestrictionComp (J := J) h).hom.app Z =
    t ≫ (sheafScalarDerivedAdjunction (projection J n) Dn).unit.app X' ≫
      (derivedRestriction n).map a := by
  let A := derivedRestriction (J := J) m
  let B := derivedRestriction (J := J) n
  let R := (residueRestriction (J := J) h).mapDerivedCategory
  let am := sheafScalarDerivedAdjunction (projection J m) Dm
  let an := sheafScalarDerivedAdjunction (projection J n) Dn
  let ar := sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn
  let c := derivedRestrictionComp (J := J) h
  have hg' : Dmn.T.map im.hom ≫ g =
      (transitivity h Dm Dn Dmn).hom.app X ≫ Dn.T.map t ≫ a := by
    rw [← hg]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
    erw [Dmn.T.map_id, Category.id_comp]
  have hu : im.hom ≫ ar.unit.app Y ≫ R.map g =
      ar.unit.app (Dm.T.obj X) ≫ R.map (Dmn.T.map im.hom ≫ g) := by
    have hn : im.hom ≫ ar.unit.app Y =
        ar.unit.app (Dm.T.obj X) ≫ R.map (Dmn.T.map im.hom) := ar.unit.naturality im.hom
    rw [← Category.assoc, hn, R.map_comp, Category.assoc]
  change am.unit.app X ≫ A.map im.hom ≫
    A.map (ar.unit.app Y ≫ R.map g) ≫ c.hom.app Z = _
  rw [← A.map_comp_assoc, hu, hg']
  rw [A.map_comp]
  simp only [Category.assoc]
  erw [c.hom.naturality]
  simp only [Functor.map_comp]
  erw [reassoc_of% transitivity_unit h Dm Dn Dmn X]
  erw [← an.unit.naturality_assoc]
  rfl


-- Unfolding the single-complex comparison leaves definitionally equal identity maps.
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionComp_single (h : n ∣ m) (M : Residue J n) :
    (derivedRestrictionComp (J := J) h).hom.app
        ((DerivedCategory.singleFunctor (Residue J n) 0).obj M) ≫
      ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app M =
    (derivedRestriction m).map
        (((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((restriction J m).mapDerivedCategorySingleFunctor 0).hom.app
        ((residueRestriction (J := J) h).obj M) ≫
      (DerivedCategory.singleFunctor (Integral J) 0).map
        ((restrictionComp (J := J) h).hom.app M) := by
  let R := residueRestriction (J := J) h
  let A := restriction J m
  let B := restriction J n
  let P := (CochainComplex.singleFunctor (Residue J n) 0).obj M
  let er := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M
  let ea := (HomologicalComplex.singleMapHomologicalComplex A (.up ℤ) 0).hom.app (R.obj M)
  let eb := (HomologicalComplex.singleMapHomologicalComplex B (.up ℤ) 0).hom.app M
  have hcochain :
      (NatTrans.mapHomologicalComplex (restrictionComp (J := J) h).hom (.up ℤ)).app P ≫ eb =
      (A.mapHomologicalComplex (.up ℤ)).map er ≫ ea ≫
        (CochainComplex.singleFunctor (Integral J) 0).map
          ((restrictionComp (J := J) h).hom.app M) := by
    ext i : 1
    by_cases hi : i = 0
    · subst hi
      change (restrictionComp (J := J) h).hom.app M ≫ 𝟙 _ =
        A.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ (restrictionComp (J := J) h).hom.app M ≫ 𝟙 _
      simp
    · exact (HomologicalComplex.isZero_single_obj_X
        (.up ℤ) 0 (B.obj M) i hi).eq_of_tgt _ _
  have hc (F : Residue J n ⥤ Integral J) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
      (F.mapDerivedCategorySingleFunctor 0).hom.app M =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) := by
    simp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    erw [Category.id_comp]
  have hcR : (R.mapDerivedCategorySingleFunctor 0).hom.app M =
      R.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map er := by
    simp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ, er]
    erw [Category.id_comp]
  have hcA : (A.mapDerivedCategorySingleFunctor 0).hom.app (R.obj M) =
      A.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor _ 0).obj (R.obj M)) ≫ DerivedCategory.Q.map ea := by
    simp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ, ea]
    erw [Category.id_comp]
  unfold derivedRestrictionComp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso R A).hom.app
    ((DerivedCategory.singleFunctor (Residue J n) 0).obj M))]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  erw [hc B, Functor.mapDerivedCategoryNatIso_fac_assoc]
  erw [hcR, hcA]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (A.mapDerivedCategoryFactors.hom.naturality er)]
  have hcomp := Functor.mapDerivedCategoryCompIso_fac R A P
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ A)) (.up ℤ)).hom.app P =
      𝟙 _ := by ext i : 1; rfl
  rw [hid] at hcomp
  erw [DerivedCategory.Q.map_id, Category.comp_id] at hcomp
  erw [reassoc_of% hcomp]
  have hfin := congrArg DerivedCategory.Q.map hcochain
  simp only [Functor.map_comp] at hfin
  have hz := congrArg (fun z ↦ (R ⋙ A).mapDerivedCategoryFactors.hom.app P ≫ z) hfin
  convert hz using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionComp_shifted_single (h : n ∣ m) (M : Residue J n) :
    (derivedRestrictionComp (J := J) h).hom.app
        (((DerivedCategory.singleFunctor (Residue J n) 0).obj M)⟦(1 : ℤ)⟧) ≫
      ((derivedRestriction n).commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Residue J n) 0).obj M) ≫
      (((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app M)⟦1⟧' =
    (derivedRestriction m).map
        (((residueRestriction (J := J) h).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor (Residue J n) 0).obj M) ≫
          (((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app M)⟦1⟧') ≫
      ((derivedRestriction m).commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Residue J m) 0).obj
          ((residueRestriction (J := J) h).obj M)) ≫
      (((restriction J m).mapDerivedCategorySingleFunctor 0).hom.app
        ((residueRestriction (J := J) h).obj M))⟦1⟧' ≫
      ((DerivedCategory.singleFunctor (Integral J) 0).map
        ((restrictionComp (J := J) h).hom.app M))⟦1⟧' := by
  let A := derivedRestriction (J := J) m
  let R := (residueRestriction (J := J) h).mapDerivedCategory
  let G := DerivedCategory.singleFunctor (Residue J n) 0
  let c := derivedRestrictionComp (J := J) h
  have he := (NatTrans.shift_app_comm c.hom (1 : ℤ) (G.obj M)).symm
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at he
  erw [reassoc_of% he]
  rw [← (shiftFunctor (DerivedCategory (Integral J)) (1 : ℤ)).map_comp]
  rw [restrictionComp_single h M]
  simp only [Functor.map_comp, Category.assoc]
  erw [← A.commShiftIso_hom_naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_adjunct (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (N : Residue J n)
    (f : changeOfRings (residueProjection (J := J) h) M ⟶ N)
    (hM : IsFlatOnSite (R := residues J m) M) :
    (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).unit.app
        ((DerivedCategory.singleFunctor (Residue J m) 0).obj M) ≫
      (residueRestriction (J := J) h).mapDerivedCategory.map
        (ordinarySingle h Dmn M ≫
          (DerivedCategory.singleFunctor (Residue J n) 0).map f) ≫
      ((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app N =
    (DerivedCategory.singleFunctor (Residue J m) 0).map
      ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app M ≫
        (residueRestriction (J := J) h).map (eqToHom (Dmn.obj_eq M) ≫ f)) := by
  let R := residueRestriction (J := J) h
  let G := DerivedCategory.singleFunctor (Residue J m) 0
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [(R.mapDerivedCategorySingleFunctor 0).hom.naturality f]
  erw [reassoc_of% ordinarySingle_unit h Dmn M hM]
  simp only [Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_pure (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (N : Residue J n)
    (f : changeOfRings (residueProjection (J := J) h) M ⟶ N)
    (U : Cᵒᵖ) (b : (residues J n).obj.obj U) (x : M.val.obj U) :
    f.val.app U (SuccessiveDerivedQuotient.pure
        (residueProjection (J := J) h) M U b x) =
      b • @id (N.val.obj U)
        (((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app M ≫
        (residueRestriction (J := J) h).map (eqToHom (Dmn.obj_eq M) ≫ f)).val.app U x) := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J (residues J n)).obj)).unit.app
      (changeOfRingsPresheaf (residueProjection (J := J) h) M)
  have hp : SuccessiveDerivedQuotient.pure (residueProjection (J := J) h) M U b x =
      b • SuccessiveDerivedQuotient.pure (residueProjection (J := J) h) M U 1 x := by
    change η.app U (b ⊗ₜ[(residues J m).obj.obj U,
      ((residueProjection (J := J) h).hom.app U).hom] x) =
      b • η.app U ((1 : (residues J n).obj.obj U) ⊗ₜ[(residues J m).obj.obj U,
        ((residueProjection (J := J) h).hom.app U).hom] x)
    rw [← (η.app U).hom.map_smul]
    congr 1
    change b ⊗ₜ[(residues J m).obj.obj U,
      ((residueProjection (J := J) h).hom.app U).hom] x =
      (b * 1) ⊗ₜ[(residues J m).obj.obj U,
        ((residueProjection (J := J) h).hom.app U).hom] x
    rw [mul_one]
  rw [hp, (f.val.app U).hom.map_smul]
  congr 1
  have hu := (Classical.choose_spec (sheafDerivedScalarAdjunction_exists
    (residueProjection (J := J) h) Dmn)).1 M U x
  change _ = f.val.app U ((eqToHom (Dmn.obj_eq M)).val.app U
    ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app M
      |>.val.app U <| x))
  change _ = f.val.app U ((eqToHom (Dmn.obj_eq M)).val.app U
    ((Classical.choose (sheafDerivedScalarAdjunction_exists
      (residueProjection (J := J) h) Dmn)).unit.app M |>.val.app U <| x))
  rw [hu]
  have he := congrArg (fun z ↦ z.val.app U
      (SuccessiveDerivedQuotient.pure (residueProjection (J := J) h) M U 1 x))
    (eqToHom_trans (Dmn.obj_eq M).symm (Dmn.obj_eq M))
  convert congrArg (f.val.app U) he.symm using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem shifted_single_adjunct (h : n ∣ m)
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (M : Residue J m) (N : Residue J n)
    (f : changeOfRings (residueProjection (J := J) h) M ⟶ N)
    (hM : IsFlatOnSite (R := residues J m) M) :
    (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).unit.app
        (((DerivedCategory.singleFunctor (Residue J m) 0).obj M)⟦(1 : ℤ)⟧) ≫
      (residueRestriction (J := J) h).mapDerivedCategory.map
        ((Dmn.T.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Residue J m) 0).obj M) ≫
        (ordinarySingle h Dmn M ≫
          (DerivedCategory.singleFunctor (Residue J n) 0).map f)⟦(1 : ℤ)⟧') ≫
      ((residueRestriction (J := J) h).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Residue J n) 0).obj N) ≫
      (((residueRestriction (J := J) h).mapDerivedCategorySingleFunctor 0).hom.app N)⟦1⟧' =
    ((DerivedCategory.singleFunctor (Residue J m) 0).map
      ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app M ≫
        (residueRestriction (J := J) h).map (eqToHom (Dmn.obj_eq M) ≫ f)))⟦(1 : ℤ)⟧' := by
  let R := (residueRestriction (J := J) h).mapDerivedCategory
  let G := DerivedCategory.singleFunctor (Residue J m) 0
  let H := DerivedCategory.singleFunctor (Residue J n) 0
  let ad := sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn
  let g := ordinarySingle h Dmn M ≫ H.map f
  have : ad.CommShift ℤ := ad.commShift_of_rightAdjoint ℤ
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [R.commShiftIso_hom_naturality_assoc g (1 : ℤ)]
  have hu : ad.unit.app ((G.obj M)⟦(1 : ℤ)⟧) ≫
      R.map ((Dmn.T.commShiftIso (1 : ℤ)).hom.app (G.obj M)) ≫
      (R.commShiftIso (1 : ℤ)).hom.app (Dmn.T.obj (G.obj M)) =
      (ad.unit.app (G.obj M))⟦(1 : ℤ)⟧' := by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      ad.unit_app_commShiftIso_hom_app ℤ (1 : ℤ) (G.obj M)
  erw [reassoc_of% hu]
  have hs := congrArg ((shiftFunctor (DerivedCategory (Residue J m)) (1 : ℤ)).map)
    (single_adjunct h Dmn M N f hM)
  simp only [Functor.map_comp, Category.assoc] at hs
  simpa only [g, Functor.map_comp, Category.assoc] using hs

-- Pull the actual derived comparison back through the fully faithful single functor.
private def comparisonF [HasTerminal C] (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : Presentation (J := J) m) (Pn : Presentation (J := J) n)
    (hF : Pm.S.X₃ = Pn.S.X₃) (hQ : IsFlatOnSite (R := residues J m) Pm.Q) :
    changeOfRings (residueProjection (J := J) h) Pm.Q ≅ Pn.Q := by
  have := ordinarySingle_isIso h Dmn Pm.Q hQ
  exact (DerivedCategory.singleFunctor (Residue J n) 0).preimageIso
    ((asIso (ordinarySingle h Dmn Pm.Q)).symm ≪≫
      Dmn.T.mapIso (identifications m Dm hm Pm).alphaF.symm ≪≫
      (transitivity h Dm Dn Dmn).app
        ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₃) ≪≫
      Dn.T.mapIso ((DerivedCategory.singleFunctor (Integral J) 0).mapIso (eqToIso hF)) ≪≫
      (identifications n Dn hn Pn).alphaF)

-- The same construction uses the fully faithful shifted single functor for torsion.
private def comparisonH [HasTerminal C] (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : Presentation (J := J) m) (Pn : Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) (hH : IsFlatOnSite (R := residues J m) Pm.H) :
    changeOfRings (residueProjection (J := J) h) Pm.H ≅ Pn.H := by
  have := ordinarySingle_isIso h Dmn Pm.H hH
  let G := DerivedCategory.singleFunctor (Residue J n) 0
  exact (G ⋙ shiftFunctor _ (1 : ℤ)).preimageIso
    ((shiftFunctor _ (1 : ℤ)).mapIso (asIso (ordinarySingle h Dmn Pm.H)).symm ≪≫
      ((Dmn.T.commShiftIso (1 : ℤ)).app
        ((DerivedCategory.singleFunctor (Residue J m) 0).obj Pm.H)).symm ≪≫
      Dmn.T.mapIso (identifications m Dm hm Pm).alphaB.symm ≪≫
      (transitivity h Dm Dn Dmn).app
        ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₁) ≪≫
      Dn.T.mapIso ((DerivedCategory.singleFunctor (Integral J) 0).mapIso (eqToIso hB)) ≪≫
      (identifications n Dn hn Pn).alphaB)

private theorem comparisonF_derived [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : Presentation (J := J) m) (Pn : Presentation (J := J) n)
    (hF : Pm.S.X₃ = Pn.S.X₃) (hQ : IsFlatOnSite (R := residues J m) Pm.Q) :
    Dmn.T.map (identifications m Dm hm Pm).alphaF.inv ≫
      (transitivity h Dm Dn Dmn).hom.app
        ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₃) ≫
      Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hF)) ≫
      (identifications n Dn hn Pn).alphaF.hom =
    ordinarySingle h Dmn Pm.Q ≫
      (DerivedCategory.singleFunctor (Residue J n) 0).map
        (comparisonF hm hn h Dm Dn Dmn Pm Pn hF hQ).hom := by
  have := ordinarySingle_isIso h Dmn Pm.Q hQ
  dsimp [comparisonF, Functor.preimageIso]
  rw [Functor.map_preimage]
  simp

private theorem comparisonH_derived [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : Presentation (J := J) m) (Pn : Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) (hH : IsFlatOnSite (R := residues J m) Pm.H) :
    Dmn.T.map (identifications m Dm hm Pm).alphaB.inv ≫
      (transitivity h Dm Dn Dmn).hom.app
        ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₁) ≫
      Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hB)) ≫
      (identifications n Dn hn Pn).alphaB.hom =
    (Dmn.T.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Residue J m) 0).obj Pm.H) ≫
      (ordinarySingle h Dmn Pm.H)⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor (Residue J n) 0).map
        (comparisonH hm hn h Dm Dn Dmn Pm Pn hB hH).hom)⟦(1 : ℤ)⟧' := by
  have := ordinarySingle_isIso h Dmn Pm.H hH
  let G := DerivedCategory.singleFunctor (Residue J n) 0
  let S := shiftFunctor (DerivedCategory (Residue J n)) (1 : ℤ)
  have he := (G ⋙ S).map_preimage
    ((S.mapIso (asIso (ordinarySingle h Dmn Pm.H)).symm) ≪≫
      ((Dmn.T.commShiftIso (1 : ℤ)).app
        ((DerivedCategory.singleFunctor (Residue J m) 0).obj Pm.H)).symm ≪≫
      Dmn.T.mapIso (identifications m Dm hm Pm).alphaB.symm ≪≫
      (transitivity h Dm Dn Dmn).app
        ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₁) ≪≫
      Dn.T.mapIso ((DerivedCategory.singleFunctor (Integral J) 0).mapIso (eqToIso hB)) ≪≫
      (identifications n Dn hn Pn).alphaB).hom
  change S.map (G.map (comparisonH hm hn h Dm Dn Dmn Pm Pn hB hH).hom) = _ at he
  rw [he]
  simp [S]

-- Normalized units identify the quotient transpose with the original projection.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonF_ordinary [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : Presentation (J := J) m) (Pn : Presentation (J := J) n)
    (hF : Pm.S.X₃ = Pn.S.X₃) (hQ : IsFlatOnSite (R := residues J m) Pm.Q) :
    Pm.p ≫ (restriction J m).map
      ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app Pm.Q ≫
        (residueRestriction (J := J) h).map
          (eqToHom (Dmn.obj_eq Pm.Q) ≫ (comparisonF hm hn h Dm Dn Dmn Pm Pn hF hQ).hom)) ≫
      (restrictionComp (J := J) h).hom.app Pn.Q = eqToHom hF ≫ Pn.p := by
  let F := DerivedCategory.singleFunctor (Integral J) 0
  let G := DerivedCategory.singleFunctor (Residue J m) 0
  let H := DerivedCategory.singleFunctor (Residue J n) 0
  let A := derivedRestriction (J := J) m
  let B := derivedRestriction (J := J) n
  let R := residueRestriction (J := J) h
  let im := identifications m Dm hm Pm
  let jn := identifications n Dn hn Pn
  let f := (comparisonF hm hn h Dm Dn Dmn Pm Pn hF hQ).hom
  let k := (sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app Pm.Q ≫
    R.map (eqToHom (Dmn.obj_eq Pm.Q) ≫ f)
  have ha := comparison_adjunct h Dm Dn Dmn im.alphaF (F.map (eqToHom hF))
    jn.alphaF.hom (ordinarySingle h Dmn Pm.Q ≫ H.map f)
    (comparisonF_derived hm hn h Dm Dn Dmn Pm Pn hF hQ)
  have hx := congrArg (fun z ↦ z ≫
    ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app Pn.Q) ha
  simp only [Category.assoc] at hx
  rw [restrictionComp_single h Pn.Q] at hx
  simp only [Functor.map_comp, Category.assoc] at hx
  have hs := congrArg A.map (single_adjunct h Dmn Pm.Q Pn.Q f hQ)
  change A.map _ = A.map (G.map k) at hs
  conv_lhs at hs => simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hs] at hx
  erw [reassoc_of% ((restriction J m).mapDerivedCategorySingleFunctor 0).hom.naturality k]
    at hx
  erw [reassoc_of% im.quotient_unit, jn.quotient_unit] at hx
  apply F.map_injective
  have hx' := hx
  dsimp only [k, f] at hx'
  simpa only [F, Functor.map_comp, Category.assoc] using hx'

-- Shift compatibility turns the torsion transpose equation into a Kummer boundary square.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonH_boundary [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : Presentation (J := J) m) (Pn : Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) (hH : IsFlatOnSite (R := residues J m) Pm.H) :
    Pm.kummer.singleδ ≫
      ((DerivedCategory.singleFunctor (Integral J) 0).map
        ((restriction J m).map
          ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app Pm.H ≫
            (residueRestriction (J := J) h).map
              (eqToHom (Dmn.obj_eq Pm.H) ≫
                (comparisonH hm hn h Dm Dn Dmn Pm Pn hB hH).hom)) ≫
          (restrictionComp (J := J) h).hom.app Pn.H))⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hB) ≫ Pn.kummer.singleδ := by
  let F := DerivedCategory.singleFunctor (Integral J) 0
  let G := DerivedCategory.singleFunctor (Residue J m) 0
  let H := DerivedCategory.singleFunctor (Residue J n) 0
  let A := derivedRestriction (J := J) m
  let B := derivedRestriction (J := J) n
  let R := residueRestriction (J := J) h
  let im := identifications m Dm hm Pm
  let jn := identifications n Dn hn Pn
  let f := (comparisonH hm hn h Dm Dn Dmn Pm Pn hB hH).hom
  let k := (sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app Pm.H ≫
    R.map (eqToHom (Dmn.obj_eq Pm.H) ≫ f)
  let g := (Dmn.T.commShiftIso (1 : ℤ)).hom.app (G.obj Pm.H) ≫
    (ordinarySingle h Dmn Pm.H ≫ H.map f)⟦(1 : ℤ)⟧'
  have hg : Dmn.T.map im.alphaB.inv ≫
      (transitivity h Dm Dn Dmn).hom.app (F.obj Pm.S.X₁) ≫
      Dn.T.map (F.map (eqToHom hB)) ≫ jn.alphaB.hom = g := by
    simpa only [g, Functor.map_comp, Category.assoc] using
      comparisonH_derived hm hn h Dm Dn Dmn Pm Pn hB hH
  have ha := comparison_adjunct h Dm Dn Dmn im.alphaB
    (F.map (eqToHom hB)) jn.alphaB.hom g hg
  have hx := congrArg (fun z ↦ z ≫
    (B.commShiftIso (1 : ℤ)).hom.app (H.obj Pn.H) ≫
      (((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app Pn.H)⟦1⟧') ha
  simp only [Category.assoc] at hx
  rw [restrictionComp_shifted_single h Pn.H] at hx
  simp only [g, Functor.map_comp, Category.assoc] at hx
  have hs := congrArg A.map (shifted_single_adjunct h Dmn Pm.H Pn.H f hH)
  change A.map _ = A.map ((G.map k)⟦(1 : ℤ)⟧') at hs
  conv_lhs at hs => simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hs] at hx
  erw [reassoc_of% im.kummer_unit, reassoc_of% jn.kummer_unit] at hx
  erw [A.commShiftIso_hom_naturality_assoc (G.map k) (1 : ℤ)] at hx
  have hk := congrArg ((shiftFunctor (DerivedCategory (Integral J)) (1 : ℤ)).map)
    (((restriction J m).mapDerivedCategorySingleFunctor 0).hom.naturality k)
  simp only [Functor.map_comp, Functor.comp_map] at hk
  dsimp only [kappa, A, B, G, H, Functor.id_obj] at hx
  simp only [Category.assoc] at hx
  erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc] at hx
  erw [reassoc_of% hk] at hx
  let S := shiftFunctor (DerivedCategory (Integral J)) (1 : ℤ)
  have cancel_single {X Y : DerivedCategory (Integral J)} (e : X ≅ Y) :
      S.map e.inv ≫ S.map e.hom = 𝟙 _ := by
    erw [← S.map_comp, e.inv_hom_id, S.map_id]
  erw [reassoc_of% cancel_single
    (((restriction J m).mapDerivedCategorySingleFunctor 0).app Pm.H),
    cancel_single (((restriction J n).mapDerivedCategorySingleFunctor 0).app Pn.H),
    Category.comp_id] at hx
  dsimp only [k, f] at hx
  simpa only [F, Functor.map_comp, Category.assoc] using hx

-- Boundary injectivity identifies that transpose with the explicit integer kernel lift.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonH_ordinary [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : Presentation (J := J) m) (Pn : Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) (hH : IsFlatOnSite (R := residues J m) Pm.H) :
    (restriction J m).map
      ((sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app Pm.H ≫
        (residueRestriction (J := J) h).map
          (eqToHom (Dmn.obj_eq Pm.H) ≫ (comparisonH hm hn h Dm Dn Dmn Pm Pn hB hH).hom)) ≫
      (restrictionComp (J := J) h).hom.app Pn.H = betaIntegral h Pm Pn hB := by
  apply kummer_boundary_injective Pm _ (kummer_killed h Pn)
  exact (comparisonH_boundary hm hn h Dm Dn Dmn Pm Pn hB hH).trans
    (betaIntegral_boundary h Pm Pn hB).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Changing modulus identifies the actual transitivity maps with ordinary quotient and
torsion scalar extension. The two presentations encode exactly the kernels/cokernels
and epi/mono hypotheses, with the same underlying B and F identified by hB and hF.
Their auxiliary short exact extensions may both be chosen split.

Source: Cartier proof paragraph 4, auxiliary exponent comparison; Stacks 06YY, 0D6D,
07A6 and 0152 (blueprint: lem-geo-cartier-exponent-independence).
Proof:
1. A flat single complex is K-flat by the independent-universe bounded-flat criterion.
   Thus ordinarySingle computes scalar extension and is invertible on Pm.Q and Pm.H.
2. Conjugate transitivity by the normalized identifications. Full faithfulness of the
   single functor, and of its shift, gives the ordinary isomorphisms eF and eH.
3. The normalized scalar adjunction on a flat single complex identifies its derived
   unit with the ordinary unit. Single-complex restriction comparisons and their shift
   compatibilities transport the composite-unit equation to ordinary sheaf maps.
4. The quotient normalization gives Pm.p followed by the transpose of eF equal to
   Pn.p. The ordinary unit is the sheafified tensor 1 tensor x; linearity gives the
   required formula for every pure tensor.
5. The kernel universal property constructs an integer-linear map beta0 satisfying
   beta0 followed by Pn.i = (m/n) times Pm.i, with hB inserted. The corresponding
   morphism of Kummer sequences has components (beta0, (m/n) times hB, hB).
   Naturality of the short exact triangle gives its boundary square.
6. The shifted composite-unit equation gives the same boundary square for the
   ordinary transpose beta of eH. The exact Hom sequence of Pm.kummer makes this
   square determine beta: any map from the m-divisible middle B to the m-torsion
   target Pn.H is zero. Hence beta = beta0 after restriction to integer coefficients.
   The ordinary unit and linearity give the torsion pure-tensor formula. -/
theorem geoCartier_exponent_independence [HasTerminal C]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (Pm : DivisibleReduction.Presentation (J := J) m)
    (Pn : DivisibleReduction.Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) (hF : Pm.S.X₃ = Pn.S.X₃)
    (hH : IsFlatOnSite (R := residues J m) Pm.H)
    (hQ : IsFlatOnSite (R := residues J m) Pm.Q) :
    ∃ (eF : changeOfRings (residueProjection (J := J) h) Pm.Q ≅ Pn.Q)
      (eH : changeOfRings (residueProjection (J := J) h) Pm.H ≅ Pn.H)
      (beta : Pm.H ⟶ (residueRestriction (J := J) h).obj Pn.H),
      (∀ (U : Cᵒᵖ) (f : Pm.S.X₃.val.obj U) (b : (residues J n).obj.obj U),
        eF.hom.val.app U (SuccessiveDerivedQuotient.pure
          (residueProjection (J := J) h) Pm.Q U b (Pm.p.val.app U f)) =
        b • @id (Pn.Q.val.obj U) (Pn.p.val.app U ((eqToHom hF).val.app U f))) ∧
      (∀ (U : Cᵒᵖ) (x : Pm.H.val.obj U),
        Pn.i.val.app U (beta.val.app U x) =
          (m / n) • (eqToHom hB).val.app U (Pm.i.val.app U x)) ∧
      (∀ (U : Cᵒᵖ) (x : Pm.H.val.obj U) (b : (residues J n).obj.obj U),
        eH.hom.val.app U (SuccessiveDerivedQuotient.pure
          (residueProjection (J := J) h) Pm.H U b x) =
          b • @id (Pn.H.val.obj U) (beta.val.app U x)) ∧
      Dmn.T.map (identifications m Dm hm Pm).alphaF.inv ≫
        (transitivity h Dm Dn Dmn).hom.app
          ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₃) ≫
        Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hF)) ≫
        (identifications n Dn hn Pn).alphaF.hom =
      ordinarySingle h Dmn Pm.Q ≫
        (DerivedCategory.singleFunctor (Residue J n) 0).map eF.hom ∧
      Dmn.T.map (identifications m Dm hm Pm).alphaB.inv ≫
        (transitivity h Dm Dn Dmn).hom.app
          ((DerivedCategory.singleFunctor (Integral J) 0).obj Pm.S.X₁) ≫
        Dn.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hB)) ≫
        (identifications n Dn hn Pn).alphaB.hom =
      (Dmn.T.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Residue J m) 0).obj Pm.H) ≫
        (ordinarySingle h Dmn Pm.H)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor (Residue J n) 0).map eH.hom)⟦(1 : ℤ)⟧' := by
  let eF := comparisonF hm hn h Dm Dn Dmn Pm Pn hF hQ
  let eH := comparisonH hm hn h Dm Dn Dmn Pm Pn hB hH
  let beta := (sheafScalarOrdinaryAdjunction (residueProjection (J := J) h) Dmn).unit.app
    Pm.H ≫ (residueRestriction (J := J) h).map (eqToHom (Dmn.obj_eq Pm.H) ≫ eH.hom)
  refine ⟨eF, eH, beta, ?_, ?_, ?_, ?_, ?_⟩
  · intro U f b
    rw [scalar_pure h Dmn Pm.Q Pn.Q eF.hom U b (Pm.p.val.app U f)]
    congr 1
    have hp := congrArg (fun z ↦ z.val.app U f)
      (comparisonF_ordinary hm hn h Dm Dn Dmn Pm Pn hF hQ)
    change _ = Pn.p.val.app U ((eqToHom hF).val.app U f) at hp
    exact hp
  · intro U x
    have hb := congrArg (fun z ↦ z ≫ Pn.i)
      (comparisonH_ordinary hm hn h Dm Dn Dmn Pm Pn hB hH)
    rw [betaIntegral_i] at hb
    have hp := congrArg (fun z ↦ z.val.app U x) hb
    change Pn.i.val.app U (beta.val.app U x) =
      (eqToHom hB).val.app U (((m / n) • Pm.i).val.app U x) at hp
    calc
      _ = (eqToHom hB).val.app U (((m / n) • Pm.i).val.app U x) := hp
      _ = _ := by
        have he (d : ℕ) : (d • Pm.i).val.app U x = d • Pm.i.val.app U x := by
          induction d with
          | zero => simp only [zero_smul]; rfl
          | succ d hd =>
            simp only [succ_nsmul]
            change (d • Pm.i).val.app U x + Pm.i.val.app U x = _
            rw [hd]
        rw [he]
        exact map_nsmul ((eqToHom hB).val.app U).hom _ _
  · intro U x b
    exact scalar_pure h Dmn Pm.H Pn.H eH.hom U b x
  · exact comparisonF_derived hm hn h Dm Dn Dmn Pm Pn hF hQ
  · exact comparisonH_derived hm hn h Dm Dn Dmn Pm Pn hB hH


end SheafOfModules.GeoCartierExponent
