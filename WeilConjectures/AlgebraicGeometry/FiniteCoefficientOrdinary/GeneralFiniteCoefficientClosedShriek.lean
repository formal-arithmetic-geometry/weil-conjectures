/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedScalarRestrictionPullbackMate
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleComplex
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleModel
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible

/-!
# Exceptional inverse image and arbitrary finite coefficient change

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
`thm-coef-finite-hom.proof.md`, Paragraph 3, and `lem-coef-finite-closed-shriek.proof.md`
in the same directory (blueprint: lem-coef-general-finite-closed-shriek).

The ordinary direct-image coefficient comparison is inverted by the canonical mate
construction.  The resulting natural transformation is the exceptional coefficient
comparison; its counit equation is included in the statement below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.FiniteCoefficientOrdinary

private theorem normalized_transpose
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    {LA : C ⥤ D} {RA : D ⥤ C} (a : LA ⊣ RA)
    {LB : E ⥤ V} {RB : V ⥤ E} (b : LB ⊣ RB)
    {SX : C ⥤ E} {UX : E ⥤ C} (x : SX ⊣ UX)
    {SZ : D ⥤ V} {UZ : V ⥤ D} (z : SZ ⊣ UZ)
    (r : UX ⋙ LA ⟶ LB ⋙ UZ) (N : D)
    (d : SX.obj (RA.obj N) ⟶ RB.obj (SZ.obj N))
    (h : LA.map (x.unit.app (RA.obj N)) ≫ r.app (SX.obj (RA.obj N)) ≫
        UZ.map (LB.map d ≫ b.counit.app (SZ.obj N)) =
      a.counit.app N ≫ z.unit.app N) :
    ((mateEquiv x z).symm (TwoSquare.mk _ _ _ _ r)).app (RA.obj N) ≫
      LB.map d ≫ b.counit.app (SZ.obj N) = SZ.map (a.counit.app N) := by
  apply (z.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu := unit_mateEquiv_symm x z (TwoSquare.mk _ _ _ _ r) (RA.obj N)
  change LA.map (x.unit.app (RA.obj N)) ≫ r.app (SX.obj (RA.obj N)) =
    z.unit.app (LA.obj (RA.obj N)) ≫
      UZ.map (((mateEquiv x z).symm (TwoSquare.mk _ _ _ _ r)).natTrans.app (RA.obj N)) at hu
  rw [Functor.map_comp, ← Category.assoc, ← hu]
  simpa only [Category.assoc, Functor.map_comp, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj] using
    h.trans (z.unit.naturality (a.counit.app N))

private theorem restriction_pullback_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z X : Scheme.{u}} (f : Z ⟶ X) :
    Etale.scalarRestrictionPullbackIso φ f = Etale.leftDerivedUpperStarRestrictScalarsIso φ f := by
  have h : Etale.upperStarRestrictScalarsIsoSheaf φ f =
      Etale.upperStarRestrictScalarsIso φ f := by
    apply Iso.ext
    apply (conjugateEquiv
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
        (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ))
      ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))).injective
    rw [Etale.conjugateEquiv_upperStarRestrictScalarsIso_hom]
    simp only [Etale.upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq,
      Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv]
    exact (conjugateEquiv _ _).apply_symm_apply _
  simp only [Etale.scalarRestrictionPullbackIso,
    Etale.leftDerivedUpperStarRestrictScalarsIso, h]

/-- The closed-immersion coefficient comparison is invertible on every ordinary derived
object.  This is the direct-image input to the exceptional mate construction.
Source: latest Weil blueprint, `lem-coef-finite-closed-shriek.proof.md`, Paragraph 1
(blueprint: lem-coef-general-finite-closed-shriek).

Proof: test the canonical comparison on the complementary open and closed restrictions.
On the closed restriction, its normalized adjunction equation and the invertible scalar
pullback mate identify it with the scalar extension of the invertible closed counit.
On the complementary open, both sides vanish: open pullback kills closed direct image,
and its scalar-pullback mate transports this vanishing through coefficient extension.
Derived open-closed conservativity then proves invertibility on X, without boundedness
or constructibility assumptions on N. This proves the closed projection input used below.
-/
theorem isIso_directImageComparison_of_isClosedImmersion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∀ N : Etale.DerivedCategoryModule A Z,
      IsIso ((directImageMaps.etale φ i).app N) := by
  intro N
  let RA := R(Etale.lowerStar (ModuleCat.{u + 1} A) i)
  let LB := L(Etale.upperStar (ModuleCat.{u + 1} B) i)
  let SX := Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ
  let SZ := Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ
  let a := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i
  let b := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) i
  let x := scalarAdjunction X.smallEtaleTopology φ
  let z := scalarAdjunction Z.smallEtaleTopology φ
  let r := Etale.leftDerivedUpperStarRestrictScalarsIso φ i
  let t := ((mateEquiv x z).symm (TwoSquare.mk _ _ _ _ r.hom)).natTrans
  have ht : IsIso t := by
    dsimp only [t, x, z, scalarAdjunction, r]
    rw [← restriction_pullback_eq]
    exact AlgebraicGeometry.ProEtale.etaleScalarPullbackMate_isIso φ i
  have he := normalized_transpose a b x z r.hom N
    ((directImageMaps.etale φ i).app N) (directImageMaps.etale_counit φ i N)
  have hmap : IsIso ((L(Etale.upperStar (ModuleCat.{u + 1} B) i)).map
      ((directImageMaps.etale φ i).app N)) := by
    have ha : IsIso a.counit := a.counit_isIso_of_R_fully_faithful
    have hb : IsIso b.counit := b.counit_isIso_of_R_fully_faithful
    have hz := z.isLeftAdjoint
    have htotal : IsIso (t.app (RA.obj N) ≫
        LB.map ((directImageMaps.etale φ i).app N) ≫
          b.counit.app (SZ.obj N)) := by
      rw [he]
      infer_instance
    have htail : IsIso (LB.map ((directImageMaps.etale φ i).app N) ≫
        b.counit.app (SZ.obj N)) :=
      IsIso.of_isIso_comp_left (t.app (RA.obj N)) _
    exact IsIso.of_isIso_comp_right _ (b.counit.app _)
  let U : X.Opens := ⟨(Set.range i.base)ᶜ,
    i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hd : Disjoint (Set.range U.ι.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  let zU := scalarAdjunction U.toScheme.smallEtaleTopology φ
  let rU := Etale.leftDerivedUpperStarRestrictScalarsIso φ U.ι
  let tU := ((mateEquiv x zU).symm (TwoSquare.mk _ _ _ _ rU.hom)).natTrans
  have htU : IsIso tU := by
    dsimp only [tU, x, zU, scalarAdjunction, rU]
    rw [← restriction_pullback_eq]
    exact AlgebraicGeometry.ProEtale.etaleScalarPullbackMate_isIso φ U.ι
  have zeroA : IsZero ((L(Etale.upperStar (ModuleCat.{u + 1} A) U.ι)).obj
      ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).obj N)) :=
    (Etale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
      (ModuleCat.{u + 1} A) U.ι i hd N).of_iso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) U.ι).app _)
  have zeroB : IsZero ((L(Etale.upperStar (ModuleCat.{u + 1} B) U.ι)).obj
      ((R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).obj (SZ.obj N))) :=
    (Etale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
      (ModuleCat.{u + 1} B) U.ι i hd (SZ.obj N)).of_iso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) U.ι).app _)
  have zeroSource : IsZero ((L(Etale.upperStar (ModuleCat.{u + 1} B) U.ι)).obj
      (SX.obj (RA.obj N))) := by
    have hzU := zU.isLeftAdjoint
    exact ((Sheaf.fixedCoefficientDerivedScalarExtension U.toScheme.smallEtaleTopology φ).map_isZero
      zeroA).of_iso ((asIso tU).app (RA.obj N)).symm
  apply Etale.isIso_of_isIso_leftDerivedUpperStar_map
    (ModuleCat.{u + 1} B) U.ι i hij ((directImageMaps.etale φ i).app N)
  · exact ⟨⟨0, zeroSource.eq_of_src _ _, zeroB.eq_of_src _ _⟩⟩
  · exact hmap

/-- The canonical natural transformation obtained by taking the mate of the ordinary
closed direct-image coefficient isomorphism.

Source: latest Weil blueprint, `thm-coef-finite-hom.proof.md`, Paragraph 3
(blueprint: lem-coef-general-finite-closed-shriek).
-/
noncomputable def closedShriekCoefficientMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ ⋙
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint := by
  let F_A := R(Etale.lowerStar (ModuleCat.{u + 1} A) i)
  let F_B := R(Etale.lowerStar (ModuleCat.{u + 1} B) i)
  let q : F_A ⋙ Sheaf.fixedCoefficientDerivedScalarExtension
      X.smallEtaleTopology φ ≅
      Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ ⋙ F_B :=
    NatIso.ofComponents
      (fun N ↦ letI := isIso_directImageComparison_of_isClosedImmersion φ i N
        asIso ((directImageMaps.etale φ i).app N)) (by
        intro N N' f
        exact (directImageMaps.etale φ i).naturality f)
  exact (mateEquiv (Adjunction.ofIsLeftAdjoint F_A)
    (Adjunction.ofIsLeftAdjoint F_B)
    (TwoSquare.mk _ _ _ _ q.inv)).natTrans

/-- The right-adjoint conjugate of the derived direct-image compositor for two closed
immersions.  This is the canonical `e` used to identify the composite exceptional
right adjoint with the iterated exceptional right adjoint.
Source: latest Weil blueprint, `thm-coef-finite-hom.proof.md`, Paragraph 3
(blueprint: lem-coef-general-finite-closed-shriek).
-/
noncomputable def closedShriekCompositionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (i' : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i] :
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) (i' ≫ i))).rightAdjoint ≅
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i')).rightAdjoint :=
  by
    let aComp := Adjunction.ofIsLeftAdjoint
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) (i' ≫ i)))
    let aIter := (Adjunction.ofIsLeftAdjoint
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) i'))).comp
      (Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
    exact conjugateIsoEquiv aComp aIter
      (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} A) i' i)

/-- Data expressing the general finite coefficient closed-shriek comparison.
The comparison is a natural transformation, so its naturality in the complex is part
of the field `comparison`; the mate equation uniquely specifies every component.
The two coherence fields state equalities of exceptional coefficient mates at M. Composition
uses the conjugate of the direct-image compositor, while successive coefficient change uses
the scalar-composition isomorphisms on the source and target of the exceptional functor.
Source: latest Weil blueprint, `lem-coef-finite-closed-shriek.proof.md`, Paragraphs 1--2
(blueprint: lem-coef-general-finite-closed-shriek).
-/
structure ClosedShriekComparisonData
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule A X) where
  comparison :
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ ⋙
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint
  comparison_isIso : IsIso (comparison.app M)
  comparison_is_canonical : comparison = closedShriekCoefficientMate φ i
  comparison_counit :
    (directImageMaps.etale φ i).app
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).map (comparison.app M) ≫
      (Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).counit.app
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) =
    (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).map
      ((Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M)
  comparison_unique :
    ∀ b :
        (Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ).obj
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ⟶
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
            ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M),
      (directImageMaps.etale φ i).app
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).map b ≫
        (Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).counit.app
          ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) =
      (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).map
        ((Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M) →
      b = comparison.app M
  comparison_composition :
    ∀ {W : Scheme.{u}} (i' : W ⟶ Z) [IsClosedImmersion i'],
      (closedShriekCoefficientMate φ (i' ≫ i)).app M =
        (Sheaf.fixedCoefficientDerivedScalarExtension (W.smallEtaleTopology) φ).map
            ((closedShriekCompositionIso A i' i).hom.app M) ≫
          (closedShriekCoefficientMate φ i').app
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i')).rightAdjoint.map
            ((closedShriekCoefficientMate φ i).app M) ≫
          (closedShriekCompositionIso B i' i).inv.app
            ((Sheaf.fixedCoefficientDerivedScalarExtension
              (X.smallEtaleTopology) φ).obj M)
  comparison_successive_change :
    ∀ {C : Type (u + 1)} [CommRing C] [Finite C]
      (ψ : B →+* C),
      (closedShriekCoefficientMate (ψ.comp φ) i).app M =
        (scalarComposition (Z.smallEtaleTopology) φ ψ).inv.app
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
          (Sheaf.fixedCoefficientDerivedScalarExtension
            (Z.smallEtaleTopology) ψ).map ((closedShriekCoefficientMate φ i).app M) ≫
          (closedShriekCoefficientMate ψ i).app
            ((Sheaf.fixedCoefficientDerivedScalarExtension
              (X.smallEtaleTopology) φ).obj M) ≫
          (R(Etale.lowerStar (ModuleCat.{u + 1} C) i)).rightAdjoint.map
            ((scalarComposition (X.smallEtaleTopology) φ ψ).hom.app M)
  source_finite :
    Etale.DerivedCategory.boundedConstructibleFiniteTor A Z
      ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M)
  scalar_finite :
    Etale.DerivedCategory.boundedConstructibleFiniteTor B Z
      ((Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ).obj
        ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M))
  target_finite :
    Etale.DerivedCategory.boundedConstructibleFiniteTor B Z
      ((R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M))

/-- The canonical mate satisfies its counit equation.
Source: latest Weil blueprint, closed-shriek proof Paragraph 1
(blueprint: lem-coef-general-finite-closed-shriek).
Proof: apply the counit formula for mates and cancel the inverse comparison. -/
private theorem closedShriekCoefficientMate_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule A X) :
    (directImageMaps.etale φ i).app
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).map ((closedShriekCoefficientMate φ i).app M) ≫
      (Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).counit.app
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) =
    (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).map
      ((Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M) := by
  unfold closedShriekCoefficientMate
  rw [mateEquiv_counit]
  dsimp only [NatIso.ofComponents_inv_app, asIso_inv]
  let := isIso_directImageComparison_of_isClosedImmersion φ i
    ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M)
  simp

/-- The exceptional counit equation uniquely determines the mate.
Source: latest Weil blueprint, closed-shriek proof Paragraph 2
(blueprint: lem-coef-general-finite-closed-shriek).
Proof: cancel the closed direct-image isomorphism, then use injectivity of the
inverse exceptional Hom equivalence. -/
private theorem closedShriekCoefficientMate_unique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule A X) :
    ∀ b :
        (Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ).obj
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ⟶
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
            ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M),
      (directImageMaps.etale φ i).app
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).map b ≫
        (Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).counit.app
          ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) =
      (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).map
        ((Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M) →
      b = (closedShriekCoefficientMate φ i).app M := by
  intro b hb
  let := isIso_directImageComparison_of_isClosedImmersion φ i
    ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M)
  apply ((Adjunction.ofIsLeftAdjoint
    (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).homEquiv _ _).symm.injective
  apply (cancel_epi ((directImageMaps.etale φ i).app
    ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M))).1
  exact hb.trans (closedShriekCoefficientMate_counit φ i M).symm

/-- Closed exceptional inverse image preserves the ordinary finite-Tor constructible domain.
Source: latest Weil blueprint, closed-shriek proof Paragraph 2, with the pre-duality
localization correction (blueprint: lem-coef-general-finite-closed-shriek).

Proof: a power of ell kills A and is invertible on X. Apply the existing ordinary
exceptional preservation theorem, whose closed case uses the complementary open
localization triangle. Transport along uniqueness of the right adjoint. -/
private theorem closedShriek_preserves_boundedConstructibleFiniteTor
    (k : Type u) [Field k] (ell : ℕ) [Fact ell.Prime]
    (hell : IsUnit (ell : k)) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell ^ r : A) = 0)
    {Z X : Scheme.{u}} (aX : X ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule A X)
    (hM : Etale.DerivedCategory.boundedConstructibleFiniteTor A X M) :
    Etale.DerivedCategory.boundedConstructibleFiniteTor A Z
      ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) := by
  obtain ⟨r, hr⟩ := hA
  let : HasInvertibleExponent A (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) := by
    refine ⟨ell ^ r, pow_pos (Fact.out : Nat.Prime ell).pos r, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hr
    · have hu : IsUnit ((ell ^ r : ℕ) : k) := by
        simpa only [Nat.cast_pow] using hell.pow r
      simpa only [map_natCast] using
        hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let : HasInvertibleExponent A X := .of_hom aX
  let : HasCompactification i := (Compactification.ofIsProper i).hasCompactification
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨a₀, b₀, hab⟩ :=
    (Etale.DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor M).2 hM
  have h := (Etale.DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor
    _).1 ⟨a₀, b₀ + 2 * d + 1,
      Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion
        A aX i d hd a₀ b₀ hab⟩
  let a := (Etale.rightDerivedUpperShriekAdjunction A i).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) i)
  let e := a.rightAdjointUniq
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z).prop_of_iso
    (e.app M) h

/-- An invertible open coefficient comparison makes the canonical closed exceptional mate
invertible. Source: latest Weil blueprint, closed-shriek proof Paragraph 1
(blueprint: lem-coef-general-finite-closed-shriek).

Proof: scalar extension of the closed-support triangle and the B-support triangle
have the same middle object. Their open terms are isomorphic because the scalar-extended
open term is in the image of open direct image; its open unit is invertible. Complete
this to a triangle morphism. The isomorphism on first terms is uniquely identified,
by the exceptional counit, with closed direct image of the specified mate. Reflect
invertibility through fully faithful closed direct image. -/
private theorem closedShriekCoefficientMate_isIso_of_open
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : Etale.DerivedCategoryModule A X)
    [IsIso ((directImageMaps.etale φ j).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M))] :
    IsIso ((closedShriekCoefficientMate φ i).app M) := by
  let F := Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ
  let scalarAdj := scalarAdjunction X.smallEtaleTopology φ
  let : F.CommShift ℤ := scalarAdj.leftAdjointCommShift ℤ
  have : scalarAdj.CommShift ℤ := scalarAdj.commShift_of_rightAdjoint ℤ
  have : F.IsTriangulated := scalarAdj.isTriangulated_leftAdjoint
  let JA := D(Etale.upperStar (ModuleCat.{u + 1} A) j)
  let JB := D(Etale.upperStar (ModuleCat.{u + 1} B) j)
  let GA := R(Etale.lowerStar (ModuleCat.{u + 1} A) j)
  let GB := R(Etale.lowerStar (ModuleCat.{u + 1} B) j)
  let adjA := Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let adjB := Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j
  let η := adjA.unit.app M
  let E := F.obj (GA.obj (JA.obj M))
  have hE : GB.essImage E :=
    ⟨(Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).obj (JA.obj M),
      ⟨(asIso ((directImageMaps.etale φ j).app (JA.obj M))).symm⟩⟩
  have hηE : IsIso (adjB.unit.app E) := adjB.isIso_unit_app_iff_mem_essImage.2 hE
  have hJA : IsIso (JA.map η) := by
    have : IsIso adjA.counit := adjA.counit_isIso_of_R_fully_faithful
    change IsIso (JA.map (adjA.unit.app M))
    rw [← IsIso.inv_eq_of_inv_hom_id (adjA.left_triangle_components M)]
    infer_instance
  let o := Etale.openScalarRestriction φ j
  have hn := o.hom.naturality η
  change (Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).map
        (JA.map η) ≫ o.hom.app (GA.obj (JA.obj M)) =
      o.hom.app M ≫ JB.map (F.map η) at hn
  have hJB : IsIso (JB.map (F.map η)) := by
    have heq : JB.map (F.map η) = o.inv.app M ≫
        (Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).map
          (JA.map η) ≫ o.hom.app (GA.obj (JA.obj M)) := by
      rw [hn]
      simp
    rw [heq]
    infer_instance
  let e : GB.obj (JB.obj (F.obj M)) ⟶ E :=
    GB.map (JB.map (F.map η)) ≫ inv (adjB.unit.app E)
  have he : IsIso e := by dsimp [e]; infer_instance
  have he_unit : adjB.unit.app (F.obj M) ≫ e = F.map η := by
    dsimp only [e]
    have hnat : F.map η ≫ adjB.unit.app E =
        adjB.unit.app (F.obj M) ≫ GB.map (JB.map (F.map η)) :=
      (adjB.unit_naturality (F.map η)).symm
    rw [← Category.assoc, ← hnat]
    simp
  obtain ⟨δA, hδA⟩ := Etale.exists_etale_closedSupportTriangle A i j hij
  obtain ⟨δB, hδB⟩ := Etale.exists_etale_closedSupportTriangle B i j hij
  let a := Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))
  let b := Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))
  let TA := F.mapTriangle.obj (Pretriangulated.Triangle.mk (a.counit.app M) η (δA.app M))
  let TB := Pretriangulated.Triangle.mk
    (b.counit.app (F.obj M)) (adjB.unit.app (F.obj M)) (δB.app (F.obj M))
  have hTA : TA ∈ distTriang _ := F.map_distinguished _ (hδA M)
  have hTB : TB ∈ distTriang _ := hδB (F.obj M)
  have hsq : TA.mor₂ ≫ inv e = (𝟙 (F.obj M)) ≫ TB.mor₂ := by
    change F.map η ≫ inv e = (𝟙 _) ≫ adjB.unit.app (F.obj M)
    rw [← he_unit]
    simp
  obtain ⟨t, ht, ht₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    TA TB hTA hTB (𝟙 _) (inv e) hsq
  let τ : TA ⟶ TB :=
    { hom₁ := t, hom₂ := 𝟙 _, hom₃ := inv e,
      comm₁ := ht, comm₂ := hsq, comm₃ := ht₃ }
  have htIso : IsIso t := Pretriangulated.isIso₁_of_isIso₂₃ τ hTA hTB
    (by dsimp [τ]; infer_instance) (by dsimp [τ]; infer_instance)
  let c := (directImageMaps.etale φ i).app
    ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M)
  let G := R(Etale.lowerStar (ModuleCat.{u + 1} B) i)
  let m := (closedShriekCoefficientMate φ i).app M
  have : IsIso c := isIso_directImageComparison_of_isClosedImmersion φ i _
  have htε : t ≫ b.counit.app (F.obj M) = F.map (a.counit.app M) := by
    change F.map (a.counit.app M) ≫ 𝟙 _ = t ≫ b.counit.app (F.obj M) at ht
    simpa only [Category.comp_id] using ht.symm
  have hpre : G.preimage (inv c ≫ t) = m := by
    apply (b.homEquiv _ _).symm.injective
    change G.map (G.preimage (inv c ≫ t)) ≫ _ = G.map m ≫ _
    rw [Functor.map_preimage, Category.assoc, htε]
    have hc := closedShriekCoefficientMate_counit φ i M
    change c ≫ G.map m ≫ _ = _ at hc
    rw [← hc]
    simp
    rfl
  have ht_eq : inv c ≫ t = G.map m := by
    simpa only [Functor.map_preimage] using congrArg G.map hpre
  have : IsIso (G.map m) := by rw [← ht_eq]; infer_instance
  exact isIso_of_reflects_iso m G

/-- Finite derived scalar extension preserves the ordinary finite-Tor constructible domain.
Source: latest Weil blueprint, closed-shriek proof Paragraph 2
(blueprint: lem-coef-general-finite-closed-shriek).

Proof: choose a bounded flat constructible model. Extension preserves flatness and
constructibility termwise. Its derived counit is invertible on this K-flat complex.
Uniqueness of left adjoints identifies this derived extension with the fixed extension. -/
private theorem scalar_preserves_boundedConstructibleFiniteTor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) [IsNoetherian X]
    (M : Etale.DerivedCategoryModule A X)
    (hM : Etale.DerivedCategory.boundedConstructibleFiniteTor A X M) :
    Etale.DerivedCategory.boundedConstructibleFiniteTor B X
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) := by
  let := φ.toAlgebra
  let E := Sheaf.extendScalars X.smallEtaleTopology φ
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  have : E.PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ f hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (Sheaf.extendScalarsCompRestrictScalarsIso X.smallEtaleTopology A B) f hP hQ
  let a := (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).derivedAdjunction.ofNatIsoRight
    U.rightDerivedFunctorIsoMapDerivedCategory
  let e := (scalarAdjunction X.smallEtaleTopology φ).leftAdjointUniq a
  obtain ⟨P, ⟨l, h, hz, hflat⟩, hc, ⟨eM⟩⟩ :=
    Etale.DerivedCategory.exists_flatConstructibleModel_of_boundedConstructibleFiniteTor M hM
  have : P.IsStrictlyGE l := (CochainComplex.isStrictlyGE_iff P l).2 fun n hn ↦ hz n (.inl hn)
  have : P.IsStrictlyLE h := (CochainComplex.isStrictlyLE_iff P h).2 fun n hn ↦ hz n (.inr hn)
  have hP := CochainComplex.kFlat_of_isStrictlyLE_of_flat P h hflat
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let Q := (E.mapHomologicalComplex (.up ℤ)).obj P
  have : CochainComplex.IsStrictlyGE Q l :=
    (CochainComplex.isStrictlyGE_iff Q l).2 fun n hn ↦ E.map_isZero (hz n (.inl hn))
  have : CochainComplex.IsStrictlyLE Q h :=
    (CochainComplex.isStrictlyLE_iff Q h).2 fun n hn ↦ E.map_isZero (hz n (.inr hn))
  have hQ : Etale.DerivedCategory.boundedConstructibleFiniteTor B X
      (_root_.DerivedCategory.Q.obj Q) := by
    apply Etale.DerivedCategory.constructibleFiniteTor_Q_obj Q l h
    · intro n
      exact ProEtale.flat_etaleSheafExtendScalars_obj (φ := φ) (hflat n)
    · intro n
      have := hc n
      exact inferInstanceAs (Scheme.IsConstructibleSheaf
        ((ProEtale.etaleSheafExtendScalars φ X).obj (P.X n)))
  let eq : (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M ≅
      _root_.DerivedCategory.Q.obj Q :=
    e.app M ≪≫ (L(E)).mapIso (eM ≪≫ ((_root_.DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
      asIso (E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P))
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) X).prop_of_iso
    eq.symm hQ

private theorem closedMate_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIso (directImageMaps.etale φ i)] :
    closedShriekCoefficientMate φ i =
      (mateEquiv (Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
        (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)))
        (inv (directImageMaps.etale φ i))).natTrans := by
  unfold closedShriekCoefficientMate
  apply congrArg (fun α ↦ (mateEquiv
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))) α).natTrans)
  ext N
  simp only [NatIso.ofComponents_inv_app, asIso_inv, NatIso.isIso_inv_app]

/-- The exceptional coefficient mate respects composition of closed immersions.
Source: latest Weil blueprint, closed-shriek proof Paragraph 2
(blueprint: lem-coef-general-finite-closed-shriek).
Proof: paste the inverse direct-image squares. Their given compositor coherence,
and the canonical conjugate compositor, identify the mate of this pasted square. -/
private theorem closedShriekCoefficientMate_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {W Z X : Scheme.{u}} (i' : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule A X) :
    (closedShriekCoefficientMate φ (i' ≫ i)).app M =
      (Sheaf.fixedCoefficientDerivedScalarExtension W.smallEtaleTopology φ).map
          ((closedShriekCompositionIso A i' i).hom.app M) ≫
        (closedShriekCoefficientMate φ i').app
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i')).rightAdjoint.map
          ((closedShriekCoefficientMate φ i).app M) ≫
        (closedShriekCompositionIso B i' i).inv.app
          ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) := by
  have : ∀ N, IsIso ((directImageMaps.etale φ i').app N) :=
    isIso_directImageComparison_of_isClosedImmersion φ i'
  have : ∀ N, IsIso ((directImageMaps.etale φ i).app N) :=
    isIso_directImageComparison_of_isClosedImmersion φ i
  have : ∀ N, IsIso ((directImageMaps.etale φ (i' ≫ i)).app N) :=
    isIso_directImageComparison_of_isClosedImmersion φ (i' ≫ i)
  have := NatIso.isIso_of_isIso_app (directImageMaps.etale φ i')
  have := NatIso.isIso_of_isIso_app (directImageMaps.etale φ i)
  have := NatIso.isIso_of_isIso_app (directImageMaps.etale φ (i' ≫ i))
  have hEx : Adjunction.ExchangeCompCompatible
      (directImageMaps.etale φ i') (directImageMaps.etale φ i)
      (directImageMaps.etale φ (i' ≫ i))
      (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} A) i' i).symm
      (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} B) i' i).symm := by
    constructor
    intro N
    rw [etale_composition]
    simp
  have h := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i')))
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) (i' ≫ i))))
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i')))
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)))
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) (i' ≫ i))))
    (directImageMaps.etale φ i') (directImageMaps.etale φ i)
    (directImageMaps.etale φ (i' ≫ i))
    (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} A) i' i).symm
    (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} B) i' i).symm hEx M
  simp only [rightAdjointUniq_ofNatIsoLeft_hom, Iso.symm_inv] at h
  change (Sheaf.fixedCoefficientDerivedScalarExtension W.smallEtaleTopology φ).map
      ((closedShriekCompositionIso A i' i).hom.app M) ≫
      (mateEquiv _ _ (inv (directImageMaps.etale φ i'))).app _ ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) i')).rightAdjoint.map
        ((mateEquiv _ _ (inv (directImageMaps.etale φ i))).app M) =
    (mateEquiv _ _ (inv (directImageMaps.etale φ (i' ≫ i)))).app M ≫
      (closedShriekCompositionIso B i' i).hom.app _ at h
  rw [closedMate_eq, closedMate_eq, closedMate_eq]
  have h' := congrArg (fun f ↦ f ≫ (closedShriekCompositionIso B i' i).inv.app
    ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M)) h
  simp only [Category.assoc, Iso.hom_inv_id_app] at h'
  erw [Category.comp_id] at h'
  exact h'.symm

private theorem mate_scalar_iso
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    {LA : C ⥤ D} {RA : D ⥤ C} (a : LA ⊣ RA)
    {LB : E ⥤ V} {RB : V ⥤ E} (b : LB ⊣ RB)
    {S S' : C ⥤ E} {T T' : D ⥤ V}
    (q : TwoSquare S LA LB T) (q' : TwoSquare S' LA LB T')
    (eS : S ≅ S') (eT : T ≅ T')
    (hq : ∀ N, q'.app N = LB.map (eS.inv.app N) ≫ q.app N ≫ eT.hom.app (LA.obj N))
    (M : D) :
    (mateEquiv a b q').app M = eS.inv.app (RA.obj M) ≫
      (mateEquiv a b q).app M ≫ RB.map (eT.hom.app M) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [b.counit_naturality]
  rw [mateEquiv_counit]
  erw [reassoc_of% (mateEquiv_counit a b q M)]
  rw [hq]
  simp only [Category.assoc]
  rw [← eT.hom.naturality]
  rfl

/-- The exceptional coefficient mate respects successive homomorphisms of finite rings.
Source: latest Weil blueprint, closed-shriek proof Paragraph 2
(blueprint: lem-coef-general-finite-closed-shriek).
Proof: invert the ordinary coefficient-composition equation. The vertical pasting
identity for mates identifies its mate with the two exceptional mates, and naturality
transports the scalar-composition isomorphisms on the source and target. -/
private theorem closedShriekCoefficientMate_successive_change
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule A X) :
    (closedShriekCoefficientMate (ψ.comp φ) i).app M =
      (scalarComposition Z.smallEtaleTopology φ ψ).inv.app
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
        (Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology ψ).map
          ((closedShriekCoefficientMate φ i).app M) ≫
        (closedShriekCoefficientMate ψ i).app
          ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) ≫
        (R(Etale.lowerStar (ModuleCat.{u + 1} C) i)).rightAdjoint.map
          ((scalarComposition X.smallEtaleTopology φ ψ).hom.app M) := by
  have : ∀ N, IsIso ((directImageMaps.etale φ i).app N) :=
    isIso_directImageComparison_of_isClosedImmersion φ i
  have : ∀ N, IsIso ((directImageMaps.etale ψ i).app N) :=
    isIso_directImageComparison_of_isClosedImmersion ψ i
  have : ∀ N, IsIso ((directImageMaps.etale (ψ.comp φ) i).app N) :=
    isIso_directImageComparison_of_isClosedImmersion (ψ.comp φ) i
  have := NatIso.isIso_of_isIso_app (directImageMaps.etale φ i)
  have := NatIso.isIso_of_isIso_app (directImageMaps.etale ψ i)
  have := NatIso.isIso_of_isIso_app (directImageMaps.etale (ψ.comp φ) i)
  let a := Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))
  let b := Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))
  let c := Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} C) i))
  let q := TwoSquare.mk _ _ _ _ (inv (directImageMaps.etale φ i))
  let r := TwoSquare.mk _ _ _ _ (inv (directImageMaps.etale ψ i))
  let t := TwoSquare.mk _ _ _ _ (inv (directImageMaps.etale (ψ.comp φ) i))
  have ht : ∀ N, t.app N =
      (R(Etale.lowerStar (ModuleCat.{u + 1} C) i)).map
        ((scalarComposition Z.smallEtaleTopology φ ψ).inv.app N) ≫
      (q.hComp r).app N ≫
        (scalarComposition X.smallEtaleTopology φ ψ).hom.app
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).obj N) := by
    intro N
    apply (cancel_epi ((directImageMaps.etale (ψ.comp φ) i).app N)).1
    dsimp only [t, TwoSquare.mk]
    simp only [NatIso.isIso_inv_app]
    rw [IsIso.hom_inv_id]
    conv_rhs => lhs; rw [etale_coefficientComposition]
    simp [q, r, TwoSquare.hComp, Category.assoc, -Functor.map_comp]
  have h := mate_scalar_iso a c (q.hComp r) t
    (scalarComposition Z.smallEtaleTopology φ ψ)
    (scalarComposition X.smallEtaleTopology φ ψ) ht M
  have hp := congrArg (fun s ↦ s.app M) (mateEquiv_vcomp a b c q r)
  rw [closedMate_eq, closedMate_eq, closedMate_eq]
  rw [h, hp]
  simp only [TwoSquare.vComp_app, Category.assoc]
  rfl

private lemma explicit_boundedConstructible
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T)
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K) :
    Etale.DerivedCategory.isBoundedConstructible A T K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    (hc q), min a b, max a b, (min_le_left a b).trans (le_max_left a b), ?_⟩
  intro q hq
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q
      (hq.trans_le (min_le_left a b))
  · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q
      ((le_max_right a b).trans_lt hq)

/-- Exceptional inverse image commutes with arbitrary finite coefficient change on the
small étale site.

Source: latest Weil blueprint, `thm-coef-finite-hom.proof.md`, Paragraph 3 and
`lem-coef-finite-closed-shriek.proof.md`, Paragraphs 1--2
(blueprint: lem-coef-general-finite-closed-shriek).

Proof: tensor the closed-support triangle by the coefficient ring and compare its open
term by the ordinary finite direct-image theorem.  The first component is the scalar
extension of the exceptional counit after the canonical direct-image comparison; the
closed direct image is fully faithful, so its adjoint transpose is invertible.  The
finite-Tor constructibility assertion is obtained from pre-duality closed-support
constructibility and the ordinary/pro-etale finite-Tor comparison (Wei Yang #1441, item 29).
Naturality, the counit equation, composition of closed immersions,
and successive coefficient changes follow by uniqueness of adjoint mates and the
canonical direct-image compositor.
-/
theorem generalFiniteCoefficientClosedShriek
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (_hell : IsUnit (ell : k))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (_hA : ∃ r : ℕ, (ell ^ r : A) = 0)
    (_hB : ∃ r : ℕ, (ell ^ r : B) = 0)
    {Z X : Scheme.{u}}
    (aZ : Z ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    (aX : X ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (_hi : i ≫ aX = aZ)
    (M : Etale.DerivedCategoryModule A X)
    (_hM : Etale.DerivedCategory.boundedConstructibleFiniteTor A X M) :
    Nonempty (ClosedShriekComparisonData φ i M) := by
  classical
  have : IsLocallyNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of k)).2
      (inferInstanceAs (IsNoetherianRing k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  have : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian aZ }
  let U : X.Opens := ⟨(Set.range i.base)ᶜ,
    i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace U :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := inferInstance
  have : LocallyOfFiniteType (U.ι ≫ aX) := inferInstance
  have : QuasiCompact (U.ι ≫ aX) := inferInstance
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hOpen : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) U
      ((Etale.upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory.obj M) := by
    exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) U).prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) U.ι).app M)
      (Etale.constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} A) U.ι _hM)
  obtain ⟨a, b, hab, ht⟩ :=
    Etale.DerivedCategory.exists_le_hasTorAmplitudeIn_of_finiteTorAmplitude hOpen.2
  have hDirect := (generalFiniteCoefficientDirectImage k hk ell _hell A B φ _hA _hB
    (U.ι ≫ aX) aX U.ι rfl _ (explicit_boundedConstructible A U _ hOpen.1)
    ⟨a, b, hab, ht⟩).1
  have hIso := closedShriekCoefficientMate_isIso_of_open φ i U.ι hij M
  have hN := closedShriek_preserves_boundedConstructibleFiniteTor
    k ell _hell A _hA aX i M _hM
  have hScalar := scalar_preserves_boundedConstructibleFiniteTor φ Z _ hN
  refine ⟨{
    comparison := closedShriekCoefficientMate φ i
    comparison_isIso := hIso
    comparison_is_canonical := rfl
    comparison_counit := closedShriekCoefficientMate_counit φ i M
    comparison_unique := closedShriekCoefficientMate_unique φ i M
    comparison_composition := fun i' ↦ closedShriekCoefficientMate_composition φ i' i M
    comparison_successive_change := fun ψ ↦
      closedShriekCoefficientMate_successive_change φ ψ i M
    source_finite := hN
    scalar_finite := hScalar
    target_finite := ?_ }⟩
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) Z).prop_of_iso
    (asIso ((closedShriekCoefficientMate φ i).app M)) hScalar

end AlgebraicGeometry.FiniteCoefficientOrdinary
