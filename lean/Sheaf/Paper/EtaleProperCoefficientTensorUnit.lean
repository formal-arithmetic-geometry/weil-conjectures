/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleEssentiallySmall
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
import all Sheaf.Paper.PurEtaleScalarMateProjection
import all Sheaf.Paper.EtaleProEtaleScalarMate
import all Sheaf.Paper.FiniteCoefficientDirectImage
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Proper direct image preserves a universal finite-coefficient tensor unit

Source: Stacks Project, Tags 0F0G and 0GL6
(blueprint: lem-fix-etale-proper-coefficient-tensor-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale


private theorem scalar_projection_ambient
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (J : DerivedCategoryModule A Z) :
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).map
        ((scalarMate φ f).app J) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ Z).obj J) =
      (scalarTensorIso φ W).hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) Z).obj J).map
              (scalarCoefficientPullbackIso φ f).hom ≫
            (scalarTensorIso φ Z).inv.app J) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let T := derivedTensor (ModuleCat.{u + 1} A) Z
  let b := (scalarCoefficientPullbackIso φ f).hom
  have ht := (T.map (adj.counit.app J)).naturality b
  dsimp +instances only [Functor.comp_obj, Functor.id_obj] at ht
  have hp : adj.homEquiv _ _
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J)).app
          (scalarCoefficient φ W) ≫
        (T.obj (L(upperStar (ModuleCat.{u + 1} A) f).obj
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J))).map b ≫
        (T.flip.obj (scalarCoefficient φ Z)).map (adj.counit.app J)) =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map ((T.obj J).map b) := by
    simp +instances only [Functor.flip_obj_map, Functor.id_obj]
    rw [ht, ← Category.assoc, adj.homEquiv_naturality_right]
    rfl
  have hm := restricted_mate_tensor adj
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (scalarExtension φ W) (scalarExtension φ Z)
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
    (scalarPullbackIso φ f).hom (scalarRestrictionPullbackIso φ f).hom
    ((derivedTensor (ModuleCat.{u + 1} A) W).flip.obj (scalarCoefficient φ W))
    (T.flip.obj (scalarCoefficient φ Z))
    (scalarTensorIso φ W) (scalarTensorIso φ Z)
    (fun C ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app C).app
        (scalarCoefficient φ W) ≫
      (T.obj (L(upperStar (ModuleCat.{u + 1} A) f).obj C)).map b)
    (scalar_tensor_pullback_square φ f) J
  simp +instances only [Functor.flip_obj_obj, Functor.flip_obj_map, Functor.id_obj,
    Category.assoc] at hp hm
  rw [hp] at hm
  simpa only [scalarMate, scalarRestrictionDirectImageMap, adj, T, b,
    TwoSquare.mk, TwoSquare.natTrans, Functor.map_comp,
    Category.assoc] using hm

private theorem scalar_directImage_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarRestrictionDirectImageMap φ f) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let α := (mateEquiv x z).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)
  have : IsIso α.natTrans := (ProEtale.scalarPullbackReverse_isIso φ f).2
  have h := iterated_mateEquiv_conjugateEquiv x z a b α
  rw [Equiv.apply_symm_apply] at h
  change scalarRestrictionDirectImageMap φ f = _ at h
  rw [h]
  infer_instance

private theorem proper_scalarMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (J : DerivedCategoryModule A X) : IsIso ((scalarMate φ p).app J) := by
  have := scalar_directImage_isIso φ p
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A p
  have h := scalar_projection_ambient φ p J
  have : IsIso ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      ((scalarMate φ p).app J) ≫
      (scalarRestrictionDirectImageMap φ p).app ((scalarExtension φ X).obj J)) := by
    rw [h]
    infer_instance
  have : IsIso ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      ((scalarMate φ p).app J))  := IsIso.of_isIso_comp_right _
        ((scalarRestrictionDirectImageMap φ p).app ((scalarExtension φ X).obj J))
  rw [_root_.DerivedCategory.isIso_iff]
  intro q
  have : IsIso ((Sheaf.restrictScalars Y.smallEtaleTopology φ).map
      ((_root_.DerivedCategory.homologyFunctor _ q).map ((scalarMate φ p).app J))) :=
    (NatIso.isIso_map_iff
      ((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryHomologyFunctorIso q)
      ((scalarMate φ p).app J)).mpr (by
        change IsIso ((_root_.DerivedCategory.homologyFunctor _ q).map
          ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
            ((scalarMate φ p).app J)))
        infer_instance)
  exact isIso_of_reflects_iso _ (Sheaf.restrictScalars Y.smallEtaleTopology φ)

private theorem scalar_unit_directImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A X) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj K) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map ((scalarMate φ f).app K) ≫
      (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj K) =
    R(lowerStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app K) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let α := scalarPullbackIso φ f
  have he := iterated_mateEquiv_conjugateEquiv a b x z α.hom
  have hd := iterated_mateEquiv_conjugateEquiv x z a b
    ((mateEquiv x z).symm (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom))
  rw [Equiv.apply_symm_apply] at hd
  have hα : ((mateEquiv x z).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)).natTrans = α.inv := by
    exact congrArg Iso.inv (scalarPullback_eq φ f)
  have hsq : (mateEquiv x z).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom) =
      TwoSquare.mk _ _ _ _ α.inv := hα
  rw [hsq] at hd
  have h := unit_mateEquiv z x
    (mateEquiv a b (TwoSquare.mk _ _ _ _ α.hom)) K
  dsimp +instances only [TwoSquare.mk, TwoSquare.natTrans] at he h
  rw [he] at h
  change R(lowerStar (ModuleCat.{u + 1} A) f).map (z.unit.app K) ≫
      (conjugateIsoEquiv (a.comp z) (x.comp b) α).hom.app
        ((scalarExtension φ X).obj K) =
    x.unit.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj K) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
        ((scalarMate φ f).app K) at h
  rw [← reassoc_of% h]
  rw [show scalarRestrictionDirectImageMap φ f = _ from hd]
  have hinv : (conjugateEquiv (x.comp b) (a.comp z)
      (TwoSquare.mk _ _ _ _ α.inv)) =
      (conjugateIsoEquiv (a.comp z) (x.comp b) α).inv := rfl
  rw [hinv]
  rw [Iso.hom_inv_id_app]
  dsimp +instances only [scalarExtension, ProEtale.pbcFixedScalarExtension, Functor.comp_obj]
  exact Category.comp_id _

private theorem universal_proper_ambient
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    {K : DerivedCategoryModule A X} {L : DerivedCategoryModule B X}
    (η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj L)
    (hη : Sheaf.IsDerivedBaseChange η) :
    letI := scalar_directImage_isIso φ p
    Sheaf.IsDerivedBaseChange
      (R(lowerStar (ModuleCat.{u + 1} A) p).map η ≫
        (inv (scalarRestrictionDirectImageMap φ p)).app L) := by
  have := scalar_directImage_isIso φ p
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let ay := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let g := (ax.homEquiv K L).symm η
  have hg : ax.unit.app K ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map g = η := by
    change ax.homEquiv K L g = η
    exact Equiv.apply_symm_apply _ _
  have hu (J : DerivedCategoryModule A X) :
      Sheaf.IsDerivedBaseChange (ax.unit.app J) := by
    intro N
    convert (ax.homEquiv J N).bijective using 1
    funext a
    exact (ax.homEquiv_unit J N a).symm
  have : IsIso g := (hu K).isIso hη g hg
  have := proper_scalarMate_isIso φ p K
  let e := asIso ((scalarMate φ p).app K) ≪≫
    R(lowerStar (ModuleCat.{u + 1} B) p).mapIso (asIso g)
  have hunit : Sheaf.IsDerivedBaseChange
      (ay.unit.app (R(lowerStar (ModuleCat.{u + 1} A) p).obj K)) := by
    intro N
    convert (ay.homEquiv (R(lowerStar (ModuleCat.{u + 1} A) p).obj K) N).bijective using 1
    funext a
    exact (ay.homEquiv_unit (R(lowerStar (ModuleCat.{u + 1} A) p).obj K) N a).symm
  have he := hunit.comp_map_iso e
  have heq : R(lowerStar (ModuleCat.{u + 1} A) p).map η ≫
      (inv (scalarRestrictionDirectImageMap φ p)).app L =
      ay.unit.app (R(lowerStar (ModuleCat.{u + 1} A) p).obj K) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map e.hom := by
    dsimp +instances only [scalarExtension, ProEtale.pbcFixedScalarExtension, Functor.comp_obj]
    apply (cancel_mono ((scalarRestrictionDirectImageMap φ p).app L)).1
    simp +instances only [Category.assoc, ← NatTrans.comp_app, IsIso.inv_hom_id,
      NatTrans.id_app, Category.comp_id]
    dsimp +instances only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [Functor.map_comp, Category.assoc]
    have hn := (scalarRestrictionDirectImageMap φ p).naturality g
    dsimp +instances only [Functor.comp_map] at hn
    rw [hn]
    erw [reassoc_of% (scalar_unit_directImage φ p K)]
    rw [← Functor.map_comp, hg]
    exact Category.comp_id _
  rw [heq]
  exact he

attribute [local irreducible] upperStar

private theorem directImage_comparison_plus
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    _root_.DerivedCategory.Plus.ι.map ((rightDerivedLowerStarRestrictScalars φ f).app L) ≫
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) =
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
          ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlusCompatibility.hom.app L) ≫
        (scalarRestrictionDirectImageMap φ f).app L.obj := by
  have h := restriction_plus_mate φ f L
  change (scalarRestrictionDirectImageMap φ f).app L.obj =
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
        ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlusCompatibility.inv.app L) ≫
      _root_.DerivedCategory.Plus.ι.map
        ((rightDerivedLowerStarRestrictScalars φ f).app L) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) at h
  erw [h, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Proper direct image of the universal tensor arrow is again universal, using
exactly the inverse of the canonical restriction/direct-image comparison.

Source: Stacks Project, etale-cohomology.tex, Tag 0F0G,
lemma-projection-formula-proper-mod-n, and more-etale.tex, Tag 0GL6.
(blueprint: lem-fix-etale-proper-coefficient-tensor-unit).

Proof: identify each universal presentation with the chosen left adjoint of exact
restriction of scalars, via the unique isomorphism preserving its unit. Restriction
of that left adjoint is tensoring with the degree-zero constant B-module. For a
proper morphism the projection formula over the finite, hence additively torsion,
ring A is invertible for arbitrary derived inputs and arbitrary tensor factors.
Apply it with this constant B-module. Inverse image identifies its pullback with
the same constant module on X. The scalar/pullback comparison is normalized on
K-flat representatives; its proper counit mate, after restriction of scalars and
the canonical restriction/direct-image comparison, is this projection morphism.
Thus the scalar mate is invertible, since exact scalar restriction detects
isomorphisms. On bounded-below inputs the ambient restriction/direct-image mate
is the stated right-derived comparison: both are characterized by the same
ordinary sectionwise identity and the direct-image resolution unit. The scalar
adjunction unit-mate equation now identifies the displayed arrow with the scalar
unit followed by restriction of this invertible mate. Composing a universal arrow
with an isomorphism preserves its universal property. No flatness or Noetherian
hypothesis enters the argument. The identity morphism and identity coefficient map
reduce to the identity mate; nonflat coefficient quotients use the same derived
tensor and require no termwise flatness of B. -/
theorem properCoefficientTensorUnit_universal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (η : K ⟶ (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L)
    (hη : Sheaf.IsDerivedBaseChange η.hom) :
    Sheaf.IsDerivedBaseChange
      (((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map η ≫
        (asIso (rightDerivedLowerStarRestrictScalars φ p)).inv.app L).hom) := by
  have := scalar_directImage_isIso φ p
  let qA := (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility
  let qB := (lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorPlusCompatibility
  have h := (universal_proper_ambient φ p η.hom hη).of_iso (qA.app K)
  have h' := h.comp_map_iso (qB.app L).symm
  have heq :
      (((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map η ≫
        (asIso (rightDerivedLowerStarRestrictScalars φ p)).inv.app L).hom) =
      ((qA.app K).hom ≫ R(lowerStar (ModuleCat.{u + 1} A) p).map η.hom ≫
        (inv (scalarRestrictionDirectImageMap φ p)).app L.obj) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map (qB.app L).symm.hom := by
    with_unfolding_all
      dsimp only [Functor.comp_obj]
      apply (cancel_mono
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map (qB.hom.app L) ≫
          (scalarRestrictionDirectImageMap φ p).app L.obj)).1
      simp +instances only [Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        IsIso.inv_hom_id_assoc]
      have hcancel := (asIso (scalarRestrictionDirectImageMap φ p)).inv_hom_id_app L.obj
      simp +instances only [asIso_inv, asIso_hom] at hcancel
      have hqid := (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map_id
        ((_root_.DerivedCategory.Plus.ι ⋙
          (lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor).obj L)
      erw [hqid, Category.id_comp, hcancel, Category.comp_id]
      erw [← directImage_comparison_plus φ p L]
      have hinv' : _root_.DerivedCategory.Plus.ι.map
          ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map η ≫
            (asIso (rightDerivedLowerStarRestrictScalars φ p)).inv.app L) ≫
          _root_.DerivedCategory.Plus.ι.map
            ((rightDerivedLowerStarRestrictScalars φ p).app L) =
          _root_.DerivedCategory.Plus.ι.map
            ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map η) := by
        have hi := (asIso (rightDerivedLowerStarRestrictScalars φ p)).inv_hom_id_app L
        change (asIso (rightDerivedLowerStarRestrictScalars φ p)).inv.app L ≫
          (rightDerivedLowerStarRestrictScalars φ p).app L = 𝟙 _ at hi
        rw [← Functor.map_comp, Category.assoc, hi]
        erw [Category.comp_id]
      erw [← Category.assoc, hinv']
      exact qA.hom.naturality η
  rw [heq]
  exact h'

end AlgebraicGeometry.Etale
