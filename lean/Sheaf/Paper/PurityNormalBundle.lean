/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension
public import Sheaf.Paper.PurityVectorBundleZeroSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.RingTheory.RegularSequenceConormal
import Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Sheaves.Stalks
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore

/-!
# The normal cone, its augmentation section, and the regular normal bundle

Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, order 1894;
Stacks Project, Divisors, Tags 0636, 0637, 063M; Algebra, Tag 00LN
(blueprint: def-pur-normal-bundle).

The cone is the relative spectrum of the conormal algebra for the given immersion.
The regular case uses the conormal module itself, with no globally chosen frame.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.PurityNormalBundle

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The conormal algebra as an object of the quasi-coherent algebra category.
Source: Stacks Tags 0630, 0636 (blueprint: def-pur-normal-bundle). -/
def algebraObject : ObjectProperty.FullSubcategory
    (fun A : Z.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
  ⟨(ConormalGradedAlgebra.presentation i).algebra,
    (ConormalGradedAlgebra.presentation i).quasicoherent⟩

/-- The normal cone as an affine scheme over `Z`, defined by relative spectrum of
`G = direct sum I^n/I^(n+1)`, with the actual conormal algebra of this immersion.
Source: Stacks Tag 0636 (blueprint: def-pur-normal-bundle). -/
def over : ObjectProperty.FullSubcategory (fun Y : Over Z ↦ IsAffineHom Y.hom) :=
  ((VectorBundleZeroSection.antiEquivalence Z).inverse.obj (algebraObject i)).unop

/-- The normal cone `Spec_Z G` for the given closed immersion.
Source: Stacks Tag 0636 (blueprint: def-pur-normal-bundle). -/
def normalCone : Scheme.{u} := (over i).obj.left

/-- The affine projection from the normal cone to the closed subscheme.
Source: Stacks Tag 0636 (blueprint: def-pur-normal-bundle). -/
def projection : normalCone i ⟶ Z := (over i).obj.hom

/-- The degree-zero augmentation, transported along the structure map to the algebra of
the identity scheme over `Z`. Both arrows are specified algebra morphisms.
Source: Stacks Tags 0636, 01LX (blueprint: def-pur-normal-bundle). -/
def augmentationToBase : (algebraObject i).obj ⟶
    ((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj :=
  ConormalGradedAlgebra.augmentation i ≫
    Under.homMk (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj.hom) (Category.id_comp _)

/-- The canonical section induced contravariantly by projection to degree zero.
Source: Stacks Tags 0636, 01LX (blueprint: def-pur-normal-bundle). -/
def zeroSection : Z ⟶ normalCone i :=
  ((VectorBundleZeroSection.antiEquivalence Z).functor.preimage
    (((VectorBundleZeroSection.antiEquivalence Z).counitIso.app (algebraObject i)).hom ≫
      ObjectProperty.homMk (augmentationToBase i))).unop.hom.left

/-- The augmentation gives a closed section even when the immersion is not regular.
Source: Stacks Tags 0636, 01LX, 01QO (blueprint: def-pur-normal-bundle).

Proof: the nonnegative grading makes projection to degree zero multiplicative. Its
composite with the structural inclusion is the identity. Under the relative-spectrum
anti-equivalence (`lem-weil-pbc-affine-morphism-relative-spec`), this is precisely the
section identity. On an affine open W of Z, the section is Spec of G(W) → O_Z(W), a
surjection since it fixes constants. The affine-cover closed-immersion criterion
(`lem-weil-pbc-closed-immersion-affine-cover-criterion`) proves closedness. This is Steps
1--2 of the node, using `lem-pur-conormal-graded-algebra` for the augmentation. -/
theorem zeroSection_spec :
    zeroSection i ≫ projection i = 𝟙 Z ∧ IsClosedImmersion (zeroSection i) := by
  have hs : zeroSection i ≫ projection i = 𝟙 Z := by
    exact Over.w
      (((VectorBundleZeroSection.antiEquivalence Z).functor.preimage
        (((VectorBundleZeroSection.antiEquivalence Z).counitIso.app (algebraObject i)).hom ≫
          ObjectProperty.homMk (augmentationToBase i))).unop.hom)
  have : IsAffineHom (projection i) := (over i).property
  have : IsClosedImmersion (zeroSection i ≫ projection i) := hs ▸ inferInstance
  exact ⟨hs, IsClosedImmersion.of_comp (zeroSection i) (projection i)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentation_inclusion :
    (ConormalGradedAlgebra.presentation i).inclusion 1 ≫
      (commAlgebraSheafModuleFunctor Z.sheaf).map
        (ConormalGradedAlgebra.augmentation i) = 0 := by
  let adj := (Scheme.Modules.exists_tensorPullbackAdjunction i).choose
  apply (adj.homEquiv (ConormalGradedAlgebra.power i 1) _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext a
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (ConormalGradedAlgebra.augmentation i).right.hom.app (op (i ⁻¹ᵁ U.unop))
    (ConormalGradedAlgebra.homogeneousClass i _ _ 1 U.unop a) = 0
  have h := (ConormalGradedAlgebra.presentation i).augmentation.exists.choose_spec
  simpa only [ConormalGradedAlgebra.augmentation, Nat.one_ne_zero, ↓reduceIte] using
    h 1 U.unop a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentation_comparison :
    ConormalGradedAlgebra.symmetricComparison i ≫ augmentationToBase i =
      VectorBundleZeroSection.augmentationToBase Z (ConormalGradedAlgebra.piece i 1) := by
  apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core Z
    (ConormalGradedAlgebra.piece i 1)
    (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj) 0)
  · intro U a
    change (augmentationToBase i).right.hom.app (op U)
      ((ConormalGradedAlgebra.symmetricComparison i).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion _).val.app (op U) a)) = 0
    dsimp only [ConormalGradedAlgebra.symmetricComparison]
    rw [(ConormalGradedAlgebra.presentation i).symmetricComparison.exists.choose_spec]
    have h := congrArg (fun q ↦ q.val.app (op U) a) (augmentation_inclusion i)
    change (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj.hom.hom.app (op U))
        ((ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
          (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a)) = 0
    change (ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
      (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a) = 0 at h
    rw [h, map_zero]
  · exact (exists_quasiCoherentSymmetricAlgebra_core Z
      (ConormalGradedAlgebra.piece i 1)
      (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
        (op (VectorBundleZeroSection.baseObject Z))).obj) 0).exists.choose_spec

private theorem preimage_affine_neighborhood (z : Z) (V : Z.Opens) (hz : z ∈ V) :
    ∃ U : X.affineOpens, i z ∈ U.1 ∧ i ⁻¹ᵁ U.1 ≤ V := by
  obtain ⟨W, hW, he⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hzW : i z ∈ W := by
    change z ∈ i ⁻¹' W
    rw [he]
    exact hz
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⟨W, hW⟩ : X.Opens)) hzW
  refine ⟨⟨U, hU⟩, hzU, ?_⟩
  intro y hy
  change y ∈ (V : Set Z)
  rw [← he]
  exact hUW hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_conormal_representative (z : Z)
    (x : (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
      (ConormalGradedAlgebra.piece i 1)) :
    ∃ (U : X.Opens) (hz : i z ∈ U) (a : (ConormalGradedAlgebra.power i 1).val.obj (op U)),
      TopCat.Presheaf.germ (ConormalGradedAlgebra.piece i 1).presheaf
        (i ⁻¹ᵁ U) z hz (ConormalGradedAlgebra.representative i 1 U a) = x := by
  obtain ⟨V, hzV, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (ConormalGradedAlgebra.piece i 1).presheaf x
  obtain ⟨U, hzU, hUV⟩ := preimage_affine_neighborhood i z V hzV
  let a' := (ConormalGradedAlgebra.piece i 1).presheaf.map (homOfLE hUV).op a
  obtain ⟨e, he⟩ := (Scheme.Modules.affine_conormal_sections i).2 U
    Γ(X, U.1) (RingEquiv.refl _) (i.ker.ideal U) (by simp [Scheme.Hom.ker_apply])
  obtain ⟨b, hb⟩ := e.surjective a'
  obtain ⟨r, hr⟩ := (i.ker.ideal U).toCotangent_surjective b
  have hrange : (r : Γ(X, U.1)) ∈ Set.range (i.ker.toModulesι.app U.1) := by
    rw [i.ker.range_toModulesι_app U]
    exact r.property
  obtain ⟨t, ht⟩ := hrange
  refine ⟨U.1, hzU, t, ?_⟩
  have hrep : ConormalGradedAlgebra.representative i 1 U.1 t = a' := by
    exact (he r t ht).symm.trans ((congrArg e hr).trans hb)
  rw [hrep]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormal_basis (c : ℕ) (z : Z)
    (hr : ∃ f : Fin c → X.presheaf.stalk (i z),
      RingTheory.Sequence.IsRegular (X.presheaf.stalk (i z)) (List.ofFn f) ∧
        Ideal.span (Set.range f) = RingHom.ker (i.stalkMap z).hom) :
    Nonempty (Module.Basis (Fin c) (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        (ConormalGradedAlgebra.piece i 1))) := by
  obtain ⟨f, hf, he⟩ := hr
  obtain ⟨_, ⟨b, hb⟩, _⟩ :=
    RingTheory.Sequence.regularSequence_conormal_free _ c f hf
  rw [he] at b
  obtain ⟨e, hs, _⟩ := (ConormalGradedAlgebra.presentation i).conormalStalk z
  let q := ConormalGradedAlgebra.quotientStalk i z
  let : Module (Z.presheaf.stalk z) (RingHom.ker (i.stalkMap z).hom).Cotangent :=
    Module.compHom _ q.symm.toRingHom
  let eL : ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
      (ConormalGradedAlgebra.piece i 1)) ≃ₗ[Z.presheaf.stalk z]
      (RingHom.ker (i.stalkMap z).hom).Cotangent :=
    { e with
      map_smul' := by
        intro r x
        change e (r • x) = q.symm r • e x
        rw [← q.apply_symm_apply r]
        simpa only [q, RingEquiv.symm_apply_apply] using hs (q.symm r) x }
  exact ⟨(b.mapCoeffs q (fun x y ↦ by
      change q.symm (q x) • y = x • y
      rw [q.symm_apply_apply])).map eL.symm⟩

private theorem regular_conormal_basis
    {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hf : RingTheory.Sequence.IsRegular R (List.ofFn f)) (J : Ideal R)
    (he : Ideal.span (Set.range f) = J) :
    ∃ b : Module.Basis (Fin c) (R ⧸ J) J.Cotangent,
      ∀ j, b j = J.toCotangent ⟨f j, he ▸ Ideal.subset_span (Set.mem_range_self j)⟩ := by
  subst J
  exact (RingTheory.Sequence.regularSequence_conormal_free R c f hf).2.1

private theorem regular_polynomial_bijective
    {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hf : RingTheory.Sequence.IsRegular R (List.ofFn f)) (J : Ideal R)
    (he : Ideal.span (Set.range f) = J) :
    Function.Bijective (MvPolynomial.aeval (R := R ⧸ J) fun j ↦
      DirectSum.of (Ideal.associatedGradedPiece J) 1
        (Submodule.Quotient.mk (⟨f j, by
          rw [pow_one]
          exact he ▸ Ideal.subset_span (Set.mem_range_self j)⟩ : (J ^ 1 : Ideal R)))) := by
  subst J
  exact (Ideal.regularSequence_gradedPolynomial f hf).1

private theorem symmetric_bijective_of_polynomial
    {S T D C : Type u} [CommRing S] [CommRing T] [CommRing D]
    [AddCommGroup C] [Module S C] [Algebra T D] {κ : Type*}
    (b : Module.Basis κ S C) (q : S ≃+* T)
    (θ : MvPolynomial κ T →ₐ[T] D) (hθ : Function.Bijective θ)
    (t : SymmetricAlgebra S C →+* D)
    (hC : ∀ r, t (algebraMap S (SymmetricAlgebra S C) r) = algebraMap T D (q r))
    (hX : ∀ j, t (SymmetricAlgebra.ι S C (b j)) = θ (MvPolynomial.X j)) :
    Function.Bijective t := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  let d := MvPolynomial.mapEquiv κ q
  have hcomp : t.comp e.symm.toRingHom = θ.toRingHom.comp d.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change t (e.symm (MvPolynomial.C r)) = θ (MvPolynomial.map q (MvPolynomial.C r))
      rw [MvPolynomial.map_C]
      change t (e.symm (algebraMap S (MvPolynomial κ S) r)) =
        θ (algebraMap T (MvPolynomial κ T) (q r))
      rw [e.symm.commutes, θ.commutes]
      exact hC r
    · intro j
      change t (e.symm (MvPolynomial.X j)) = θ (d (MvPolynomial.X j))
      have hd : d (MvPolynomial.X j) = MvPolynomial.X j := MvPolynomial.map_X _ j
      rw [hd]
      exact (congrArg t (SymmetricAlgebra.equivMvPolynomial_symm_X b j)).trans (hX j)
  have heq : t = (θ.toRingHom.comp d.toRingHom).comp e.toRingHom := by
    apply RingHom.ext
    intro x
    have h : t (e.symm (e x)) = θ (d (e x)) := DFunLike.congr_fun hcomp (e x)
    rw [e.symm_apply_apply] at h
    exact h
  rw [heq]
  exact (hθ.comp d.bijective).comp e.bijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_stalk_iso (c : ℕ) (z : Z)
    (hr : ∃ f : Fin c → X.presheaf.stalk (i z),
      RingTheory.Sequence.IsRegular (X.presheaf.stalk (i z)) (List.ofFn f) ∧
        Ideal.span (Set.range f) = RingHom.ker (i.stalkMap z).hom) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (ConormalGradedAlgebra.symmetricComparison i).right.hom) := by
  let R := X.presheaf.stalk (i z)
  let S := Z.presheaf.stalk z
  let J := RingHom.ker (i.stalkMap z).hom
  let C := (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
    (ConormalGradedAlgebra.piece i 1)
  let q := ConormalGradedAlgebra.quotientStalk i z
  obtain ⟨eg, hg⟩ := (ConormalGradedAlgebra.presentation i).stalkChart z
  obtain ⟨es, hsc, hsg⟩ := (ConormalGradedAlgebra.presentation i).symmetricStalk z
  obtain ⟨ec, hec, hcg⟩ := (ConormalGradedAlgebra.presentation i).conormalStalk z
  let t : SymmetricAlgebra S C →+* Ideal.associatedGraded J :=
    eg.hom.hom.comp (((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (ConormalGradedAlgebra.symmetricComparison i).right.hom).hom.comp es.inv.hom)
  have htC (r : S) : t (algebraMap S (SymmetricAlgebra S C) r) =
      algebraMap (R ⧸ J) (Ideal.associatedGraded J) (q.symm r) := by
    obtain ⟨a, ha⟩ := i.stalkMap_surjective z r
    obtain ⟨U, hz, a, hga⟩ := X.presheaf.exists_germ_eq a
    have hr : Z.presheaf.germ (i ⁻¹ᵁ U) z hz (i.app U a) = r := by
      rw [← Scheme.Hom.germ_stalkMap_apply, hga]
      exact ha
    rw [← hr, ← hsc (i ⁻¹ᵁ U) hz (i.app U a)]
    change eg.hom (((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (ConormalGradedAlgebra.symmetricComparison i).right.hom)
        (es.inv (es.hom _))) = _
    erw [CommRingCat.inv_hom_apply]
    have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
      (i ⁻¹ᵁ U) z hz (ConormalGradedAlgebra.symmetricComparison i).right.hom
    erw [hgerm]
    have hw := congrArg (fun f ↦ f.hom.app (op (i ⁻¹ᵁ U)) (i.app U a))
      (Under.w (ConormalGradedAlgebra.symmetricComparison i))
    change (ConormalGradedAlgebra.symmetricComparison i).right.hom.app (op (i ⁻¹ᵁ U))
      ((SymmetricAlgebraSheaf.algebra (ConormalGradedAlgebra.piece i 1)).hom.hom.app
        (op (i ⁻¹ᵁ U)) (i.app U a)) =
      (ConormalGradedAlgebra.presentation i).algebra.hom.hom.app
        (op (i ⁻¹ᵁ U)) (i.app U a) at hw
    rw [hw, ← (ConormalGradedAlgebra.presentation i).constants U a]
    obtain ⟨h, he⟩ := hg 0 U hz a
    rw [he]
    change DirectSum.of (Ideal.associatedGradedPiece J) 0
      (Submodule.Quotient.mk ⟨X.presheaf.germ U (i z) hz a, h⟩) = _
    have hq : q.symm (Z.presheaf.germ (i ⁻¹ᵁ U) z hz (i.app U a)) =
        Ideal.Quotient.mk J (X.presheaf.germ U (i z) hz a) := by
      apply q.injective
      rw [q.apply_symm_apply]
      exact (Scheme.Hom.germ_stalkMap_apply i U z hz a).symm
    rw [hq]
    rfl
  have htι (y : J) : t (SymmetricAlgebra.ι S C (ec.symm (J.toCotangent y))) =
      DirectSum.of (Ideal.associatedGradedPiece J) 1
        (Submodule.Quotient.mk
          (⟨y, by simpa only [pow_one] using y.property⟩ : (J ^ 1 : Ideal R))) := by
    obtain ⟨U, hz, a, hx⟩ := exists_conormal_representative i z
      (ec.symm (J.toCotangent y))
    have hs := (hsg (i ⁻¹ᵁ U) hz (ConormalGradedAlgebra.representative i 1 U a)).trans
      (congrArg (SymmetricAlgebra.ι S C) hx)
    have hinv := (congrArg (fun x ↦ es.inv x) hs).symm.trans
      (CommRingCat.inv_hom_apply es _)
    change eg.hom (((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (ConormalGradedAlgebra.symmetricComparison i).right.hom)
        (es.inv (SymmetricAlgebra.ι S C (ec.symm (J.toCotangent y))))) = _
    refine (congrArg (fun x ↦ eg.hom (((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (ConormalGradedAlgebra.symmetricComparison i).right.hom) x)) hinv).trans ?_
    refine (congrArg (fun x ↦ eg.hom x)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply (i ⁻¹ᵁ U) z hz
        (ConormalGradedAlgebra.symmetricComparison i).right.hom
        ((SymmetricAlgebraSheaf.inclusion (ConormalGradedAlgebra.piece i 1)).val.app
          (op (i ⁻¹ᵁ U)) (ConormalGradedAlgebra.representative i 1 U a)))).trans ?_
    change eg.hom (TopCat.Presheaf.germ
      (ConormalGradedAlgebra.presentation i).algebra.right.obj (i ⁻¹ᵁ U) z hz
        ((ConormalGradedAlgebra.symmetricComparison i).right.hom.app (op (i ⁻¹ᵁ U))
          ((SymmetricAlgebraSheaf.inclusion (ConormalGradedAlgebra.piece i 1)).val.app
            (op (i ⁻¹ᵁ U)) (ConormalGradedAlgebra.representative i 1 U a)))) = _
    have hψ :
        (ConormalGradedAlgebra.symmetricComparison i).right.hom.app (op (i ⁻¹ᵁ U))
          ((SymmetricAlgebraSheaf.inclusion (ConormalGradedAlgebra.piece i 1)).val.app
            (op (i ⁻¹ᵁ U)) (ConormalGradedAlgebra.representative i 1 U a)) =
        ((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op (i ⁻¹ᵁ U))
          (ConormalGradedAlgebra.representative i 1 U a) :=
      (ConormalGradedAlgebra.presentation i).symmetricComparison.exists.choose_spec _ _
    obtain ⟨h, he⟩ := hg 1 U hz a
    obtain ⟨h', he'⟩ := hcg U hz a
    refine (congrArg (fun x ↦ eg.hom (TopCat.Presheaf.germ
      (ConormalGradedAlgebra.presentation i).algebra.right.obj (i ⁻¹ᵁ U) z hz x))
        hψ).trans (he.trans ?_)
    apply congrArg (DirectSum.of (Ideal.associatedGradedPiece J) 1)
    apply (Submodule.Quotient.eq _).mpr
    have heq := (he'.symm.trans ((congrArg ec hx).trans (ec.apply_symm_apply _)))
    exact (J.toCotangent_eq.mp heq)
  obtain ⟨f, hf, he⟩ := hr
  have heJ : Ideal.span (Set.range f) = J := he
  let y (j : Fin c) : J := ⟨f j, heJ ▸ Ideal.subset_span (Set.mem_range_self j)⟩
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin c) (R ⧸ J) J.Cotangent,
      ∀ j, b j = J.toCotangent (y j) := by
    exact regular_conormal_basis f hf J heJ
  let : Module S J.Cotangent := Module.compHom _ q.symm.toRingHom
  let ecL : C ≃ₗ[S] J.Cotangent :=
    { ec with
      map_smul' := by
        intro r x
        change ec (r • x) = q.symm r • ec x
        rw [← q.apply_symm_apply r]
        simpa only [q, RingEquiv.symm_apply_apply] using hec (q.symm r) x }
  let bc : Module.Basis (Fin c) S C :=
    (b.mapCoeffs q (fun x m ↦ by
      change q.symm (q x) • m = x • m
      rw [q.symm_apply_apply])).map ecL.symm
  have hbc (j : Fin c) : bc j = ec.symm (J.toCotangent (y j)) := by
    simp only [bc, Module.Basis.map_apply, Module.Basis.mapCoeffs_apply, hb]
    rfl
  let θ : MvPolynomial (Fin c) (R ⧸ J) →ₐ[R ⧸ J] Ideal.associatedGraded J :=
    MvPolynomial.aeval fun j ↦ DirectSum.of (Ideal.associatedGradedPiece J) 1
      (Submodule.Quotient.mk
        (⟨y j, by simpa only [pow_one] using (y j).property⟩ : (J ^ 1 : Ideal R)))
  have hθ : Function.Bijective θ := by
    exact regular_polynomial_bijective f hf J heJ
  have hbt : Function.Bijective t := by
    apply symmetric_bijective_of_polynomial (S := S) (T := R ⧸ J)
      (D := Ideal.associatedGraded J) (C := C) bc q.symm θ hθ t htC
    intro j
    rw [hbc, htι]
    exact (MvPolynomial.aeval_X (R := R ⧸ J) (S₁ := Ideal.associatedGraded J)
      (fun j ↦ DirectSum.of (Ideal.associatedGradedPiece J) 1
        (Submodule.Quotient.mk
          (⟨y j, by simpa only [pow_one] using (y j).property⟩ : (J ^ 1 : Ideal R)))) j).symm
  have hψ : Function.Bijective ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (ConormalGradedAlgebra.symmetricComparison i).right.hom) := by
    have heq : ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
        (ConormalGradedAlgebra.symmetricComparison i).right.hom).hom =
        eg.inv.hom.comp (t.comp es.hom.hom) := by
      apply RingHom.ext
      intro x
      change _ = eg.inv (eg.hom (((TopCat.Presheaf.stalkFunctor CommRingCat z).map
        (ConormalGradedAlgebra.symmetricComparison i).right.hom) (es.inv (es.hom x))))
      erw [CommRingCat.inv_hom_apply, CommRingCat.inv_hom_apply]
    change Function.Bijective ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (ConormalGradedAlgebra.symmetricComparison i).right.hom).hom
    rw [heq]
    exact (ConcreteCategory.bijective_of_isIso eg.inv).comp
      (hbt.comp (ConcreteCategory.bijective_of_isIso es.hom))
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hψ

/-- A regular immersion has a conormal module of rank `c`, and the canonical graded map
from its symmetric algebra to its conormal algebra is invertible.
Source: Stacks Tags 063M, 0637; Algebra Tag 00LN
(blueprint: def-pur-normal-bundle).

Proof: these are Steps 3--5 of the node. Finite type over the field makes X and Z
Noetherian (`lem-weil-pbc-finite-type-over-noetherian`). At each z the defining regular
sequence of length c gives the basis of J_z/J_z^2
(`lem-weil-pbc-regular-sequence-conormal-free`). The conormal-algebra stalk comparison
identifies these with conormal stalks. Coherence and the coherent free-stalk criterion
(`lem-sc-coherent-free-stalks-locally-free`) give local freeness; residue-field dimension
computes its rank as c. For every degree, the chosen regular generators identify Sym(C_z)
with the polynomial algebra on their basis
(`lem-weil-pbc-symmetric-algebra-free-module-polynomial` and its universal property).
The canonical map sends variables to their degree-one classes, so it is precisely the
isomorphism of `lem-pur-regular-sequence-graded-polynomial`. The module stalk criterion
(`lem-weil-pbc-module-iso-on-stalks`) makes it an isomorphism globally. Its module inverse
is an algebra map by applying the injective comparison to every algebra identity. -/
theorem regular_spec (P : WeilConjectures.PurityFiniteSetting.{u})
    (hX : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hX] [LocallyOfFiniteType hX] [QuasiCompact hX]
    [IsSeparated (i ≫ hX)] [LocallyOfFiniteType (i ≫ hX)] [QuasiCompact (i ≫ hX)]
    (c : ℕ) (hreg : IsRegularImmersionOfPureCodimension hX i c) :
    (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFreeOfRank c ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison i) := by
  have hNX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian hX
  have hNZ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ hX)
  have hb := fun z ↦ conormal_basis i c z (hreg.2.2 z)
  have hf : (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFree :=
    Scheme.Modules.isFiniteLocallyFree_of_coherent_free_stalks _
      ((ConormalGradedAlgebra.presentation i).coherent hNX 1)
      (fun z ↦ ⟨Module.Free.of_basis (hb z).some, Module.Finite.of_basis (hb z).some⟩)
  constructor
  · classical
    choose Y I hI hx e using Scheme.Modules.exists_mem_over_iso_free
      (ConormalGradedAlgebra.piece i 1)
    apply SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.mpr
    refine ⟨Z, Y, ?_, fun z ↦ ⟨(e z).some ≪≫ SheafOfModules.freeFunctor.mapIso ?_⟩⟩
    · rw [Opens.coversTop_iff]
      exact eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hx z⟩
    · have hc : Fintype.card (I z) = c := by
        rw [← Scheme.Modules.finrank_stalk_of_over_iso_free (e z) (hx z)]
        change Module.finrank (Z.presheaf.stalk z)
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
            (ConormalGradedAlgebra.piece i 1)) = c
        simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (hb z).some
      exact (((Fintype.equivFin (I z)).trans (finCongr hc)).trans Equiv.ulift.symm).toIso
  · have : ∀ z : Z, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
        (ConormalGradedAlgebra.symmetricComparison i).right.hom) :=
      fun z ↦ comparison_stalk_iso i c z (hreg.2.2 z)
    have : IsIso (ConormalGradedAlgebra.symmetricComparison i).right :=
      TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
    have : IsIso ((Under.forget Z.sheaf).map
        (ConormalGradedAlgebra.symmetricComparison i)) := ‹IsIso
          (ConormalGradedAlgebra.symmetricComparison i).right›
    exact isIso_of_reflects_iso (ConormalGradedAlgebra.symmetricComparison i)
      (Under.forget Z.sheaf)

/-- The regular normal cone equipped with its canonical vector-bundle identification.
The isomorphism is contravariantly induced by the canonical symmetric-algebra comparison.
Source: Stacks Tags 0637, 01M2 (blueprint: def-pur-normal-bundle). -/
def vectorBundle (P : WeilConjectures.PurityFiniteSetting.{u})
    (hX : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hX] [LocallyOfFiniteType hX] [QuasiCompact hX]
    [IsSeparated (i ≫ hX)] [LocallyOfFiniteType (i ≫ hX)] [QuasiCompact (i ≫ hX)]
    (c : ℕ) (hreg : IsRegularImmersionOfPureCodimension hX i c) :
    PurityVectorBundle P Z (i ≫ hX) c := by
  letI : (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFreeOfRank c :=
    (regular_spec i P hX c hreg).1
  letI : IsIso (ConormalGradedAlgebra.symmetricComparison i) :=
    (regular_spec i P hX c hreg).2
  let e : VectorBundleZeroSection.algebraObject Z c (ConormalGradedAlgebra.piece i 1) ≅
      algebraObject i :=
    ObjectProperty.isoMk _ (asIso (ConormalGradedAlgebra.symmetricComparison i))
  let eOver := (ObjectProperty.ι (fun Y : Over Z ↦ IsAffineHom Y.hom)).mapIso
    (((VectorBundleZeroSection.antiEquivalence Z).inverse.mapIso e).unop)
  exact {
    E := normalCone i
    p := projection i
    𝓔 := ConormalGradedAlgebra.piece i 1
    phi := (Over.forget Z).mapIso eOver
    over_commutes := Over.w eOver.hom }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical symmetric-algebra identification carries the degree-zero augmentation
section of the normal cone to the vector-bundle zero section.
Source: Stacks Tags 0637, 01M2 (blueprint: def-pur-normal-bundle).

Proof: Step 6 of the node. The symmetric-algebra augmentation fixes constants and kills
every degree-one generator (`def-pur-vector-bundle-zero-section`). The conormal
augmentation after the comparison has the same values, by preservation of degrees.
Uniqueness in `lem-weil-pbc-quasi-coherent-symmetric-algebra-core` identifies the algebra
maps. The contravariant relative-spectrum anti-equivalence then identifies their sections.
This uses the same chosen anti-equivalence and the exact canonical comparison used in
`vectorBundle`, so it is an equality of the displayed arrows. -/
theorem vectorBundle_zeroSection (P : WeilConjectures.PurityFiniteSetting.{u})
    (hX : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hX] [LocallyOfFiniteType hX] [QuasiCompact hX]
    [IsSeparated (i ≫ hX)] [LocallyOfFiniteType (i ≫ hX)] [QuasiCompact (i ≫ hX)]
    (c : ℕ) (hreg : IsRegularImmersionOfPureCodimension hX i c) :
    (vectorBundle i P hX c hreg).zeroSection = zeroSection i := by
  let := (regular_spec i P hX c hreg).1
  let := (regular_spec i P hX c hreg).2
  let E := VectorBundleZeroSection.antiEquivalence Z
  let A := VectorBundleZeroSection.algebraObject Z c (ConormalGradedAlgebra.piece i 1)
  let B := algebraObject i
  let e : A ≅ B := ObjectProperty.isoMk _
    (asIso (ConormalGradedAlgebra.symmetricComparison i))
  have h :
      E.inverse.map e.inv ≫
        E.functor.preimage ((E.counitIso.app A).hom ≫
          ObjectProperty.homMk (VectorBundleZeroSection.augmentationToBase Z
            (ConormalGradedAlgebra.piece i 1))) =
      E.functor.preimage ((E.counitIso.app B).hom ≫
        ObjectProperty.homMk (augmentationToBase i)) := by
    apply E.functor.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    have hn := E.counitIso.hom.naturality e.inv
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    erw [← Category.assoc, hn, Category.assoc]
    apply congrArg (fun q ↦ (E.counitIso.app B).hom ≫ q)
    apply ObjectProperty.hom_ext
    change inv (ConormalGradedAlgebra.symmetricComparison i) ≫
      VectorBundleZeroSection.augmentationToBase Z (ConormalGradedAlgebra.piece i 1) = _
    rw [← augmentation_comparison i, IsIso.inv_hom_id_assoc]
    all_goals rfl
  have h' := congrArg (fun q ↦ q.unop.hom.left) h
  exact h'

end AlgebraicGeometry.PurityNormalBundle
