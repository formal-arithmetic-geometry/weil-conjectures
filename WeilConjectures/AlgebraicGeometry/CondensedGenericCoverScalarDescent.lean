/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedComponentScalarModel.CondensedComponentScalarModelData
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.CondensedIrreducibleGenericScalarModel
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion

/-! # Descending a fixed geometric-generic scalar value to a contractible cover

Source: Hemo--Richarz--Scholbach, Theorem 4.13, irreducible case, diagram (4.4).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem indEtale_bijective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) : f.IndEtale := by
  rw [RingHom.IndEtale.iff_ind_etale]
  exact MorphismProperty.le_ind _ _ (RingHom.Etale.of_bijective hf)

private theorem indEtale_respectsIso : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
  (show RingHom.StableUnderComposition (@RingHom.IndEtale.{u}) from by
    intro A B C _ _ _ f g hf hg
    exact hg.comp hf).respectsIso fun e ↦ indEtale_bijective _ e.bijective

private theorem indEtale_across {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.IndEtale) : f.IndEtaleAcrossUniverses := by
  exact indEtale_respectsIso.1 _ (ULift.ringEquiv : ULift.{u} B ≃+* B).symm
    (indEtale_respectsIso.2 _ (ULift.ringEquiv : ULift.{u} A ≃+* A) hf)

private theorem spectrum_indEtale {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.IndEtale) :
    (Spec.map (CommRingCat.ofHom f)).appTop.hom.IndEtale := by
  have h := indEtale_respectsIso.1 _
    (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
    (indEtale_respectsIso.2 _
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv hf)
  have heq : (Spec.map (CommRingCat.ofHom f)).appTop =
      (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom f ≫
        (Scheme.ΓSpecIso (.of B)).inv := by
    apply (cancel_mono (Scheme.ΓSpecIso (.of B)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Scheme.ΓSpecIso_naturality]
  rw [heq]
  exact h

private theorem spectrum_faithfullyFlat {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat) :
    (Spec.map (CommRingCat.ofHom f)).appTop.hom.FaithfullyFlat := by
  have h := RingHom.FaithfullyFlat.respectsIso.1 _
    (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
    (RingHom.FaithfullyFlat.respectsIso.2 _
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv hf)
  have heq : (Spec.map (CommRingCat.ofHom f)).appTop =
      (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom f ≫
        (Scheme.ΓSpecIso (.of B)).inv := by
    apply (cancel_mono (Scheme.ΓSpecIso (.of B)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Scheme.ΓSpecIso_naturality]
  rw [heq]
  exact h

/-- A specified geometric-generic scalar model descends to a w-contractible affine
cover of an irreducible affine base. The perfect value and its generic comparison
are inputs; this statement neither constructs the value nor compares components.

Source: HRS Theorem 4.13, diagram (4.4) and the paragraph following it
(blueprint: lem-pod-condensed-generic-cover-scalar-descent).

Proof:
1. Choose a faithfully flat ind-etale w-contractible affine cover T of X. Let V be
its geometric-generic fibre and h : pi_0(V) -> pi_0(T) its component map. Flat going
down lifts the generic point below each point of T, in the same connected component.
A point of the fibre product exists above the resulting pair of points over X.
Thus h is onto. Its target is extremally disconnected profinite, so Stonean
projectivity gives a continuous section a. The empty case uses the empty section.
2. Component pullback on T is an equivalence on lisse objects, so K|T is the
pullback of a dualizable L on pi_0(T). On V the actual component pullback is an
equivalence on all module derived objects: use the profinite description of the
geometric-point affine basis, weakly-etale localization, coefficient comparison,
and termwise passage through the exact module equivalence to the unbounded
ordinary derived category. This comparison uses the actual component functor.
3. Pull the given generic model to V. The component-derived square and scalar
compatibility identify it with pi_V^* h^* L = pi_V^* F_pi_0(V)(P). Full faithfulness
of the V comparison gives h^* L = F_pi_0(V)(P). Pull along a, use h a = id, and
use scalar-realization compatibility to get L = F_pi_0(T)(P). Component pullback
to T gives the required isomorphism. All comparisons use the canonical coefficient
map and are natural on ordinary derived categories; no flatness of Lambda is used. -/
theorem generic_cover_scalar_descent
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsAffine X] [IrreducibleSpace X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (hK : Nonempty (HasRightDual K))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (hη : ∃ ξ : X, IsGenericPoint ξ (Set.univ : Set X) ∧ ξ ∈ Set.range η)
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (hP : DerivedCategory.IsPerfectRingComplex P)
    (e : (CondensedRing.upperStar Λ.X η).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X (Spec (.of Ω))).obj P) :
    ∃ (T : Scheme.{u}) (f : T ⟶ X),
      IsAffine T ∧ IsWContractibleRing Γ(T, ⊤) ∧ WeaklyEtale f ∧ Surjective f ∧
      Nonempty ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K ≅
        (condensedScalarRealization Λ.X T).obj P) := by
  classical
  let A := Γ(X, ⊤)
  obtain ⟨B, hring, halg, hind, hff, hw⟩ := exists_isWContractibleRing A
  let := hring
  let := halg
  let := hind
  let := hff
  let := hw
  let T := Spec (.of B)
  let f : T ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ X.isoSpec.inv
  have hff' : f.appTop.hom.FaithfullyFlat := by
    dsimp only [f]
    rw [Scheme.Hom.comp_appTop]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective
        ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance))
      (spectrum_faithfullyFlat _ (RingHom.faithfullyFlat_algebraMap_iff.mpr hff))
  have hind' : RingHom.IndEtaleAcrossUniverses f.appTop.hom := by
    apply indEtale_across
    dsimp only [f]
    rw [Scheme.Hom.comp_appTop]
    exact (spectrum_indEtale _ ((RingHom.IndEtale.algebraMap_iff _ _).mpr hind)).comp
      (indEtale_bijective _ ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance))
  have hη' : ∀ x : Spec (.of Ω), η x = genericPoint X := by
    obtain ⟨ξ, hξ, z, hz⟩ := hη
    intro x
    have hx : x = z := Subsingleton.elim _ _
    rw [hx, hz]
    exact hξ.eq (genericPoint_spec X)
  have hT : IsWContractibleRing Γ(T, ⊤) :=
    RingHom.wContractible_of_ringEquiv
      (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
  let := hT
  obtain ⟨m⟩ := (condensed_irreducible_generic_scalar_model Λ X Ω η hη' K hK).2
    P hP e T f hff' hind' hT
  have hfs : Flat f ∧ Surjective f :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mpr hff'
  have hfw : WeaklyEtale f := by
    dsimp only [f]
    infer_instance
  exact ⟨T, f, inferInstance, hT, hfw, hfs.2, ⟨m.model⟩⟩


end AlgebraicGeometry.ProEtale
