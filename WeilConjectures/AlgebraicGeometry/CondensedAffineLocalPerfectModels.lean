/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedScalarRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Topology.Irreducible

import WeilConjectures.AlgebraicGeometry.CondensedFiniteClosedModelLifts
import WeilConjectures.AlgebraicGeometry.CondensedIrreducibleGenericScalarModel
import WeilConjectures.AlgebraicGeometry.CondensedLisseProEtaleLocality
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion

/-! # Scalar perfect models on affine schemes with finitely many components

Source: Hemo--Richarz--Scholbach, Theorem 4.13, affine forward implication
(blueprint: lem-zl-condensed-affine-local-perfect-models).
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

private theorem irreducible_spec_model
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (A : Type u) [CommRing A] [IsDomain A]
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.IndEtale A B]
    [Module.FaithfullyFlat A B] [IsWContractibleRing B]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
        (condensedRingObj Λ.X (Spec (.of A))))) (hK : IsDualizable K) :
    ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
      DerivedCategory.IsPerfectRingComplex P ∧
      Nonempty ((CondensedRing.upperStar Λ.X
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X (Spec (.of B))).obj P) := by
  let T := Spec (.of A)
  let Ω := AlgebraicClosure (T.residueField (genericPoint T))
  let η : Spec (.of Ω) ⟶ T := Spec.map
    (CommRingCat.ofHom (algebraMap (T.residueField (genericPoint T)) Ω)) ≫
      T.fromSpecResidueField (genericPoint T)
  have hη : ∀ x : Spec (.of Ω), η x = genericPoint T := by
    intro x
    change T.fromSpecResidueField (genericPoint T)
      ((Spec.map (CommRingCat.ofHom
        (algebraMap (T.residueField (genericPoint T)) Ω))) x) = genericPoint T
    exact Scheme.fromSpecResidueField_apply (genericPoint T) _
  obtain ⟨⟨P, hP, ⟨α⟩⟩, h⟩ :=
    condensed_irreducible_generic_scalar_model Λ T Ω η hη K hK
  have : IsWContractibleRing Γ(Spec (.of B), ⊤) :=
    RingHom.wContractible_of_ringEquiv
      (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
  obtain ⟨M⟩ := h P hP α (Spec (.of B))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (spectrum_faithfullyFlat _ (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance))
    (indEtale_across _ (spectrum_indEtale _
      ((RingHom.IndEtale.algebraMap_iff _ _).mpr inferInstance))) inferInstance
  exact ⟨P, hP, ⟨M.model⟩⟩

private theorem spec_finite_component_models
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (A : Type u) [CommRing A] (hcomponents : (irreducibleComponents (Spec (.of A))).Finite)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
        (condensedRingObj Λ.X (Spec (.of A))))) (hK : IsDualizable K) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (Spec (.of A)), ∀ i : C.I₀,
      ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
        DerivedCategory.IsPerfectRingComplex P ∧
        Nonempty ((CondensedRing.upperStar Λ.X (C.f i)).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X (C.X i)).obj P) := by
  classical
  change (irreducibleComponents (PrimeSpectrum A)).Finite at hcomponents
  have := hcomponents.to_subtype
  let ι := minimalPrimes A
  have hf : Finite ι :=
    Finite.of_injective (minimalPrimes.equivIrreducibleComponents (R := A)).toEquiv
      (minimalPrimes.equivIrreducibleComponents (R := A)).injective
  let := hf
  let I (a : ι) : Ideal A := a.1
  have (a : ι) : (I a).IsPrime := a.2.1.1
  have hcover (x : PrimeSpectrum A) : ∃ a : ι, I a ≤ x.asIdeal := by
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
      (J := x.asIdeal) bot_le
    exact ⟨⟨p, hp⟩, hpx⟩
  choose Cbar hring halg hind hff hw using fun a : ι ↦
    exists_isWContractibleRing (A ⧸ I a)
  let (a : ι) : CommRing (Cbar a) := hring a
  let (a : ι) : Algebra (A ⧸ I a) (Cbar a) := halg a
  let (a : ι) : Algebra A (Cbar a) :=
    Algebra.compHom (Cbar a) (Ideal.Quotient.mk (I a))
  have (a : ι) : IsScalarTower A (A ⧸ I a) (Cbar a) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let (a : ι) := hind a
  let (a : ι) := hff a
  let (a : ι) := hw a
  let q (a : ι) : Spec (.of (A ⧸ I a)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I a)))
  let K' (a : ι) := (CondensedRing.upperStar Λ.X (q a)).mapDerivedCategory.obj K
  have hm (a : ι) :
      ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
        DerivedCategory.IsPerfectRingComplex P ∧
        Nonempty ((CondensedRing.upperStar Λ.X
          (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I a) (Cbar a))))).mapDerivedCategory.obj
            (K' a) ≅
              (condensedScalarRealization Λ.X (Spec (.of (Cbar a)))).obj P) := by
    have := condensed_derivedPullback_preserves_dualizable Λ (q a) K hK
    exact irreducible_spec_model Λ (A ⧸ I a) (Cbar a) (K' a) this
  choose P hP e using hm
  have α (a : ι) : (CondensedRing.upperStar Λ.X
      (closedModelFiberMap A (Cbar a) ≫ closedModelLiftMap A (Cbar a))).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X (Spec (.of (Cbar a)))).obj (P a) := by
    have heq : closedModelFiberMap A (Cbar a) ≫ closedModelLiftMap A (Cbar a) =
        Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I a) (Cbar a))) ≫ q a := by
      dsimp [closedModelFiberMap, closedModelLiftMap, q]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (Algebra.ClosedLift.toAlgHom A (Cbar a)).commutes x
    exact (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarCongr Λ.X heq)).app K ≪≫
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ.X _ _)).app K ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app K ≪≫ (e a).some
  obtain ⟨h, _, _, _, _, hC⟩ :=
    condensed_finite_closed_model_lifts Λ A ι I hcover Cbar K hK P hP α
  let C : Scheme.Cover.{u} Scheme.proetalePrecoverage (Spec (.of A)) :=
    { I₀ := ι, X := fun a ↦ Spec (.of (Algebra.ClosedLift A (Cbar a))),
      f := fun a ↦ closedModelLiftMap A (Cbar a), mem₀ := hC }
  refine ⟨C, fun a ↦ ⟨P a, hP a, ?_⟩⟩
  exact ⟨(h a).2.2.2.2.1.choose⟩

/-- The affine forward step in the local perfect-model theorem.

Source: Hemo--Richarz--Scholbach, Theorem 4.13, irreducible and finite-component
paragraphs, using the prescribed henselian lifts of Bhatt--Scholze, Definition 2.2.10
and Lemmas 2.2.12 and 6.1.1
(blueprint: lem-zl-condensed-affine-local-perfect-models).

Proof:
Identify X with Spec A by its canonical affine isomorphism. Index the finitely many
irreducible components by their minimal prime ideals I_a; their quotient spectra cover
Spec A, by mem_irreducibleComponent and irreducibleComponent_mem_irreducibleComponents.
Each A/I_a is a domain, so its spectrum is nonempty irreducible. Apply
exists_isWContractibleRing to A/I_a to obtain a faithfully flat ind-etale algebra Cbar_a
which is w-contractible. Pull K back to Spec(A/I_a); it remains dualizable by
condensed_derivedPullback_preserves_dualizable. Choose a geometric generic point using
the algebraic closure of the residue field at the generic point. The theorem
condensed_irreducible_generic_scalar_model produces a perfect scalar complex P_a
and a scalar-model isomorphism on Spec Cbar_a, with the same P_a as at that point.
The canonical derived composition comparison identifies this restriction with the
restriction of K along closedModelFiberMap followed by closedModelLiftMap. Apply
condensed_finite_closed_model_lifts to the ideals I_a, the Cbar_a, and these specified
isomorphisms. It provides a pro-etale covering by Spec(ClosedLift A Cbar_a), together
with the scalar models P_a. Transport this cover back to X through its affine
isomorphism and use the canonical derived composition comparison. The index set is
finite but P_a may vary; no amplitude bound or coefficient flatness is used. For an
empty affine scheme the minimal-prime index set is empty and the same construction
is the empty pro-etale covering. -/
theorem condensed_affine_dualizable_local_perfect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsAffine X]
    (hcomponents : (irreducibleComponents X).Finite)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : Nonempty (HasRightDual K)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)),
        DerivedCategory.IsPerfectRingComplex P ∧
        Nonempty (((CondensedRing.upperStar Λ (C.f i)).mapDerivedCategory).obj K ≅
          (condensedScalarRealization Λ (C.X i)).obj P) := by
  classical
  let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
  let A := Γ(X, ⊤)
  have hA : (irreducibleComponents (Spec A)).Finite := by
    have he := irreducibleComponentsEquivOfIsPreirreducibleFiber
      X.isoSpec.hom.homeomorph X.isoSpec.hom.homeomorph.continuous
      X.isoSpec.hom.homeomorph.isOpenMap
      (fun _ ↦ (Set.subsingleton_singleton.preimage
        X.isoSpec.hom.homeomorph.injective).isPreirreducible)
      X.isoSpec.hom.homeomorph.surjective
    have := hcomponents.to_subtype
    have : Finite (irreducibleComponents (Spec A)) := Finite.of_equiv _ he.toEquiv.symm
    exact Set.toFinite _
  let F := (CondensedRing.upperStar Λ X.isoSpec.inv).mapDerivedCategory
  obtain ⟨C, hC⟩ := spec_finite_component_models R A hA (F.obj K)
    (condensed_derivedPullback_preserves_dualizable R X.isoSpec.inv K hK)
  let D := C.pushforward X.isoSpec.inv
    (Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance)
  refine ⟨D, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hC i
  refine ⟨P, hP, ⟨?_⟩⟩
  exact (Functor.mapDerivedCategoryNatIso
    (CondensedRing.upperStarComp Λ (C.f i) X.isoSpec.inv)).app K ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app K ≪≫ e

end AlgebraicGeometry.ProEtale
