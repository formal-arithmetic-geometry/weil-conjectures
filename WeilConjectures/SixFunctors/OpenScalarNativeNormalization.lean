/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarNativePullback
import WeilConjectures.SixFunctors.OpenScalarTotalNormalization
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement

/-! # Canonical normalization of the constructed native inverse image

Source: Stacks Project, Tags 03EL, 07A4 and 0FPT.
(blueprint: lem-sp-open-scalar-native-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor
attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

/-- The native derived tensor with its fixed K-flat representative comparison.
Source: Stacks Project, Tag 07A4
(blueprint: lem-sp-open-scalar-native-normalization). -/
def nativeTensorModel (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) : ProEtaleTensorModel T R where
  tensor := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} (Scheme.ProEt.topology T) R)
  representative := NatIso.ofComponents (fun Z ↦
    RingedDerivedNative.tensorIso.{u + 1, u, u + 1, u + 2} (Scheme.ProEt.topology T) R
      Z.1.obj Z.2.obj (Or.inl
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Z.1.obj).mpr
          Z.1.property.1))) (by
    intro Z W f
    exact RingedDerivedNative.tensorIso_naturality.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology T) R Z.1.obj Z.2.obj W.1.obj W.2.obj _ _ f.1.hom f.2.hom)

/-- The derived monoidal tensorator is the canonical representative-normalized comparison.
Source: Stacks Project, Tags 03EL, 07A4 and 0FPT
(blueprint: lem-sp-open-scalar-native-normalization).

Proof: on two flat K-flat complexes the exact derived monoidal construction gives
its localization square. The total-complex normalization identifies the ordinary
monoidal comparison with the canonical pure-tensor comparison. Cancel the two
invertible localization tensorators. This gives precisely the defining square
of the canonical inverse-image comparison. Its uniqueness on the resolving
subcategory makes the two natural isomorphisms equal on all derived objects. -/
theorem nativePullback_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (K H : DerivedCategory (proEtaleRingModules Y R)) :
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology Y) R
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology X) S
    letI := nativePullbackMonoidal f R S c
    Functor.OplaxMonoidal.δ (proEtaleRingDerivedPullback f R S c) K H =
      (proEtaleCanonicalTensorComparison f R S c (nativeTensorModel Y R)
        (nativeTensorModel X S)).hom.app (K, H) := by
  let := RingedDerivedNative.moduleMonoidal.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) R
  let := RingedDerivedNative.moduleSymmetric.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) R
  let := RingedDerivedNative.modulePreadditive.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) R
  let := RingedDerivedNative.moduleClosed.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) R
  let := RingedDerivedNative.moduleMonoidal.{u + 1, u, u + 1} (Scheme.ProEt.topology X) S
  let := RingedDerivedNative.moduleSymmetric.{u + 1, u, u + 1} (Scheme.ProEt.topology X) S
  let := RingedDerivedNative.modulePreadditive.{u + 1, u, u + 1} (Scheme.ProEt.topology X) S
  let := RingedDerivedNative.moduleClosed.{u + 1, u, u + 1} (Scheme.ProEt.topology X) S
  let := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} (Scheme.ProEt.topology Y) R
  let := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} (Scheme.ProEt.topology X) S
  let L := proEtaleRingModulePullback f R S c
  let F := proEtaleRingDerivedPullback f R S c
  let m := (ordinary_monoidal f R S c).choose
  have hm := (ordinary_monoidal f R S c).choose_spec
  let n := nativePullbackMonoidal f R S c
  let : F.Monoidal := n
  let a := nativeTensorModel Y R
  let b := nativeTensorModel X S
  let α : a.tensor ⋙ F ≅ F.prod F ⋙ b.tensor := NatIso.ofComponents
    (fun Z ↦ (Functor.Monoidal.μIso F Z.1 Z.2).symm) (by
      intro Z W g
      exact (Functor.OplaxMonoidal.δ_natural F g.1 g.2).symm)
  have hα : ∀ (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
      (hp : proEtaleFlatRepresentatives Y R P) (hq : proEtaleFlatRepresentatives Y R Q),
      ∃ (hp' : proEtaleFlatRepresentatives X S ((L.mapHomologicalComplex (.up ℤ)).obj P))
        (hq' : proEtaleFlatRepresentatives X S ((L.mapHomologicalComplex (.up ℤ)).obj Q)),
        F.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
          α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          b.tensor.map (Prod.mkHom (L.mapDerivedCategoryFactors.hom.app P)
            (L.mapDerivedCategoryFactors.hom.app Q)) =
        L.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)).inv ≫
          b.representative.hom.app (⟨_,hp'⟩,⟨_,hq'⟩) := by
    intro P Q hp hq
    have hp' := (proEtaleCanonicalTensorPullback f R S c a b).1 P hp
    have hq' := (proEtaleCanonicalTensorPullback f R S c a b).1 Q hq
    refine ⟨hp', hq', ?_⟩
    have hP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp.1
    have hQ := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mpr hq.1
    have hFP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr hp'.1
    have := RingedDerivedNative.isIso_mu.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology Y) R P Q (Or.inl hP)
    have := RingedDerivedNative.isIso_mu.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology X) S ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) (Or.inl hFP)
    have hpt := (HomotopyCategory.kFlat_quotient_obj_iff P).1
      (RingedDerivedNative.kFlat.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) R P hP)
    have hqt := (HomotopyCategory.kFlat_quotient_obj_iff Q).1
      (RingedDerivedNative.kFlat.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) R Q hQ)
    have hn := (derived_monoidal f R S c m).choose_spec P Q hpt hqt
    have ht := total_normalization f R S c m hm P Q
    rw [ht] at hn
    change F.map (inv (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ≫
        Functor.OplaxMonoidal.δ F (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        (L.mapDerivedCategoryFactors.hom.app P ⊗ₘ L.mapDerivedCategoryFactors.hom.app Q) =
      L.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f R S c P Q).inv ≫
        inv (Functor.LaxMonoidal.μ DerivedCategory.Q
          ((L.mapHomologicalComplex (.up ℤ)).obj P)
          ((L.mapHomologicalComplex (.up ℤ)).obj Q))
    apply (cancel_epi (F.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q))).mp
    apply (cancel_mono (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((L.mapHomologicalComplex (.up ℤ)).obj P)
      ((L.mapHomologicalComplex (.up ℤ)).obj Q))).mp
    simpa only [Category.assoc, ← F.map_comp_assoc, IsIso.hom_inv_id,
      F.map_id, Category.id_comp, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id,
      Category.comp_id] using hn
  have he : α = proEtaleCanonicalTensorComparison f R S c a b :=
    (proEtaleCanonicalTensorPullback f R S c a b).2.unique hα
      (proEtaleCanonicalTensorPullback f R S c a b).2.exists.choose_spec
  exact congrArg (fun e ↦ e.hom.app (K, H)) he

private theorem tensorModel_ext {T : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    (a b : ProEtaleTensorModel T R) (ht : a.tensor = b.tensor)
    (hi : ∀ P Q hp hq, HEq
      (a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩))
      (b.representative.app (⟨P, hp⟩, ⟨Q, hq⟩))) : a = b := by
  cases a with
  | mk ta ar =>
    cases b with
    | mk bt br =>
      dsimp only at ht
      cases ht
      have hr : ar = br := by
        ext Z
        exact congrArg Iso.hom (eq_of_heq
          (hi Z.1.obj Z.2.obj Z.1.property Z.2.property))
      cases hr
      rfl

private theorem tensorModel_eq_native (m : Models.{u}) (hm : NativeModels m)
    (A : Type u) [CommRing A] (T : Scheme.{u}) :
    tensorModel m A T = nativeTensorModel T (proEtaleConstantRing T A) := by
  apply tensorModel_ext
  · exact congrArg (fun s ↦ @MonoidalCategory.tensor _ _ s)
      (hm T (proEtaleConstantRing T A)).1
  · intro P Q hp hq
    exact native_tensorModel_comparison m hm A T P Q hp hq

/-- The constructed open monoidal structure has the prescribed canonical tensorator.
Source: Stacks Project, Tags 03EL, 07A4 and 0FPT
(blueprint: lem-sp-open-scalar-native-normalization).

Proof: the representative comparisons and the tensor bifunctors identify each
selected model with the native model. Transport the native normalization through
these model equalities and the monoidal-structure equalities. Equality elimination
identifies the transported tensorator, proving the asserted equation. -/
theorem nativeOpen_normalization (m : Models.{u}) (hm : NativeModels m)
    (A : Type u) [CommRing A] [Finite A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K H : proEtaleDerivedCategory X A) :
    openDelta m A j (nativeOpenMonoidal m hm A j) K H =
      (restrictionTensor m A j).hom.app (K, H) := by
  have hd := nativeOpenMonoidal_delta m hm A j K H
  have hn := nativePullback_normalization j (proEtaleConstantRing X A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A) K H
  have hc : HEq ((restrictionTensor m A j).hom.app (K, H))
      ((proEtaleCanonicalTensorComparison j (proEtaleConstantRing X A)
        (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)
        (nativeTensorModel X (proEtaleConstantRing X A))
        (nativeTensorModel U (proEtaleConstantRing U A))).hom.app (K, H)) := by
    change HEq ((proEtaleCanonicalTensorComparison j _ _ _
      (tensorModel m A X) (tensorModel m A U)).hom.app (K, H)) _
    rw [tensorModel_eq_native m hm A X, tensorModel_eq_native m hm A U]
  exact eq_of_heq (hd.trans ((heq_of_eq hn).trans hc.symm))

end AlgebraicGeometry.ProEtale.OpenScalarTensor
