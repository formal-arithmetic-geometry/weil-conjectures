/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.LocalizationCech.FlatLocalizationKoszulHomotopySupplement
import Mathlib.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.ProperBaseChange.RingedKoszulFactorColimit
import all WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# Localization annihilates the finite extended Cech complex

Source: Stacks Project, dualizing.tex, Tag 0A6R (lemma-local-cohomology-adjoint),
with the ringed-site sheafification construction of algebraization.tex, Tag 099E.
(blueprint: lem-weil-pbc-ringed-cech-localization-acyclic).
-/

@[expose] public section

set_option autoImplicit false

universe u wO wB

open CategoryTheory Opposite
open scoped ZeroObject TensorProduct

namespace CategoryTheory

open Limits

private theorem tensor_zero_of_power_torsion
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    (φ : A →+* B) (s : A) (e : ℕ) (hu : IsUnit (φ s))
    (hm : ∀ m : M, s ^ e • m = 0) :
    letI := φ.toAlgebra
    ∀ z : B ⊗[A] M, z = 0 := by
  let := φ.toAlgebra
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | add z z' hz hz' => simp [hz, hz']
  | tmul b m =>
    have hz : (φ s) ^ e • (b ⊗ₜ[A] m) = 0 := by
      calc
        (φ s) ^ e • (b ⊗ₜ[A] m) = b ⊗ₜ[A] (s ^ e • m) := by
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
            TensorProduct.smul_tmul']
          congr 1
          change (φ s) ^ e * b = φ (s ^ e) * b
          rw [map_pow]
        _ = 0 := by rw [hm, TensorProduct.tmul_zero]
    obtain ⟨v, hv⟩ := hu.pow e
    rw [← hv] at hz
    calc
      b ⊗ₜ[A] m = (↑v⁻¹ : B) • ((↑v : B) • (b ⊗ₜ[A] m)) := by
        rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hz, smul_zero]

private theorem localization_image_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat).sections)
    (X : Cᵒᵖ) :
    IsUnit ((ringedLocalizationRingUnitOfUniverses.{u, u, u} O s).hom.app X (s.val X)) := by
  exact (IsLocalization.Away.algebraMap_isUnit
    (R := O.obj.obj X)
    (S := ringedSectionLocalizationCarrierOfUniverses.{u, u, u} O s X)
    (show O.obj.obj X from s.val X)).map
      ((toSheafify J (ringedLocalizationRingPresheafOfUniverses.{u, u, u} O s)).app X).hom

private theorem changeOfRings_zero_of_power_torsion
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat).sections)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (e : ℕ) (hm : ∀ (X : Cᵒᵖ) (m : M.val.obj X),
      (show O.obj.obj X from s.val X) ^ e • m = 0) :
    IsZero (SheafOfModules.changeOfRings.{u, u, u}
      (ringedLocalizationRingUnitOfUniverses.{u, u, u} O s) M) := by
  let φ := ringedLocalizationRingUnitOfUniverses.{u, u, u} O s
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M
  have hp : IsZero P := by
    apply (IsZero.iff_id_eq_zero P).2
    apply PresheafOfModules.hom_ext
    intro X
    apply ConcreteCategory.hom_ext
    intro z
    exact tensor_zero_of_power_torsion (φ.hom.app X).hom (s.val X) e
      (localization_image_unit O s X) (hm X) z
  exact (PresheafOfModules.sheafification (𝟙 _)).map_isZero hp

private theorem koszul_homology_power_torsion
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (h : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (hs : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (f : W ⟶ V), S f →
        s.val (op W) ∈ Ideal.span (Set.range (fun i : Fin r ↦ (h i).val (op W))))
    (n : ℕ) (q : ℤ) (X : Cᵒᵖ)
    (m : (((ringedKoszulDiagram O r h).obj n).homology q).val.obj X) :
    (show O.obj.obj X from s.val X) ^ (r * (n + 1) + 1) • m = 0 := by
  let M := ((ringedKoszulDiagram O r h).obj n).homology q
  obtain ⟨S, hS, hmem⟩ := hs X.unop
  apply ((SheafOfModules.toSheaf _).obj M).isSeparated _ _ hS
  intro W f hf
  change M.val.map f.op (_ • m) = M.val.map f.op 0
  rw [map_zero, M.val.map_smul]
  change O.obj.map f.op ((show O.obj.obj X from s.val X) ^ _) •
    (show M.val.obj (op W) from M.val.map f.op m) = 0
  have hs' : O.obj.map f.op (show O.obj.obj X from s.val X) =
      (show O.obj.obj (op W) from s.val (op W)) := s.property f.op
  rw [map_pow, hs']
  exact ordered_koszul_ideal_power_annihilates_homology O r h n q (op W) _
    (Ideal.pow_mem_pow (hmem W f hf) _) _

private noncomputable def iso_of_obj_map
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B)
    (ho : ∀ M, F.obj M = G.obj M)
    (hf : ∀ {M N} (f : M ⟶ N), F.map f =
      eqToHom (ho M) ≫ G.map f ≫ eqToHom (ho N).symm) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ eqToIso (ho M)) (by
    intro M N f
    simp only [eqToIso.hom, hf, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id])

private noncomputable def extension_universes_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O B : Sheaf J CommRingCat.{u}) (φ : O ⟶ B) :
    SheafOfModules.RingedTensor.tensorFunctor φ ≅ scalarFunctor O φ := by
  let ep : SheafOfModules.RingedTensor.tensorPresheafFunctor φ ≅
      scalarPresheafFunctor O φ :=
    NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk (fun X ↦ Iso.refl _) (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b m =>
        exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ M f) b m).trans
          (SheafOfModules.changeOfRingsMap_tmulOfUniverses φ M f b m).symm)) (by
      intro M N f
      ext X z
      rfl)
  exact Functor.isoWhiskerRight ep (PresheafOfModules.sheafification (𝟙 _))

/-- Localizing at a section locally in the ideal of a finite generating list kills its
extended localization Cech complex in the unbounded derived category of localized modules.
The derived functor is the universal pair supplied by derived change of rings; its choice
is determined up to the unique counit-compatible isomorphism. No ideal sheaf or target
completeness hypothesis is used.

Source: Stacks Project, dualizing.tex, Tag 0A6R (lemma-local-cohomology-adjoint),
algebraization.tex, Tag 099E (lemma-global-extended-cech-complex).
(blueprint: lem-weil-pbc-ringed-cech-localization-acyclic).

Proof:
1. Compare the ordinary scalar-extension functor in the derived model with the
   universe-polymorphic extension functor. Identity maps on sectionwise tensor products
   give a natural isomorphism, since both restriction maps have the same pure-tensor
   formula. Scalar localization is exact, and extension preserves colimits by its
   adjunction to restriction of scalars.
2. The image of s in the localized ring sheaf is a unit. If a power of s annihilates
   every section of a module sheaf, that module's scalar extension vanishes: on a pure
   tensor move the power of s to the module factor, then cancel its invertible image.
   Module sheafification preserves this zero object.
3. In the nth ordered Koszul complex, the power r * (n + 1) + 1 of the ideal generated
   by the h_i annihilates homology. On the covering sieve in the hypothesis, s lies in
   this ideal. Naturality of s and separatedness of the homology sheaf therefore show
   that the same fixed power of s annihilates every homology section. Step 2 kills its
   scalar extension. This also covers the empty generating list.
4. The extended Cech complex is the filtered colimit of these Koszul complexes.
   Homology preserves this colimit because module sheaves form a Grothendieck abelian
   category. Scalar extension preserves it by step 1. The colimit of the zero objects
   from step 3 is zero, so all scalar-extended Cech homology objects vanish.
5. Exact scalar extension commutes with homology. Thus the scalar-extended Cech
   complex is acyclic, and its image in the derived category is zero.
6. Exact scalar extension preserves every quasi-isomorphism, so the universal derived
   counit is an isomorphism on every complex. Apply it to the Cech complex and transport
   the zero object of step 5 across this isomorphism. -/
theorem ringed_cech_localization_acyclic
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (h : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (s : (O.obj ⋙ forget CommRingCat).sections)
    [HasDerivedCategory.{wO} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ringedLocalizationRingOfUniverses.{u, u, u} O s)))]
    (hs : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (f : W ⟶ V), S f →
        s.val (op W) ∈ Ideal.span (Set.range (fun i : Fin r ↦ (h i).val (op W)))) :
    Nonempty
      (((Classical.choice
        (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u, u, u, wO, wB}
          (ringedLocalizationRingUnitOfUniverses.{u, u, u} O s))).T.obj
          (DerivedCategory.Q.obj (ringedExtendedCech O r h).1)) ≅ 0) := by
  classical
  let B := ringedLocalizationRingOfUniverses.{u, u, u} O s
  let φ := ringedLocalizationRingUnitOfUniverses.{u, u, u} O s
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)
  let D := Classical.choice
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u, u, u, wO, wB} φ)
  let e₀ : D.E ≅ SheafOfModules.RingedTensor.tensorFunctor φ :=
    iso_of_obj_map _ _ D.obj_eq D.map_eq
  let e₁ := extension_universes_iso O B φ
  obtain ⟨E, ho, hf, hadd, hlim, hcol, hstable⟩ := scalarLocalization_sheaf_exact J O s
  let e₂ : E ≅ scalarFunctor O φ := iso_of_obj_map _ _ ho hf
  obtain ⟨_, hlimD, hcolD⟩ := hstable D.E ⟨e₀ ≪≫ e₁ ≪≫ e₂.symm⟩
  let : PreservesFiniteLimits D.E := hlimD
  let : PreservesFiniteColimits D.E := hcolD
  let : (SheafOfModules.RingedTensor.tensorFunctor φ).IsLeftAdjoint :=
    (SheafOfModules.RingedTensor.tensorAdjunction φ).isLeftAdjoint
  let : PreservesColimitsOfShape ℕ D.E :=
    preservesColimitsOfShape_of_natIso e₀.symm
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let : AB5OfSize.{0, 0} A := AB5OfSize_of_univLE A
  let : HasExactColimitsOfShape ℕ A := inferInstance
  let K := ringedKoszulDiagram O r h
  obtain ⟨α, _⟩ := exists_ringed_cech_koszul_colimit_iso O r h
  have hz (q : ℤ) : IsZero (D.E.obj ((ringedExtendedCech O r h).1.homology q)) := by
    let H := HomologicalComplex.homologyFunctor A (.up ℤ) q
    let : PreservesColimitsOfShape ℕ H := inferInstance
    have hstage (n : ℕ) : IsZero (D.E.obj ((K.obj n).homology q)) := by
      rw [D.obj_eq]
      exact changeOfRings_zero_of_power_torsion O s _ (r * (n + 1) + 1)
        (koszul_homology_power_torsion O r h s hs n q)
    have hzero : IsZero ((H ⋙ D.E).obj (colimit K)) :=
      (isColimitOfPreserves (H ⋙ D.E) (colimit.isColimit K)).isZero_pt
        (Functor.isZero _ hstage)
    exact hzero.of_iso ((H ⋙ D.E).mapIso α).symm
  have hac : ((D.E.mapHomologicalComplex (.up ℤ)).obj
      (ringedExtendedCech O r h).1).Acyclic := by
    intro q
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ q).2
    exact (hz q).of_iso (((ringedExtendedCech O r h).1.sc q).mapHomologyIso D.E)
  have hε : IsIso D.ε := by
    let : D.T.IsLeftDerivedFunctor D.ε
        (HomologicalComplex.quasiIso A (.up ℤ)) := D.universal
    apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts
      (W := HomologicalComplex.quasiIso A (.up ℤ)) D.T D.ε
    intro P Q f hf
    let : QuasiIso f := hf
    let : QuasiIso ((D.E.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let := hε
  let L := (D.E.mapHomologicalComplex (.up ℤ)).obj (ringedExtendedCech O r h).1
  have : QuasiIso (0 : L ⟶ 0) :=
    ⟨fun q ↦ (quasiIsoAt_iff_exactAt' _ q
      (HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) q)).2 (hac q)⟩
  have hzQ : IsZero (DerivedCategory.Q.obj L) :=
    (DerivedCategory.Q.map_isZero (isZero_zero _)).of_iso
      (asIso (DerivedCategory.Q.map (0 : L ⟶ 0)))
  have hzero : IsZero (D.T.obj (DerivedCategory.Q.obj (ringedExtendedCech O r h).1)) :=
    hzQ.of_iso (asIso (D.ε.app _))
  exact ⟨hzero.isoZero⟩

end CategoryTheory
