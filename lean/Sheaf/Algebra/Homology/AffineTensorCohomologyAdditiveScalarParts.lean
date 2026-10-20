module

public import WeilConjectures.Algebra.Homology.RingTensorCohomology
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-! Intermediate additivity part of affine tensor cohomology. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace RingTensorCohomology

private theorem resolution_kFlat (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat
      ((resolution A).obj M) :=
  (flatResolution A).kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le M

open scoped TensorProduct ChangeOfRings in
private theorem restrictedExtension_quasiIso_of_kFlat
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (a : P ⟶ Q)
    (ha : QuasiIso a)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q) :
    QuasiIso ((extend R B).map ((restrict R A).map a)) := by
  have : (ModuleCat.extendScalars (algebraMap R B)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  have : (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  obtain ⟨eP, heP⟩ := ModuleCat.exists_baseTensorOrdinaryIso R A B P
  obtain ⟨eQ, heQ⟩ := ModuleCat.exists_baseTensorOrdinaryIso R A B Q
  let F := (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)
  let G := (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).mapHomologicalComplex
      (.up ℤ)
  have : QuasiIso (F.map a) :=
    CochainComplex.scalarExtension_quasiIso_of_kFlat _ a ha hP hQ
  have : QuasiIso (G.map (F.map a)) := inferInstance
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk eP eQ ?_)).2 this
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    change (G.map (F.map a)).f j (eP.hom.f j (b ⊗ₜ[R, algebraMap R B] x)) =
      eQ.hom.f j (b ⊗ₜ[R, algebraMap R B] (a.f j x))
    rw [heP, heQ]
    rfl
  | add x y hx hy => simp only [_root_.map_add] at hx hy ⊢; rw [hx, hy]

open CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_homology_additive
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive] [F.PreservesKFlatQuasiIso]
    (i : ℤ) :
    (resolution A ⋙ F.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i).Additive := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  have (N : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ)
  let G := Fh ⋙ DerivedCategory.Qh
  let P : Set (HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) :=
    {X | ∃ K : CochainComplex (ModuleCat.{u} A) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat K ∧ q.obj K = X}
  have hres (X : HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) :
      ∃ (X' : HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ) s := by
    obtain ⟨M, rfl⟩ := X.quotient_obj_surjective
    refine ⟨q.obj ((resolution A).obj M), q.map ((augmentation A).app M), ?_, ?_⟩
    · exact ⟨_, resolution_kFlat A M, rfl⟩
    · rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff]
      dsimp [augmentation]
      infer_instance
  have hinv (X Y : HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ P) (hY : Y ∈ P)
      (hs : HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ) s) :
      IsIso (G.map s) := by
    obtain ⟨K, hK, rfl⟩ := hX
    obtain ⟨K', hK', rfl⟩ := hY
    exact F.isIso_Qh_map_mapHomotopyCategory_map
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hK)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hK') s hs
  obtain ⟨_, L, ε, _, ⟨c, htri⟩, hcompute⟩ :=
    Functor.leftDerived_from_resolvingClass (ModuleCat.{u} A)
      (DerivedCategory (ModuleCat.{u} B)) G P hres hinv
  let := c
  let := htri
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  -- The augmentation makes the localized resolution additive.
  let α := Functor.whiskerRight (augmentation A) (q ⋙ DerivedCategory.Qh)
  have : IsIso α := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro M
    have hs : QuasiIso ((augmentation A).app M) := by
      dsimp [augmentation]
      infer_instance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hs
  have hα : (resolution A ⋙ q ⋙ DerivedCategory.Qh).Additive :=
    Functor.additive_of_iso (asIso α).symm
  have : ((resolution A ⋙ q) ⋙ DerivedCategory.Qh ⋙ L).Additive := by
    change ((resolution A ⋙ q ⋙ DerivedCategory.Qh) ⋙ L).Additive
    infer_instance
  -- On the chosen K-flat resolutions the derived counit is invertible.
  let β := Functor.whiskerLeft (resolution A ⋙ q) ε
  have : IsIso β := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro M
    exact hcompute _ ⟨_, resolution_kFlat A M, rfl⟩
  have hβ : ((resolution A ⋙ q) ⋙ G).Additive :=
    Functor.additive_of_iso (asIso β)
  -- Homology factors through both the homotopy and derived categories.
  let e := isoWhiskerLeft (resolution A ⋙ q ⋙ Fh)
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i) ≪≫
    isoWhiskerLeft (resolution A)
      (isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm
          (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i) ≪≫
        isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
          (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i))
  have : ((resolution A ⋙ q ⋙ Fh) ⋙
      DerivedCategory.Qh ⋙ H).Additive := by
    change (((resolution A ⋙ q) ⋙ G) ⋙ H).Additive
    infer_instance
  exact Functor.additive_of_iso e

/-- Additivity of the two affine tensor cohomology functors.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-affine-tensor-cohomology-additive-parts)

Proof: Stacks Tag 06Y6 computes derived extension on K-flat models and makes
it an exact, hence additive, functor. The resolution augmentation identifies
source cohomology naturally with derived extension from R to B after restriction
from A, followed by homology. Thus additivity transports to source. For target,
ordinary tensor associativity identifies B tensor_R P with
(A tensor_R B) tensor_A P for the A-K-flat resolution P. The maps and inverses
are given on pure tensors, so the identification is natural in P and hence M.
This identifies target cohomology with derived extension from A to A tensor_R B,
followed by restriction to B and homology. These functors are additive, so
additivity transports to target by conjugation with the natural comparison.
The chosen resolution functor need not itself preserve addition. No flatness or
boundedness assumption is needed, and the same comparisons apply to zero rings
and zero complexes. -/
theorem affineTensorCohomology_additive_parts
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    (source R A B i).Additive ∧ (target R A B i).Additive := by
  have : (ModuleCat.extendScalars (algebraMap R B)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  have : (ModuleCat.extendScalars (algebraMap R B)).PreservesKFlatQuasiIso :=
    ⟨fun hP hQ f ↦ CochainComplex.scalarExtension_quasiIso_of_kFlat
      (algebraMap R B) f inferInstance hP hQ⟩
  let F := ModuleCat.restrictScalars (algebraMap R A) ⋙
    ModuleCat.extendScalars (algebraMap R B)
  have : F.PreservesKFlatQuasiIso :=
    ⟨fun hP hQ f ↦ restrictedExtension_quasiIso_of_kFlat
      R A B f inferInstance hP hQ⟩
  constructor
  · have := resolution_homology_additive R B (ModuleCat.extendScalars (algebraMap R B)) i
    change (restrict R A ⋙ resolution R ⋙ extend R B ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i).Additive
    infer_instance
  · exact resolution_homology_additive A B F i

end RingTensorCohomology
