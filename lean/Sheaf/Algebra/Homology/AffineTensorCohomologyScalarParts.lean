module

public import Sheaf.Algebra.Homology.RingTensorCohomology
import all Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso
import Sheaf.Algebra.Homology.BaseTensorOrdinaryIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! Intermediate scalar transport part of affine tensor cohomology. -/
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

open CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_homology_scalar
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive] [F.PreservesKFlatQuasiIso]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) (a : A) (b : B)
    (hscalar : ∀ X : ModuleCat.{u} A,
      F.map (a • 𝟙 X) = b • 𝟙 (F.obj X)) :
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map ((resolution A).map (a • 𝟙 M))) i =
      b • 𝟙 (((F.mapHomologicalComplex (.up ℤ)).obj ((resolution A).obj M)).homology i) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  have (N : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let P := (resolution A).obj M
  let s := (augmentation A).app M
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let qb := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  have hs : QuasiIso s := by dsimp [s, augmentation]; infer_instance
  have : IsIso (DerivedCategory.Qh.map (q.map s)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  have heq : DerivedCategory.Qh.map (q.map ((resolution A).map (a • 𝟙 M))) =
      DerivedCategory.Qh.map (q.map (a • 𝟙 P)) := by
    apply (cancel_mono (DerivedCategory.Qh.map (q.map s))).1
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (fun f ↦ DerivedCategory.Qh.map (q.map f))
    have hn := (augmentation A).naturality (a • 𝟙 M)
    change (resolution A).map (a • 𝟙 M) ≫ s = (a • 𝟙 P) ≫ s
    rw [show (resolution A).map (a • 𝟙 M) ≫ s = s ≫ (a • 𝟙 M) from hn]
    simp
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P (resolution_kFlat A M)
  have hext : DerivedCategory.Qh.map (Fh.map (q.map ((resolution A).map (a • 𝟙 M)))) =
      DerivedCategory.Qh.map (Fh.map (q.map (a • 𝟙 P))) := by
    apply (cancel_epi (F.leftDerivedFunctorCounit.app (q.obj P))).1
    have hn := F.leftDerivedFunctorCounit.naturality
      (q.map ((resolution A).map (a • 𝟙 M)))
    have hn' := F.leftDerivedFunctorCounit.naturality (q.map (a • 𝟙 P))
    dsimp only [Functor.comp_map] at hn hn'
    rw [← hn, ← hn']
    change F.leftDerivedFunctor.map _ ≫ _ = F.leftDerivedFunctor.map _ ≫ _
    rw [heq]
  have hext' : HomologicalComplex.homologyMap
      (Fc.map ((resolution A).map (a • 𝟙 M))) i =
      HomologicalComplex.homologyMap (Fc.map (a • 𝟙 P)) i := by
    let e := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).app
        (qb.obj (Fc.obj P)) ≪≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).app (Fc.obj P)
    apply (cancel_epi e.hom).1
    have hn (f : P ⟶ P) : H.map (DerivedCategory.Qh.map (qb.map (Fc.map f))) ≫ e.hom =
        e.hom ≫ HomologicalComplex.homologyMap (Fc.map f) i := by
      have hn := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.naturality
        (qb.map (Fc.map f))
      have hn' := (HomotopyCategory.homologyFunctorFactors
        (ModuleCat.{u} B) (.up ℤ) i).hom.naturality (Fc.map f)
      dsimp only [Functor.comp_map] at hn hn'
      change H.map (DerivedCategory.Qh.map (qb.map (Fc.map f))) ≫
        ((DerivedCategory.homologyFunctorFactorsh _ i).hom.app (qb.obj (Fc.obj P)) ≫
          (HomotopyCategory.homologyFunctorFactors _ (.up ℤ) i).hom.app (Fc.obj P)) = _
      rw [← Category.assoc, hn, Category.assoc, hn']
      rfl
    rw [← hn, ← hn]
    exact congrArg (fun f ↦ H.map f ≫ e.hom) hext
  rw [hext']
  have hterm : Fc.map (a • 𝟙 P) = b • 𝟙 (Fc.obj P) := by
    apply HomologicalComplex.Hom.ext
    funext j
    exact hscalar (P.X j)
  rw [hterm]
  unfold HomologicalComplex.homologyMap
  rw [show (HomologicalComplex.shortComplexFunctor _ _ i).map (b • 𝟙 (Fc.obj P)) =
    b • 𝟙 ((Fc.obj P).sc i) from rfl]
  simp only [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

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

open scoped TensorProduct ChangeOfRings in
private theorem extendScalars_smul_id
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (X : ModuleCat.{u} R) (r : R) :
    (ModuleCat.extendScalars (algebraMap R B)).map (r • 𝟙 X) =
      algebraMap R B r • 𝟙 ((ModuleCat.extendScalars (algebraMap R B)).obj X) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp only [ModuleCat.ExtendScalars.map_tmul]
  let : Algebra R B := (algebraMap R B).toAlgebra
  change (1 : B) ⊗ₜ[R] (r • x) = algebraMap R B r • ((1 : B) ⊗ₜ[R] x)
  rw [TensorProduct.tmul_smul]
  rfl

private theorem restrictScalars_smul_id
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (X : ModuleCat.{u} A) (r : R) :
    (ModuleCat.restrictScalars (algebraMap R A)).map (algebraMap R A r • 𝟙 X) =
      r • 𝟙 ((ModuleCat.restrictScalars (algebraMap R A)).obj X) := by
  ext x
  rfl

/-- The original-base scalar formulas for affine tensor cohomology.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-affine-tensor-cohomology-scalar-parts)

Proof: For an additive module functor F preserving K-flat quasi-isomorphisms,
let P be the chosen resolution of M. Augmentation naturality and linearity show
that resolution(a times identity) and a times identity on P become equal after
localization, since the augmentation is a quasi-isomorphism. Apply the existing
left derived functor of F. Naturality and invertibility of its counit on P then
identify the localized termwise F maps. The natural homology factorization
isomorphisms give equality on ordinary homology. If F sends a times identity
to b times identity on modules, termwise extensionality and linearity of
short-complex homology give b times identity on this homology.
For source, take F to be extension from R to B and apply this argument to the
restricted complex. Restriction and tensor balancing give the scalar formula.
For target, take F to be restriction from A to R followed by extension to B.
Ordinary tensor associativity identifies its map on A-K-flat complexes with
extension from A to A tensor_R B followed by restriction to B. The generator
formulas give the commuting arrow square, so this F preserves K-flat
quasi-isomorphisms. Apply the same argument to the A-resolution. No additivity
of the resolution functor, boundedness, or flatness of A or B over R is needed.
The argument covers r = 0, r = 1, zero complexes and zero coefficient rings. -/
theorem affineTensorCohomology_scalar_parts
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : R),
      (source R A B i).map (algebraMap R A r • 𝟙 M) =
        algebraMap R B r • 𝟙 ((source R A B i).obj M)) ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : R),
      (target R A B i).map (algebraMap R A r • 𝟙 M) =
        algebraMap R B r • 𝟙 ((target R A B i).obj M)) := by
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
  · intro M r
    have hrestrict : (restrict R A).map (algebraMap R A r • 𝟙 M) =
        r • 𝟙 ((restrict R A).obj M) := by
      apply HomologicalComplex.Hom.ext
      funext j
      exact restrictScalars_smul_id R A (M.X j) r
    change HomologicalComplex.homologyMap
      ((extend R B).map ((resolution R).map
        ((restrict R A).map (algebraMap R A r • 𝟙 M)))) i = _
    rw [hrestrict]
    exact resolution_homology_scalar R B (ModuleCat.extendScalars (algebraMap R B))
      ((restrict R A).obj M) i r (algebraMap R B r) (fun X ↦ extendScalars_smul_id R B X r)
  · intro M r
    change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map
        ((resolution A).map (algebraMap R A r • 𝟙 M))) i = _
    apply resolution_homology_scalar A B F M i (algebraMap R A r) (algebraMap R B r)
    intro X
    change (ModuleCat.extendScalars (algebraMap R B)).map
      ((ModuleCat.restrictScalars (algebraMap R A)).map (algebraMap R A r • 𝟙 X)) = _
    rw [restrictScalars_smul_id]
    exact extendScalars_smul_id R B _ r
end RingTensorCohomology
