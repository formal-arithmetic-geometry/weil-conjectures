/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResidueTorTest
import WeilConjectures.Algebra.Homology.SmoothBaseChange.AlternatingUnitResolution
/-! # Periodic quotient Tor computed by an alternating unit resolution -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u})
  {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)

private def ordinaryIso : pbcExtend φ ≅ SheafOfModules.ordinaryExtension.{u + 1, u, u + 1}
  (J := ProEt.topology T) φ := by
  let F := pbcExtend φ
  have hobj (M : pbcModules T R) : F.obj M =
      (SheafOfModules.ordinaryExtension.{u + 1, u, u + 1}
        (J := ProEt.topology T) φ).obj M :=
    (pbcExtensionExistence φ).choose_spec.choose M
  refine NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) ?_
  intro M N f
  have hm : F.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm :=
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose f
  change F.map f ≫ eqToHom (hobj N) = _
  rw [hm]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl


private def leftTensorIso
    (M : pbcModules T R) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    tensorLeft M ≅ SheafOfModules.leftTensorSheaf (B := R) M := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  refine NatIso.ofComponents (fun N ↦ SheafOfModules.tensorObjIsoSheafification M N) ?_
  intro N N' f
  have h := SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom_kfi M f
  let a := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  have he : (SheafOfModules.leftTensorSheaf (B := R) M).map f =
      a.map (M.val ◁ f.val) := by
    change a.map (SheafOfModules.siteTensorSecondMap M.val f.val) = _
    congr 1
  rw [he]
  exact h

private def extensionTensorIso :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    tensorLeft ((pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))) ≅
      pbcExtend φ ⋙ pbcRestrict φ := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  exact leftTensorIso T _ ≪≫ SheafOfModules.tensorExtensionIso (J := ProEt.topology T) φ ≪≫
    Functor.isoWhiskerRight (ordinaryIso T φ).symm (pbcRestrict φ)

private theorem scalar_resolution_homology
    (P : CochainComplex (pbcModules T R) ℤ)
    (r : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))))
    (hP : CochainComplex.IsKFlatResolutionIndependentCoefficients r)
    (M : pbcModules T R) (i : ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    Nonempty ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i ≅
      (pbcRestrict φ).obj ((DerivedCategory.homologyFunctor _ i).obj
        ((pbcDerivedExtend φ).obj ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let sM := (CochainComplex.singleFunctor _ 0).obj M
  obtain ⟨Q, s, hQ, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) sM
  have : QuasiIso r := hP.1
  have : QuasiIso s := hs
  let F := curriedTensor (pbcModules T R)
  let f := HomologicalComplex.mapBifunctorMap (𝟙 P) s F (.up ℤ)
  let g := HomologicalComplex.mapBifunctorMap r (𝟙 Q) F (.up ℤ)
  have : QuasiIso f := ResidueTensor.tensor_left_quasiIso R s hs hP.2
  have : QuasiIso g := ResidueTensor.tensor_right_quasiIso R r hP.1 hQ
  let e₁ := CochainComplex.mapBifunctorSingle₂Iso F M P
  let e₂ := CochainComplex.mapBifunctorSingle₁Iso F
    ((pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))) Q
  let e₃ := (NatIso.mapHomologicalComplex (extensionTensorIso T φ) (.up ℤ)).app Q
  have : IsIso (pbcComplexCounit φ Q) := complexCounit_isIso T φ Q hQ
  let e₄ := (pbcDerivedRestrict φ).mapIso (asIso (pbcComplexCounit φ Q)) ≪≫
    (pbcRestrict φ).mapDerivedCategoryFactors.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q)
  let e₅ := DerivedCategory.Q.mapIso e₃
  let e₆ := (pbcDerivedExtend φ).mapIso (asIso (DerivedCategory.Q.map s))
  exact ⟨(HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso e₁.symm ≪≫
    (asIso (HomologicalComplex.homologyMap f i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap g i) ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso e₂ ≪≫
    ((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      (e₅ ≪≫ e₄.symm ≪≫ (pbcDerivedRestrict φ).mapIso e₆) ≪≫
    ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso i).symm.app _⟩



private local instance restriction_faithful
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) : (pbcRestrict φ).Faithful where
  map_injective := by
    intro M N f g h
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

private theorem full_restriction_of_unit_epi
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (p : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S))) [Epi p]
    (hp : ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : R.obj.obj U) = (1 : S.obj.obj U)) :
    (pbcRestrict φ).Full := by
  let F := SheafOfModules.toSheaf ((adicLisseForget T).obj R)
  have : Epi (F.map p) := inferInstance
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology T) (F.map p).hom :=
    (Sheaf.isLocallySurjective_iff_epi' _ (F.map p)).2 inferInstance
  have hform (U : T.ProEtᵒᵖ) (x : R.obj.obj U) :
      p.val.app U x = φ.hom.app U x := by
    have h := (p.val.app U).hom.map_smul x (1 : R.obj.obj U)
    change (p.val.app U (x * (1 : R.obj.obj U)) : S.obj.obj U) =
      φ.hom.app U x * (@id (S.obj.obj U) (p.val.app U (1 : R.obj.obj U))) at h
    simpa only [mul_one, hp U, id_eq] using h
  have : Presheaf.IsLocallySurjective (ProEt.topology T)
      ((adicLisseForget T).map φ).hom := by
    constructor
    intro U s
    apply (ProEt.topology T).superset_covering _ (Presheaf.imageSieve_mem _ (F.map p).hom s)
    intro V f hf
    obtain ⟨x, hx⟩ := hf
    exact ⟨x, (hform (op V) x).symm.trans hx⟩
  exact SheafOfModules.restriction_full ((adicLisseForget T).map φ)




private theorem tensor_scalar_zero
    (f : End (SheafOfModules.unit ((adicLisseForget T).obj R)))
    (M : pbcModules T R)
    (hkill : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (1 : R.obj.obj U) • x = 0) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    (MonoidalCategory.tensorRight M).map f = 0 := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  have hμ : ReductionTensor.tensorMultiplication T R f M = 0 := by
    ext U x
    change (ReductionTensor.tensorMultiplication T R f M).val.app U x = 0
    rw [ReductionTensor.tensorMultiplication_apply]
    exact hkill U x
  let e := ReductionTensor.tensorUnitIso T R M
  have hsite : (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := R) M).map f = 0 := by
    apply (cancel_epi e.inv).1
    apply (cancel_mono e.hom).1
    change e.inv ≫ (SheafOfModules.siteSheafTensorRight M).map f ≫ e.hom = 0 at hμ
    simpa only [Category.assoc, comp_zero, zero_comp] using hμ
  let c := SheafOfModules.siteSheafTensorRightIso R M
  apply (cancel_epi (c.hom.app _)).1
  have h := c.hom.naturality f
  rw [hsite, zero_comp] at h
  simpa only [comp_zero] using h.symm

/-- An exact alternating resolution of a quotient unit computes nonpositive Tor with
any quotient module annihilated by both alternating scalars.

Source: blueprint order 1429, residue counterexample in the levelwise-truncation
proposition; Stacks Project, Tag 0118.
(blueprint: lem-weil-pbc-periodic-quotient-tor).

Proof: the exact alternating complex of units resolves the cokernel of the second
scalar. The normalized quotient epimorphism identifies this cokernel with the
restricted quotient unit. This bounded-above complex of flat modules is K-flat.
After tensoring with the given module both differentials vanish, so every
nonpositive cohomology is the module itself. To identify this calculation with the
specified derived scalar extension, choose a K-flat resolution of the module and
use the double tensor complex. Tensoring either augmentation is a quasi-isomorphism;
the ordinary tensor-extension comparison and the universal derived-extension counit
identify the other end with the prescribed derived reduction. Finally exact faithful
full quotient restriction lifts the resulting cohomology isomorphism to the quotient.
The computation includes degree zero and makes no boundedness assumption on Tor. -/
theorem periodicQuotient_tor
    (f g : End (SheafOfModules.unit ((adicLisseForget T).obj R)))
    (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hef : (ShortComplex.mk f g hfg).Exact)
    (heg : (ShortComplex.mk g f hgf).Exact)
    (p : SheafOfModules.unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget T).obj S)))
    [Epi p] (hp : ∀ U : T.ProEtᵒᵖ,
      p.val.app U (1 : R.obj.obj U) = (1 : S.obj.obj U))
    (hz : g ≫ p = 0) (hex : (ShortComplex.mk g p hz).Exact)
    (N : pbcModules T S)
    (hfkill : ∀ (U : T.ProEtᵒᵖ) (x : ((pbcRestrict φ).obj N).val.obj U),
      f.val.app U (1 : R.obj.obj U) • x = 0)
    (hgkill : ∀ (U : T.ProEtᵒᵖ) (x : ((pbcRestrict φ).obj N).val.obj U),
      g.val.app U (1 : R.obj.obj U) • x = 0)
    (i : ℤ) (hi : i ≤ 0) :
    Nonempty ((DerivedCategory.homologyFunctor _ i).obj
      ((pbcDerivedExtend φ).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((pbcRestrict φ).obj N))) ≅ N) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let := full_restriction_of_unit_epi T φ p hp
  let M := (pbcRestrict φ).obj N
  let v := cokernel.desc g p hz
  have : Mono v := hex.mono_cokernelDesc
  have : Epi (cokernel.π g ≫ v) := by simpa only [v, cokernel.π_desc] using inferInstanceAs (Epi p)
  have : Epi v := epi_of_epi (cokernel.π g) v
  have : IsIso v := isIso_of_mono_of_epi v
  obtain ⟨P,r,hP,hcoh⟩ := SheafOfModules.alternatingUnit_resolution R f g hfg hgf hef heg
  let r' := r ≫ (CochainComplex.singleFunctor _ 0).map v
  have : QuasiIso r := hP.1
  have : QuasiIso r' := inferInstanceAs (QuasiIso (r ≫ (CochainComplex.singleFunctor _ 0).map v))
  obtain ⟨eh⟩ := scalar_resolution_homology T φ P r' ⟨inferInstance,hP.2⟩ M i
  obtain ⟨ez⟩ := hcoh M i hi (tensor_scalar_zero T f M hfkill) (tensor_scalar_zero T g M hgkill)
  exact ⟨(pbcRestrict φ).preimageIso (eh.symm ≪≫ ez ≪≫ MonoidalCategory.leftUnitor M)⟩

end AlgebraicGeometry.Scheme
