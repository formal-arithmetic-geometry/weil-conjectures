/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.TAdmissibleCoefficientModels
public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
import Sheaf.Paper.CondensedAffineOrdinaryScalarSections
import Sheaf.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.Algebra.Category.ModuleCat.Descent
import Sheaf.CategoryTheory.ConstantModuleKFlat
import all Sheaf.RingTheory.DerivedModuleScalarAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exact ordinary scalar realization for flat condensed coefficients

Source: Hemo--Richarz--Scholbach, Section 3 and proof of Theorem 6.2(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Ordinary extension of discrete scalar modules along the constant-section map,
followed by the sectionwise/internal module equivalence and inverse image to X.
All the functors here are the ones used in `condensedScalarRealization`.
Source: HRS (3.1), Remark 3.2
(blueprint: lem-zl-flat-condensed-scalar-realization). -/
def ordinaryScalarRealization
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    ModuleCat.{u + 1} (scalarRing Λ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X) :=
  commutativeSiteConstantModuleFunctor (coherentTopology Profinite.{u}) (scalarRing Λ) ⋙
    (condensedScalarExtensionModel Λ.X).E ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ.X).inverse ⋙
    (upperStarFromPoint X).mapMod Λ.X

private noncomputable instance evaluation_additive
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (W : X.ProEt) : (SheafOfModules.evaluation.{u + 1} R (op W)).Additive :=
  inferInstanceAs ((SheafOfModules.forget.{u + 1} R ⋙
    PresheafOfModules.evaluation R.obj (op W)).Additive)

private theorem exact_of_spectrum_evaluations
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (S : ShortComplex (SheafOfModules.{u + 1} R))
    (hS : ∀ (D : CommRingCat.{u}) [IsWContractibleRing D]
      (f : Spec D ⟶ X) [WeaklyEtale f],
      (S.map (SheafOfModules.evaluation.{u + 1} R (op (Scheme.ProEt.mk f)))).Exact) :
    S.Exact := by
  let F := SheafOfModules.toSheaf.{u + 1} R
  have : PreservesFiniteColimits F :=
    (moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} R).2.2.1
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  apply F.epi_of_epi_map (f := kernel.lift S.g S.f S.zero)
  apply (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1}
    (F.map (kernel.lift S.g S.f S.zero))).1
  refine ⟨fun {V} x ↦ ?_⟩
  obtain ⟨I, W, f, hcover, hW⟩ := Scheme.ProEt.exists_wContractible_affine_cover X V
  have hcover' : Sieve.ofArrows W f ∈ Scheme.ProEt.topology X V :=
    Precoverage.generate_mem_toGrothendieck hcover
  refine (Scheme.ProEt.topology X).superset_covering ?_ hcover'
  rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
  obtain ⟨D, hD, e, _⟩ := hW i
  have : IsWContractibleRing D := hD
  let p := e.hom ≫ (W i).hom
  have : WeaklyEtale p := by dsimp [p]; infer_instance
  let ev := SheafOfModules.evaluation.{u + 1} R (op (Scheme.ProEt.mk p))
  have he : (S.map ev).Exact := hS D p
  have hs : Function.Surjective
      ((F.map (kernel.lift S.g S.f S.zero)).hom.app (op (Scheme.ProEt.mk p))) := by
    rw [ShortComplex.exact_map_iff_epi_map_kernel_lift,
      ModuleCat.epi_iff_surjective] at he
    exact he
  let zi : Scheme.ProEt.mk p ≅ W i := MorphismProperty.Over.isoMk e rfl
  let z := zi.hom
  let y := ((F.obj (kernel S.g)).obj.map (f i).op) x
  obtain ⟨b, hb⟩ := hs (((F.obj (kernel S.g)).obj.map z.op) y)
  have hz : Function.Surjective
      ((F.obj S.X₁).obj.map z.op) := by
    exact (ConcreteCategory.bijective_of_isIso _).2
  obtain ⟨c, hc⟩ := hz b
  have hcy : (F.map (kernel.lift S.g S.f S.zero)).hom.app (op (W i)) c = y := by
    apply (ConcreteCategory.bijective_of_isIso
      ((F.obj (kernel S.g)).obj.map z.op)).1
    have hn := ConcreteCategory.congr_hom
      ((F.map (kernel.lift S.g S.f S.zero)).hom.naturality z.op) c
    exact hn.symm.trans (by simpa only [AddCommGrpCat.comp_apply, hc] using hb)
  exact (Presheaf.imageSieve _ x).downward_closed ⟨c, hcy⟩ a

private theorem ordinaryScalarRealization_additive
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    (ordinaryScalarRealization Λ X).Additive := by
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    let : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  have : (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ.X).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : ((upperStarFromPoint X).mapMod Λ.X).Additive :=
    Functor.additive_of_preserves_binary_products _
  dsimp only [ordinaryScalarRealization]
  infer_instance

private theorem ordinaryScalarRealization_exact
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hflat : ∀ S : Profinite.{u}, ExtremallyDisconnected S → (scalarSectionMap Λ S).Flat)
    (X : Scheme.{u}) :
    PreservesFiniteLimits (ordinaryScalarRealization Λ X) ∧
      PreservesFiniteColimits (ordinaryScalarRealization Λ X) := by
  let F := ordinaryScalarRealization Λ X
  have : F.Additive := ordinaryScalarRealization_additive Λ X
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ.X X)
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have he (S : ShortComplex (ModuleCat.{u + 1} (scalarRing Λ))) (hS : S.Exact) :
      (S.map F).Exact := by
    apply ((S.map F).exact_map_iff_of_faithful e.functor).mp
    apply exact_of_spectrum_evaluations X _
    intro D hD f hf
    obtain ⟨r, ⟨θ⟩⟩ := condensed_affine_ordinary_scalar_sections.{u} Λ.X X D f
    let ev := SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (condensedRingObj Λ.X X))) (op (Scheme.ProEt.mk f))
    let res := ModuleCat.restrictScalars.{u + 1} r.inv.hom
    have : res.Faithful := inferInstance
    let t := ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (scalarSectionMap Λ (Profinite.of (ConnectedComponents (PrimeSpectrum D))))
    have : t.IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
        (scalarSectionMap Λ (Profinite.of (ConnectedComponents (PrimeSpectrum D))))).isLeftAdjoint
    have : t.Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
        (scalarSectionMap Λ
          (Profinite.of (ConnectedComponents (PrimeSpectrum D))))).left_adjoint_additive
    have : PreservesFiniteColimits t := inferInstance
    have : PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (scalarSectionMap Λ (Profinite.of (ConnectedComponents (PrimeSpectrum D))))) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (hflat _ (IsWContractibleRing.extremallyDisconnected_connectedComponents (R := D)))
    have hex : (S.map (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (scalarSectionMap Λ
          (Profinite.of (ConnectedComponents (PrimeSpectrum D)))))).Exact := hS.map _
    have hθ : F ⋙ e.functor ⋙ ev ⋙ res ≅
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (scalarSectionMap Λ (Profinite.of (ConnectedComponents (PrimeSpectrum D)))) := θ
    have hex' : (S.map (F ⋙ e.functor ⋙ ev ⋙ res)).Exact := by
      exact ShortComplex.exact_of_iso (S.mapNatIso hθ).symm hex
    exact ((S.map F |>.map e.functor |>.map ev).exact_map_iff_of_faithful res).mp hex'
  exact ((Functor.exact_tfae F).out 1 3).mp he

/-- Flat extremally disconnected evaluations make ordinary scalar realization exact,
and its termwise derived functor is the prescribed derived scalar realization.
No coherence, finite generation or geometric component condition is required.

Source: HRS Section 3, (3.1)--(3.2), Remark 3.2, and proof of Theorem 6.2(2)
(blueprint: lem-zl-flat-condensed-scalar-realization).

Proof: evaluate on the affine weakly contractible basis. The coefficient comparison
identifies sections with Λ(pi_0 V), and ordinary scalar realization evaluates as
extension of scalars along R -> Λ(pi_0 V), by the ordinary scalar-section comparison.
The component space is extremally disconnected, so the hypothesis makes this map flat.
Tensor therefore preserves the kernel/image/cokernel sequences of every scalar short
exact sequence. Exactness of sections on the basis and their conservativity imply
exactness of ordinary scalar realization. Additivity follows from its construction;
its right exactness is also the composite of the right exact constituent functors.
Termwise realization now preserves quasi-isomorphisms. Resolve a scalar complex by a
K-flat complex with flat terms. Constant realization preserves K-flatness, and the
counit of the fixed derived change-of-rings construction is invertible there. The
exact constituent functors give the prescribed comparison to ordinary realization
on these resolutions. Both functors invert the resolution maps, so naturality
extends the comparison to all scalar complexes and the localization universal
property gives the displayed natural isomorphism. The argument applies to arbitrary
unbounded complexes and to the zero ring and empty scheme. -/
theorem flat_ordinaryScalarRealization
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hflat : ∀ S : Profinite.{u}, ExtremallyDisconnected S → (scalarSectionMap Λ S).Flat)
    (X : Scheme.{u}) :
    ∃ (ha : (ordinaryScalarRealization Λ X).Additive)
      (hl : PreservesFiniteLimits (ordinaryScalarRealization Λ X))
      (hr : PreservesFiniteColimits (ordinaryScalarRealization Λ X)),
      letI := ha
      letI := hl
      letI := hr
      Nonempty ((ordinaryScalarRealization Λ X).mapDerivedCategory ≅
        condensedScalarRealization Λ.X X) := by
  classical
  have ha := ordinaryScalarRealization_additive Λ X
  obtain ⟨hl, hr⟩ := ordinaryScalarRealization_exact Λ hflat X
  refine ⟨ha, hl, hr, ?_⟩
  let R := scalarRing Λ
  let c := commutativeSiteConstantModuleFunctor (coherentTopology Profinite.{u}) R
  let m := condensedScalarExtensionModel Λ.X
  let p := (InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ.X).inverse
  let q := (upperStarFromPoint X).mapMod Λ.X
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    let : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  have : p.Additive := Functor.additive_of_preserves_binary_products p
  have : q.Additive := Functor.additive_of_preserves_binary_products q
  let φ := p ⋙ q
  let F := ordinaryScalarRealization Λ X
  let H := c.mapDerivedCategory ⋙ m.T ⋙ φ.mapDerivedCategory
  let β : DerivedCategory.Q ⋙ H ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight c.mapDerivedCategoryFactors.hom (m.T ⋙ φ.mapDerivedCategory) ≫
    Functor.whiskerLeft (c.mapHomologicalComplex (.up ℤ))
      (Functor.whiskerRight m.ε φ.mapDerivedCategory ≫
        Functor.whiskerLeft (m.E.mapHomologicalComplex (.up ℤ))
          φ.mapDerivedCategoryFactors.hom) ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (c ⋙ m.E)) (.up ℤ)).hom
        (φ.mapHomologicalComplex (.up ℤ)) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl ((c ⋙ m.E) ⋙ φ))
          (.up ℤ)).hom) DerivedCategory.Q
  have βiso (P : CochainComplex (ModuleCat.{u + 1} R) ℤ)
      (hP : P.IsKFlatForTotalTensor) (hf : ∀ n, Module.Flat R (P.X n)) :
      IsIso (β.app P) := by
    have hc := isKFlat_constantModule (coherentTopology Profinite.{u}) R P hP hf
    have := m.computes ((c.mapHomologicalComplex (.up ℤ)).obj P) hc
    dsimp [β]
    infer_instance
  have := ModuleCat.hasFunctorialFlatResolution_sameUniverse R
  have : IsIso β := by
    apply (NatTrans.isIso_iff_isIso_app β).2
    intro K
    obtain ⟨P, a, ha, hf, hP⟩ := K.exists_quasiIso_flat_kFlat
    have := ha
    have := βiso P hP (fun n ↦ (ModuleCat.flat_iff_flat _).1 (hf n))
    have h := β.naturality a
    have : IsIso ((DerivedCategory.Q ⋙ H).map a) := by dsimp; infer_instance
    have : IsIso ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map a) := by
      dsimp
      infer_instance
    exact IsIso.of_isIso_fac_left h
  have : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) (DerivedCategory.Q ⋙ H) H :=
    ⟨Iso.refl _⟩
  let e : H ≅ F.mapDerivedCategory := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ H F.mapDerivedCategory (asIso β)
  have k : φ.mapDerivedCategory ≅ p.mapDerivedCategory ⋙ q.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso p q
  exact ⟨e.symm ≪≫ Functor.isoWhiskerLeft (c.mapDerivedCategory ⋙ m.T) k⟩

end AlgebraicGeometry.ProEtale.CondensedRing
