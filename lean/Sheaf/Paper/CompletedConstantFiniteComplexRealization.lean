/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module
public import Sheaf.Paper.CompletedConstantRealizationData
import Sheaf.Paper.CompletedConstantModuleModel
import Sheaf.Paper.CompletedConstantResolutionTensorCalculation
import Sheaf.Paper.CompletedConstantDerivedTensorTower
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Homology.FullSubcategory
/-!
# Completed constant realization of finite complexes
Source: Stacks Project, proetale.tex, Tags 09BT and 09BV; sites-modules.tex,
Tags 093J--093M; algebra.tex, Tag 00MB
(blueprint: lem-weil-pbc-completed-constant-finite-complex-realization).
Positive quotient levels are indexed by `n : ℕ`, with exponent `n + 1`.
The comparison is stated on finite-free resolutions of bounded finite complexes.
Naturality on the category of resolutions includes independence of the resolution.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u v w vD vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
private theorem completedConstant_eval_step
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 2)).toRingHom) ≫
        CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)) =
      CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  change Ideal.Quotient.factorPowSucc I (n + 1)
    (AdicCompletion.evalₐ I (n + 2) (AdicCompletion.mk I A s)) =
      AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I A s)
  simp only [AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (s.val (n + 2)) = Ideal.Quotient.mk _ (s.val (n + 1))
  apply Ideal.Quotient.eq.mpr
  have hs := (Submodule.Quotient.eq _).mp
    (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ (n + 1)) s)
  simpa [smul_eq_mul, Ideal.mul_top] using hs


private theorem completedConstant_exists_resolution
    {C : Type (u + 1)} [CommRing C] [IsNoetherianRing C]
    (Q : CochainComplex (ModuleCat.{u + 1} C) ℤ)
    (hQ : completedConstantFiniteComplex Q) :
    ∃ (F : CochainComplex (ModuleCat.{u + 1} C) ℤ) (f : F ⟶ Q),
      completedConstantResolutions C (Arrow.mk f) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} C)
  obtain ⟨hfinite, a, b, hbound⟩ := hQ
  have : Q.IsStrictlyLE b := (Q.isStrictlyLE_iff b).2
    (fun i hi ↦ hbound i (Or.inr hi))
  have hcoh (i : ℤ) :
      Module.Finite C ((DerivedCategory.homologyFunctor (ModuleCat C) i).obj
        (DerivedCategory.Q.obj Q)) := by
    have := hfinite i
    have : Module.Finite C (Q.cycles i) :=
      Module.Finite.of_injective (Q.iCycles i).hom
        ((ModuleCat.mono_iff_injective _).1 inferInstance)
    have : Module.Finite C (Q.homology i) :=
      Module.Finite.of_surjective (Q.homologyπ i).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    let e : Q.homology i ≅
        (DerivedCategory.homologyFunctor (ModuleCat C) i).obj
          (DerivedCategory.Q.obj Q) :=
      (DerivedCategory.homologyFunctorFactors (ModuleCat C) i).symm.app Q
    exact Module.Finite.equiv e.toLinearEquiv
  have hpseudo := (DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology.{_, 0, u + 1}
    C (DerivedCategory.Q.obj Q)).2
      ⟨⟨b, fun i hi ↦ (DerivedCategory.Q.obj Q).isZero_of_isLE b i hi⟩, hcoh⟩
  obtain ⟨F, c, hc, hfree, ⟨e⟩⟩ := hpseudo
  have := hc
  have (i : ℤ) : CategoryTheory.Projective (F.X i) := by
    have := (hfree i).1
    infer_instance
  obtain ⟨f, hf⟩ := DerivedCategory.Q_map_surjective_of_projective F Q c e.hom
  have hfi : IsIso (DerivedCategory.Q.map f) := by rw [hf]; infer_instance
  refine ⟨F, f, ⟨?_, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat C) f).1 hfi,
    fun i ↦ ⟨(hfree i).2, (hfree i).1⟩, c, ?_⟩⟩
  · exact ⟨hfinite, a, b, hbound⟩
  · intro i hi
    exact F.isZero_of_isStrictlyLE c i hi

private theorem completedConstant_finite_quasiIso
    {C : Type (u + 1)} [CommRing C] [IsNoetherianRing C]
    {D : Type v} [Category.{w} D] [Abelian D] (c : ModuleCat.{u + 1} C ⥤ D)
    (hc : c.Additive)
    [PreservesFiniteLimits ((completedConstantFiniteModules C).ι ⋙ c)]
    [PreservesFiniteColimits ((completedConstantFiniteModules C).ι ⋙ c)]
    {F Q : CochainComplex (ModuleCat.{u + 1} C) ℤ} (f : F ⟶ Q)
    (hF : ∀ i : ℤ, Module.Finite C (F.X i))
    (hQ : ∀ i : ℤ, Module.Finite C (Q.X i)) (hf : QuasiIso f) :
    QuasiIso ((completedConstantMapComplex c hc).map f) := by
  let := hc
  let F' : CochainComplex (FGModuleCat.{u + 1} C) ℤ :=
    F.liftObjectProperty (ModuleCat.isFG C) hF
  let Q' : CochainComplex (FGModuleCat.{u + 1} C) ℤ :=
    Q.liftObjectProperty (ModuleCat.isFG C) hQ
  let f' : F' ⟶ Q' := { f i := ObjectProperty.homMk (f.f i) }
  have : QuasiIso f' :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f'
      (forget₂ (FGModuleCat.{u + 1} C) (ModuleCat.{u + 1} C))).1 hf
  let c' : FGModuleCat.{u + 1} C ⥤ D := (ModuleCat.isFG C).ι ⋙ c
  have : PreservesFiniteLimits c' := inferInstanceAs
    (PreservesFiniteLimits ((completedConstantFiniteModules C).ι ⋙ c))
  have : PreservesFiniteColimits c' := inferInstanceAs
    (PreservesFiniteColimits ((completedConstantFiniteModules C).ι ⋙ c))
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f' c'

private noncomputable def completedConstant_quotientMap
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) {m n : ℕᵒᵖ} (g : m ⟶ n) :
    completedConstantQuotient X I R β m ⟶ completedConstantQuotient X I R β n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (completedConstantQuotient X I R β m).val.obj U)
        (Y := (completedConstantQuotient X I R β n).val.obj U)
        { toFun := fun x ↦ ((adicLisseRingSystem X I).map g).hom.app U x
          map_add' := map_add _
          map_smul' := by
            intro r x
            change ((adicLisseRingSystem X I).map g).hom.app U
                ((β ≫ limit.π (adicLisseRingSystem X I) m).hom.app U r *
                  (show ((adicLisseRingSystem X I).obj m).obj.obj U from x)) =
              (β ≫ limit.π (adicLisseRingSystem X I) n).hom.app U r *
                ((adicLisseRingSystem X I).map g).hom.app U x
            rw [map_mul]
            congr 1
            exact RingHom.congr_fun
              (congrArg (fun k ↦ (k.hom.app U).hom) (show
                (β ≫ limit.π (adicLisseRingSystem X I) m) ≫
                  (adicLisseRingSystem X I).map g =
                  β ≫ limit.π (adicLisseRingSystem X I) n by
                    rw [Category.assoc, limit.w])) (show R.obj.obj U from r) }
      naturality := by
        intro U V f
        ext x
        exact ConcreteCategory.congr_hom
          (((adicLisseRingSystem X I).map g).hom.naturality f) x }

private noncomputable def completedConstant_quotients
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) : CompletedConstantQuotientTower X I R β where
  diagram :=
    { obj := completedConstantQuotient X I R β
      map := completedConstant_quotientMap X I R β
      map_id := by
        intro n
        ext U x
        change ((adicLisseRingSystem X I).map (𝟙 n)).hom.app U x = x
        exact RingHom.congr_fun
          (congrArg (fun k ↦ (k.hom.app U).hom) ((adicLisseRingSystem X I).map_id n)) x
      map_comp := by
        intro m n p f g
        ext U x
        change ((adicLisseRingSystem X I).map (f ≫ g)).hom.app U x =
          ((adicLisseRingSystem X I).map g).hom.app U
            (((adicLisseRingSystem X I).map f).hom.app U x)
        exact RingHom.congr_fun
          (congrArg (fun k ↦ (k.hom.app U).hom) ((adicLisseRingSystem X I).map_comp f g)) x }
  level _ := rfl
  transition _ _ _ _ _ := rfl

private theorem completedConstant_comparisons
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    CompletedConstantReductionComparisons X I R β c hc h := by
  let := AdicCompletion.isNoetherianRing I
  let P := completedConstant_quotients X I R β
  obtain ⟨L⟩ := completed_constant_derived_tensor_tower X R P.diagram
  obtain ⟨T, hk, ⟨eT⟩⟩ :=
    completed_constant_resolution_tensor_calculation X I d R β c hc e h P
  let U := SheafOfModules.restrictScalars ((adicLisseForget X).map β)
  let B := (adicLisseForget X).obj R
  let H := (adicLisseForget X).obj (adicLisseCompletedRing X I)
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf B) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf H))
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf B) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf H))
  have : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf B)
  have : PreservesFiniteColimits U :=
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf B)
  have := d.exact_finite.1
  have := d.exact_finite.2
  have hlim : PreservesFiniteLimits
      (((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
        completedConstantRealization X I d.scalar) ⋙ U) := inferInstance
  have hcolim : PreservesFiniteColimits
      (((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
        completedConstantRealization X I d.scalar) ⋙ U) := inferInstance
  have : PreservesFiniteLimits
      ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
        completedConstantRealization X I d.scalar ⋙
          SheafOfModules.restrictScalars ((adicLisseForget X).map β)) := hlim
  have : PreservesFiniteColimits
      ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
        completedConstantRealization X I d.scalar ⋙
          SheafOfModules.restrictScalars ((adicLisseForget X).map β)) := hcolim
  have : PreservesFiniteLimits ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙ c) :=
    preservesFiniteLimits_of_natIso
      (Functor.isoWhiskerLeft (completedConstantFiniteModules (AdicCompletion I A)).ι e).symm
  have : PreservesFiniteColimits ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙ c) :=
    preservesFiniteColimits_of_natIso
      (Functor.isoWhiskerLeft (completedConstantFiniteModules (AdicCompletion I A)).ι e).symm
  have hq (z : (completedConstantResolutions (AdicCompletion I A)).FullSubcategory) :=
    completedConstant_finite_quasiIso c hc z.obj.hom
      (fun i ↦ (z.property.2.2.1 i).1) z.property.1.1 z.property.2.1
  refine ⟨fun Q hQ ↦ completedConstant_exists_resolution Q hQ, P, L, T, ⟨?_⟩⟩
  let r := (completedConstantResolutions (AdicCompletion I A)).ι
  let mc := completedConstantMapComplex c hc
  let q := completedConstantQ (completedConstantModules X R)
  let a : r ⋙ Arrow.leftFunc ⋙ mc ⋙ q ⟶ r ⋙ Arrow.rightFunc ⋙ mc ⋙ q :=
    Functor.whiskerLeft r (Functor.whiskerRight Arrow.leftToRight (mc ⋙ q))
  have (z : (completedConstantResolutions (AdicCompletion I A)).FullSubcategory) :
      IsIso (a.app z) := by
    change IsIso (q.map (mc.map z.obj.hom))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hq z)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  let ε : r ⋙ Arrow.leftFunc ⋙ mc ⋙ q ⋙ L.functor ⟶
      r ⋙ Arrow.leftFunc ⋙ mc ⋙ completedConstantTensorTower X R P.diagram :=
    Functor.whiskerLeft (r ⋙ Arrow.leftFunc ⋙ mc) L.counit
  have (z : (completedConstantResolutions (AdicCompletion I A)).FullSubcategory) :
      IsIso (ε.app z) := L.computes _ (hk z)
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  exact Functor.isoWhiskerRight (asIso a).symm L.functor ≪≫ asIso ε ≪≫ eT

private theorem completedConstant_scalar_exists
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    ∃ φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I,
      ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom) := by
  let c := constantSheaf (ProEt.topology X) CommRingCat.{u + 1}
  let π : (Functor.const ℕᵒᵖ).obj (adicLisseConstantRing X (AdicCompletion I A)) ⟶
      adicLisseRingSystem X I := NatTrans.ofOpSequence
    (fun n ↦ c.map (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (fun n ↦ by
      simp only [Functor.const_obj_map, adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (congrArg c.map (completedConstant_eval_step I n)).symm.trans
        (c.map_comp _ _))
  exact ⟨limit.lift _ ⟨_, π⟩, fun n ↦ limit.lift_π _ _⟩

private theorem completedConstant_pullback_iso
    (X T : Scheme.{u}) (f : X ⟶ T) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hfinite : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    ∃ β : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (adicLisseCompletedRing T I) ⟶ adicLisseCompletedRing X I,
      IsIso β ∧ ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem X I) (op n) =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (adicLisseRingSystem T I) (op n)) ≫
            proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (A ⧸ I ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)))
  let e (Z : Scheme.{u}) : adicLisseRingSystem Z I ≅ proEtaleCoefficientTower Z Q := by
    let a : adicLisseRingSystem Z I ⟶ proEtaleCoefficientTower Z Q :=
      NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (fun n ↦ by
        simp [adicLisseRingSystem, proEtaleCoefficientTower, Q])
    have (n : ℕᵒᵖ) : IsIso (a.app n) := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso a := NatIso.isIso_of_isIso_app a
    exact asIso a
  have (n : ℕᵒᵖ) : Finite (Q.obj n) := hfinite n.unop
  have : IsIso (proEtaleProfiniteComparison f Q) :=
    (proEtale_profinite_coefficient_inverse_image Q).2.1 X T f
  let F := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let β := F.map (lim.mapIso (e T)).hom ≫ proEtaleProfiniteComparison f Q ≫
    (lim.mapIso (e X)).inv
  refine ⟨β, inferInstance, ?_⟩
  intro n
  dsimp only [β]
  simp only [Category.assoc, Functor.mapIso_inv]
  change F.map (lim.mapIso (e T)).hom ≫ proEtaleProfiniteComparison f Q ≫
    limMap (e X).inv ≫ limit.π (adicLisseRingSystem X I) (op n) = _
  rw [limMap_π]
  rw [← Category.assoc (proEtaleProfiniteComparison f Q)]
  rw [(proEtale_profinite_coefficient_inverse_image Q).2.2.1 X T f (op n)]
  have hinv : (e X).inv.app (op n) = 𝟙 _ := by
    simp [e]
    rfl
  simp only [hinv, Category.comp_id]
  change F.map (limMap (e T).hom) ≫
    F.map (limit.π (proEtaleCoefficientTower T Q) (op n)) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ I ^ (n + 1))) = _
  rw [← Category.assoc, ← F.map_comp, limMap_π]
  have hhom : (e T).hom.app (op n) = 𝟙 _ := rfl
  rw [hhom, Category.comp_id]


/-- Completed constant realization is exact on finite C-modules, is adic lisse of
finite type, and commutes with derived finite reductions, naturally and compatibly
with all quotient maps, both over H and over B = u⁻¹ H_T. The map B → H is specified
by its finite projections; no preservation of an infinite limit by u⁻¹ is assumed.
Source: Stacks Project, Tags 09BT, 09BV, 093J--093M, 0912, and 00MB.
Proof: form the scalar map from the compatible evaluation cone. The module-level
completion calculation supplies its exact finite realization and local lisse models.
Noetherian pseudo-coherence represents every bounded finite complex by a
bounded-above finite-free complex; projectivity lifts the derived isomorphism to
a quasi-isomorphism of complexes. Lift both complexes to the abelian category of
finite modules: exactness of finite realization preserves that quasi-isomorphism,
as does scalar restriction. On the category of resolutions, invert its localized
natural transformation, apply the derived tensor-tower functor, and compose with
its K-flat counit and the finite-free tensor calculation. This gives the entire
quotient diagram, with every transition retained. For relative coefficients, use
the proved profinite comparison for the finite quotient rings, transport along the
identity-component isomorphism of the two tower presentations, and check the
finite projections. This coefficient map is an isomorphism; the same finite-free
calculation applies to scalar restriction along it. No preservation of arbitrary
infinite limits by inverse image is required.
(blueprint: lem-weil-pbc-completed-constant-finite-complex-realization). -/
theorem completed_constant_finite_complex_realization (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hfinite : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    ∃ (d : CompletedConstantModuleRealization X I)
      (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive),
      CompletedConstantReductionComparisons X I (adicLisseCompletedRing X I) (𝟙 _)
        (completedConstantRealization X I d.scalar) d.additive h ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T),
        ∃ β : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
            (adicLisseCompletedRing T I) ⟶ adicLisseCompletedRing X I,
          (∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem X I) (op n) =
            (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
                (limit.π (adicLisseRingSystem T I) (op n)) ≫
              proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
                (CommRingCat.of (A ⧸ I ^ (n + 1)))) ∧
          ∃ hc : (completedConstantRealization X I d.scalar ⋙
            SheafOfModules.restrictScalars ((adicLisseForget X).map β)).Additive,
            CompletedConstantReductionComparisons X I
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
                (adicLisseCompletedRing T I)) β
              (completedConstantRealization X I d.scalar ⋙
                SheafOfModules.restrictScalars ((adicLisseForget X).map β)) hc h := by
  obtain ⟨φ, hφ⟩ := completedConstant_scalar_exists X I
  obtain ⟨d, _⟩ := completed_constant_module_model X I φ hφ
  let h (n : ℕ) : (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive :=
    CompletedConstantReduction.constant_additive X _
  have habs := completedConstant_comparisons X I d (adicLisseCompletedRing X I)
    (𝟙 _) (completedConstantRealization X I d.scalar) d.additive (Iso.refl _) h
  refine ⟨d, h, habs, ?_⟩
  intro T f
  obtain ⟨β, hβ, hπ⟩ := completedConstant_pullback_iso X T f I hfinite
  let := hβ
  let := d.additive
  let hc : (completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β)).Additive := inferInstance
  exact ⟨β, hπ, hc, completedConstant_comparisons X I d _ β _ hc (Iso.refl _) h⟩
end AlgebraicGeometry.Scheme
