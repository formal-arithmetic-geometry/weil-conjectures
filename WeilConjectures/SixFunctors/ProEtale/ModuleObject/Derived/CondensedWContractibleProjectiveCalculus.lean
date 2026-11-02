/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ContractibleLisseEvaluation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentPointMonoidalFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentDerivedSymmetry
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentLisseEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentFinalScalarComparison
import WeilConjectures.CategoryTheory.Cochain.CochainDerivedAdjunction
import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedKFlatWord.RingedKFlatWordComparisonDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ProfiniteCoefficientSliceBaseChange
import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.SixFunctors.ExactRightDerivedAdjointKFlatRepresentative
import all WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Bounded-projective calculus for condensed sheaves

Source: Hemo--Richarz--Scholbach, Definition 3.3, Lemma 4.1(1)--(2), Remark 3.2,
and Theorem 4.13 (blueprint: lem-zl-condensed-wcontractible-projective-calculus).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj ZeroObject TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (T : Scheme.{u})
/-- Pull a scalar section back along p_T and evaluate it on T. The source section is
represented by the homomorphism Z to Λ(*) sending n to n*r; the unit of sheafification
provides 1 on T. This is the underlying function of the canonical map R to B.
Source: HRS (3.1)--(3.2), Remark 3.2
(blueprint: lem-zl-condensed-wcontractible-projective-calculus). -/
def projectiveCalculusScalarSection (r : condensedScalarRing Λ.X) :
    Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
      (Scheme.ProEt.mk (𝟙 T)) :=
  affineScalarSection Λ.X T r


/-- The section ring B, as a specialization of the published evaluation model.
Source: HRS Lemma 4.1 (blueprint: lem-zl-condensed-wcontractible-projective-calculus). -/
abbrev projectiveCalculusRing : CommRingCat.{u + 1} :=
  Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ.X T) (Scheme.ProEt.mk (𝟙 T))

/-- The constant-section realization F_T, with no independently chosen functor.
Source: HRS (3.2) (blueprint: lem-zl-condensed-wcontractible-projective-calculus). -/
abbrev projectiveCalculusRealization :=
  Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
    (Scheme.ProEt.mk (𝟙 T))
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T)

/-- The ordinary derived module category on T, with its existing derived tensor.
Source: HRS Section 3 (blueprint: lem-zl-condensed-wcontractible-projective-calculus). -/
abbrev projectiveCalculusCategory :=
  Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)

-- The helpers keep the localization universe independent of the ring universe.
private theorem perfect_shift {R : Type (u + 1)} [CommRing R]
    {Q : DerivedCategory (ModuleCat.{u + 1} R)}
    (hQ : DerivedCategory.IsPerfectRingComplex Q) (m : ℤ) :
    DerivedCategory.IsPerfectRingComplex (Q⟦m⟧) := by
  obtain ⟨q, a, b, _, _, hp, ⟨e⟩⟩ := hQ
  have := q.isStrictlyGE_shift a m (a - m) (by omega)
  have := q.isStrictlyLE_shift b m (b - m) (by omega)
  refine ⟨q⟦m⟧, a - m, b - m, inferInstance, inferInstance, fun i ↦ hp (i + m), ?_⟩
  exact ⟨(shiftFunctor _ m).mapIso e ≪≫ ((DerivedCategory.Q.commShiftIso m).app q).symm⟩

private theorem perfect_scalar_extension {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (σ : R →+* S) {P : DerivedCategory (ModuleCat.{u + 1} R)}
    (hP : DerivedCategory.IsPerfectRingComplex P) :
    DerivedCategory.IsPerfectRingComplex
      ((RingDerivedScalarExtension.moduleDerivedExtension σ).obj P) := by
  obtain ⟨q, a, b, _, _, hq, ⟨e⟩⟩ := hP
  let E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S :=
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} σ
  let U : ModuleCat.{u + 1} S ⥤ ModuleCat.{u + 1} R :=
    ModuleCat.restrictScalars.{u + 1} σ
  let L := RingDerivedScalarExtension.moduleDerivedExtension σ
  have : U.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1} σ).isRightAdjoint
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, u + 1, u + 1} σ).isLeftAdjoint
  have := ModuleCat.hasFunctorialFlatResolution_sameUniverse R
  have := ModuleCat.extendScalars_preservesKFlatQuasiIso σ
  have : AB5OfSize.{0, 0} (ModuleCat.{u + 1} R) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u + 1} R) := inferInstance
  have hk : (HomologicalComplex.quasiIso (ModuleCat.{u + 1} R) (.up ℤ)).kFlat q := by
    apply CochainComplex.kFlat_of_bounded_of_flat q a b
    intro i
    have := (hq i).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  let ad : L ⊣ U.mapDerivedCategory :=
    ConstantScalarRealization.moduleDerivedAdjunction σ
  let adj : E ⊣ U := ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1} σ
  let t := (ad.homEquiv _ _).symm
    (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app q) ≫
      U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj q))
  have : IsIso t := Adjunction.isIso_cochainTranspose_of_kFlat E U adj ad q hk
  let q' : CochainComplex (ModuleCat.{u + 1} S) ℤ :=
    (E.mapHomologicalComplex (.up ℤ)).obj q
  have hqa : q'.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
    fun i hi ↦ E.map_isZero (q.isZero_of_isStrictlyGE a i hi)
  have hqb : q'.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    fun i hi ↦ E.map_isZero (q.isZero_of_isStrictlyLE b i hi)
  refine ⟨q', a, b, hqa, hqb, ?_, ⟨L.mapIso e ≪≫ asIso t⟩⟩
  intro i
  let := σ.toAlgebra
  have := (hq i).1
  have := (hq i).2
  exact ⟨inferInstanceAs (Module.Projective S (S ⊗[R] q.X i)),
    inferInstanceAs (Module.Finite S (S ⊗[R] q.X i))⟩

private theorem cone_terms {R : Type (u + 1)} [CommRing R]
    {q q' : CochainComplex (ModuleCat.{u + 1} R) ℤ} (v : q ⟶ q')
    (hq : ∀ i, Module.Projective R (q.X i) ∧ Module.Finite R (q.X i))
    (hq' : ∀ i, Module.Projective R (q'.X i) ∧ Module.Finite R (q'.X i)) (i : ℤ) :
    Module.Projective R ((CochainComplex.mappingCone v).X i) ∧
      Module.Finite R ((CochainComplex.mappingCone v).X i) := by
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod v i (i + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd (q.X (i + 1)) (q'.X i)
  have := (hq (i + 1)).1
  have := (hq (i + 1)).2
  have := (hq' i).1
  have := (hq' i).2
  exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
    Module.Finite.equiv e.toLinearEquiv.symm⟩

/-- Bounded finite-projective cone and scalar calculus on a w-contractible affine.
Source: HRS Definition 3.3, Lemma 4.1(1)--(2), Remark 3.2 and Theorem 4.13;
Stacks Tags 00NX, 066R, 06YQ, 06YY
(blueprint: lem-zl-condensed-wcontractible-projective-calculus).

Proof plan, following the six steps of the node:
1. Use lem-zl-condensed-wcontractible-lisse-evaluation: F is exact, fully faithful,
   and identifies perfect B-complexes with dualizable objects. Fullness after choosing
   perfect models gives the assertion on arrows, including its commuting square.
2. Transport f along the specified representative isomorphisms. Bounded-above
   projectives are K-projective (lem-pc-ring-derived-map-representative), so choose a
   chain map v. Its mapping cone has q'^n plus q^(n+1), with differential
   (y,x) mapping to (d y + v x,-d x). It is bounded, and the two summands are finite
   projective: use their finite generators and lift on each summand separately.
3. Exactness sends the cone triangle to a distinguished triangle. TR3 and
   lem-sf-triangle-morphism-iso identify any other cone with its image. The image is
   dualizable by step 1. Zero and shifts have bounded finite-projective representatives.
   Transport evaluation and coevaluation along an isomorphism; the triangle identities
   follow by cancelling the two inverse maps.
4. Mathlib's tensor-product instances preserve finite generation and projectivity
   under arbitrary scalar extension. Projective modules are flat; no flatness of B/R
   is required.
5. Bounded flat complexes are K-flat. The derived-adjunction representative theorem
   lem-sfb-exact-right-adjoint-kflat-representative identifies the specified left adjoint
   with termwise scalar extension on this representative. The image has the same degree
   bounds and finite-projective terms, hence is perfect.
6. The scalar comparison supplied by the evaluation theorem is natural on all complexes.
   The scalar-normalized component comparison identifies its map R to B with the explicit
   pullback section projectiveCalculusScalarSection. Restrict the natural isomorphism to
   perfect objects and use steps 1 and 5 to obtain dualizability of L_T(P).
-/
theorem condensed_wcontractible_projective_calculus
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (T : Scheme.{u})
    [IsAffine T] [IsWContractibleRing Γ(T, ⊤)] :
    (∀ (Q Q' : DerivedCategory (ModuleCat.{u + 1} (projectiveCalculusRing Λ T)))
        (f : Q ⟶ Q'),
      DerivedCategory.IsPerfectRingComplex Q → DerivedCategory.IsPerfectRingComplex Q' →
      ∀ (q q' : CochainComplex (ModuleCat.{u + 1} (projectiveCalculusRing Λ T)) ℤ)
        (a b a' b' : ℤ),
        q.IsStrictlyGE a → q.IsStrictlyLE b →
        q'.IsStrictlyGE a' → q'.IsStrictlyLE b' →
        (∀ i : ℤ, Module.Projective (projectiveCalculusRing Λ T) (q.X i) ∧
          Module.Finite (projectiveCalculusRing Λ T) (q.X i)) →
        (∀ i : ℤ, Module.Projective (projectiveCalculusRing Λ T) (q'.X i) ∧
          Module.Finite (projectiveCalculusRing Λ T) (q'.X i)) →
        ∀ (e : DerivedCategory.Q.obj q ≅ Q) (e' : DerivedCategory.Q.obj q' ≅ Q'),
        ∃ v : q ⟶ q',
          DerivedCategory.Q.map v ≫ e'.hom = e.hom ≫ f ∧
          (∃ c d : ℤ, (CochainComplex.mappingCone v).IsStrictlyGE c ∧
            (CochainComplex.mappingCone v).IsStrictlyLE d ∧
            ∀ i : ℤ,
              Module.Projective (projectiveCalculusRing Λ T)
                ((CochainComplex.mappingCone v).X i) ∧
              Module.Finite (projectiveCalculusRing Λ T)
                ((CochainComplex.mappingCone v).X i)) ∧
          (∀ i : ℤ, Nonempty ((CochainComplex.mappingCone v).X i ≅
            q'.X i ⊞ q.X (i + 1))) ∧
          ∀ (K : projectiveCalculusCategory Λ T)
            (g : (projectiveCalculusRealization Λ T).obj Q' ⟶ K)
            (h : K ⟶ ((projectiveCalculusRealization Λ T).obj Q) ⟦(1 : ℤ)⟧),
            Triangle.mk ((projectiveCalculusRealization Λ T).map f) g h ∈
              distTriang _ →
            Nonempty (K ≅ (projectiveCalculusRealization Λ T).obj
              (DerivedCategory.Q.obj (CochainComplex.mappingCone v))) ∧ IsDualizable K) ∧
    IsDualizable ((projectiveCalculusRealization Λ T).obj 0) ∧
    (∀ (Q : DerivedCategory (ModuleCat.{u + 1} (projectiveCalculusRing Λ T)))
        (m : ℤ), DerivedCategory.IsPerfectRingComplex Q →
      IsDualizable (((projectiveCalculusRealization Λ T).obj Q) ⟦m⟧)) ∧
    (∀ (K K' : projectiveCalculusCategory Λ T),
      Nonempty (K ≅ K') → IsDualizable K → IsDualizable K') ∧
    (∀ (K K' : projectiveCalculusCategory Λ T) (u : K ⟶ K'),
      IsDualizable K → IsDualizable K' →
      ∃ (Q Q' : DerivedCategory (ModuleCat.{u + 1} (projectiveCalculusRing Λ T)))
        (f : Q ⟶ Q'),
        DerivedCategory.IsPerfectRingComplex Q ∧ DerivedCategory.IsPerfectRingComplex Q' ∧
        ∃ (e : (projectiveCalculusRealization Λ T).obj Q ≅ K)
          (e' : (projectiveCalculusRealization Λ T).obj Q' ≅ K'),
          (projectiveCalculusRealization Λ T).map f ≫ e'.hom = e.hom ≫ u) ∧
    ∃ σ : condensedScalarRing Λ.X →+* projectiveCalculusRing Λ T,
      (∀ r : condensedScalarRing Λ.X, σ r = projectiveCalculusScalarSection Λ T r) ∧
      (∀ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
        DerivedCategory.IsPerfectRingComplex P →
        DerivedCategory.IsPerfectRingComplex
          ((RingDerivedScalarExtension.moduleDerivedExtension σ).obj P) ∧
        IsDualizable ((condensedScalarRealization Λ.X T).obj P)) ∧
      Nonempty
        (ObjectProperty.ι (DerivedCategory.IsPerfectRingComplex
            (R := condensedScalarRing Λ.X)) ⋙ condensedScalarRealization Λ.X T ≅
          ObjectProperty.ι (DerivedCategory.IsPerfectRingComplex
            (R := condensedScalarRing Λ.X)) ⋙
            RingDerivedScalarExtension.moduleDerivedExtension σ ⋙
              projectiveCalculusRealization Λ T) := by
  let F := projectiveCalculusRealization Λ T
  obtain ⟨heval, hcomponent⟩ := (condensed_wcontractible_lisse_evaluation Λ).1 T
  obtain ⟨hff, ⟨hs, ht⟩, _, e, ⟨ef⟩, _⟩ := heval
  let := hs
  let := ht
  let := hff.some.full
  have hdual (Q : DerivedCategory (ModuleCat.{u + 1} (projectiveCalculusRing Λ T)))
      (hQ : DerivedCategory.IsPerfectRingComplex Q) : IsDualizable (F.obj Q) := by
    exact IsDualizable.of_iso (ef.app ⟨Q, hQ⟩) (e.functor.obj ⟨Q, hQ⟩).property
  have hmodels (K : projectiveCalculusCategory Λ T) (hK : IsDualizable K) :
      ∃ Q, DerivedCategory.IsPerfectRingComplex Q ∧ Nonempty (F.obj Q ≅ K) := by
    let X : (Evaluation.lisse (Scheme.ProEt.topology T)
      (condensedRingObj Λ.X T)).FullSubcategory := ⟨K, hK⟩
    exact ⟨(e.inverse.obj X).obj, (e.inverse.obj X).property,
      ⟨(ef.app (e.inverse.obj X)).symm ≪≫
        (Evaluation.lisse _ _).ι.mapIso (e.counitIso.app X)⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q Q' f _ _ q q' a b a' b' hqa hqb hq'a hq'b hq hq' eq eq'
    have : ∀ i, Projective (q.X i) := fun i ↦ by
      have := (hq i).1
      exact ModuleCat.projective_of_categoryTheory_projective _
    have : q.IsKProjective := CochainComplex.isKProjective_of_projective q b
    obtain ⟨v, hv⟩ := CochainComplex.IsKProjective.exists_Q_map_eq q q'
      (eq.hom ≫ f ≫ eq'.inv)
    have hv' : DerivedCategory.Q.map v ≫ eq'.hom = eq.hom ≫ f := by
      rw [hv]
      simp
    have hca : (CochainComplex.mappingCone v).IsStrictlyGE (min (a - 1) a') :=
      CochainComplex.isStrictlyGE_mappingCone v a a' _ (by omega) (by omega)
    have hcb : (CochainComplex.mappingCone v).IsStrictlyLE (max (b - 1) b') := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨q.isZero_of_isStrictlyLE b _ (by omega),
        q'.isZero_of_isStrictlyLE b' _ (by omega)⟩
    have hc := cone_terms v hq hq'
    refine ⟨v, hv', ⟨min (a - 1) a', max (b - 1) b', hca, hcb, hc⟩, ?_, ?_⟩
    · intro i
      exact ⟨(HomologicalComplex.homotopyCofiber.XIsoBiprod v i (i + 1) rfl) ≪≫
        biprod.braiding _ _⟩
    · intro K g h htri
      obtain ⟨et, _⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
        (F.map_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished v)) htri
        (Arrow.isoMk (F.mapIso eq) (F.mapIso eq') (by
          change F.map eq.hom ≫ F.map f = F.map (DerivedCategory.Q.map v) ≫ F.map eq'.hom
          simpa only [← F.map_comp] using (congrArg F.map hv').symm))
      let ec := Triangle.π₃.mapIso et
      exact ⟨⟨ec.symm⟩, IsDualizable.of_iso ec
        (hdual _ ⟨_, _, _, hca, hcb, hc, ⟨Iso.refl _⟩⟩)⟩
  · apply hdual
    refine ⟨0, 0, 0, inferInstance, inferInstance, ?_, ?_⟩
    · intro i
      have hz : IsZero ((0 : CochainComplex
          (ModuleCat.{u + 1} (projectiveCalculusRing Λ T)) ℤ).X i) :=
        (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
      have := ModuleCat.subsingleton_of_isZero hz
      exact ⟨inferInstance, inferInstance⟩
    · exact ⟨(Functor.mapZeroObject DerivedCategory.Q).symm⟩
  · intro Q m hQ
    exact IsDualizable.of_iso ((F.commShiftIso m).app Q) (hdual _ (perfect_shift hQ m))
  · rintro K K' ⟨i⟩ hK
    exact IsDualizable.of_iso i hK
  · intro K K' u hK hK'
    obtain ⟨Q, hQ, ⟨i⟩⟩ := hmodels K hK
    obtain ⟨Q', hQ', ⟨i'⟩⟩ := hmodels K' hK'
    refine ⟨Q, Q', F.preimage (i.hom ≫ u ≫ i'.inv), hQ, hQ', i, i', ?_⟩
    change F.map (F.preimage (i.hom ≫ u ≫ i'.inv)) ≫ i'.hom = i.hom ≫ u
    rw [F.map_preimage]
    simp
  · obtain ⟨hct, hcb, hlim, hcolim, α, _, hcomp⟩ := hcomponent
    let := hct
    let := hcb
    let := hlim
    let := hcolim
    obtain ⟨_, _, _, _, a, ha, _, _, ⟨i⟩⟩ := hcomp
    let σ := a.hom.hom.comp (profiniteScalarMap Λ.X (affineComponentSpace T))
    refine ⟨σ, ha, ?_, ⟨Functor.isoWhiskerLeft (ObjectProperty.ι _) i⟩⟩
    intro P hP
    have hp := perfect_scalar_extension σ hP
    exact ⟨hp, IsDualizable.of_iso (i.app P).symm (hdual _ hp)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
