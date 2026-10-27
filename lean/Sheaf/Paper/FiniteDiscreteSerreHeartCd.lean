/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
import all Sheaf.Paper.FiniteDiscreteEncodingConstructibility
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf

/-! # Finite discrete coefficients and the torsion étale bound -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

private theorem ordinary_constructible_iff (A : Type u) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ordinaryConstructible A T M ↔ IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [ordinaryConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A]

private def sectionsIso (X : Scheme.{u}) (e : Encoding A X) :
    condensedModuleSections (coefficient A) X ≅
      (e.ordinary.trans e.fixed).functor ⋙
        globalSectionsFunctor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X ⋙
          forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1} := by
  rw [show (e.ordinary.trans e.fixed).functor = e.ordinary.functor ⋙ e.fixed.functor from rfl,
    e.ordinary_functor, e.fixed_functor]
  exact NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)

private theorem serre_etaleOrigin (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (e : Encoding A X) (M : Internal A X)
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible (coefficient A) X) M) :
    etaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
      ((e.ordinary.trans e.fixed).functor.obj M) := by
  let E := e.ordinary.trans e.fixed
  let P := IsConstantModelConstructible (coefficient A) X
  let Q := (etaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).inverseImage E.functor
  apply hM Q ?_ inferInstance inferInstance inferInstance inferInstance
    (fun _ ↦ inferInstance)
  intro N hN
  obtain ⟨F, _, ⟨i⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1} A)
    ((ordinary_constructible_iff A X _).mp ((constructible_comparison A X e N).mp hN))
  exact ⟨F, ⟨i⟩⟩

omit [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] in
private theorem etale_sections_isZero
    (ℓ : ℕ) [Fact ℓ.Prime] (htors : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (X : Scheme.{u}) (d : ℕ) (hcd : X.HasTorsionEtaleCohomologicalDimensionLE d)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (q : ℕ) (hq : d < q) :
    IsZero (((Etale.sectionsFunctor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).rightDerived q).obj
      F) := by
  let R := ULift.{u + 1} A
  let U := forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}
  let FAb := (sheafCompose X.smallEtaleTopology U).obj F
  obtain ⟨n, hn⟩ := htors
  have hz : (ℓ ^ n : R) = 0 := by
    apply ULift.ext
    change (ℓ ^ n : A) = 0
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn 1
  have hF : FAb.IsTorsion := by
    apply Scheme.isTorsion_of_nsmul_id_eq_zero (pow_pos (Fact.out : ℓ.Prime).pos n)
    ext V s
    change (ℓ ^ n) • (s : F.obj.obj V) = 0
    have hs (t : F.obj.obj V) : (ℓ ^ n) • t = 0 := by
      rw [← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hz, zero_smul]
    exact hs s
  have hsub := hcd FAb hF q hq
  let := hsub
  have hzAb : IsZero ((Etale.cohomology Ab.{u + 1} X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj FAb)) :=
    AddCommGrpCat.isZero_of_subsingleton _
  let e := (Scheme.nonempty_etaleModuleCohomology_forgetIso X R q).some
  have hm := hzAb.of_iso (e.app F)
  have hzM : IsZero ((Etale.cohomology (ModuleCat.{u + 1} R) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero hm)
  let Γ := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let ev := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    (Opposite.op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))
  have : ev.Additive := ⟨by intros; rfl⟩
  have hzΓ : IsZero ((Γ.rightDerived q).obj F) := hzM.of_iso
    (Γ.homologyRightDerivedFunctorObjSingleFunctorIso F q).symm
  exact hzΓ.of_iso (Functor.rightDerivedObjIsoOfIso
    (Sheaf.ΓNatIsoSheafSections _ _ (MorphismProperty.Over.mkIdTerminal @Etale X)).symm q F)

/-- Finite discrete weak-Serre heart modules have the given torsion étale bound.
Source: Stacks Tags 03SA(3), 099Y, finite discrete coefficient encoding.
(blueprint: lem-sfb-finite-discrete-serre-heart-cd)

Proof: the normalized encoding identifies constructible generators with ordinary
constructible sheaves. These are of étale origin, whose essential image is closed
under kernels, cokernels, extensions and coproducts. Hence the encoded module has
an étale antecedent. The given power of ℓ kills its underlying abelian sheaf, so
the assumed torsion dimension kills its étale cohomology above d. Étale/pro-étale
sections comparison, the encoding equivalence and exact coefficient forgetting
transport this vanishing to the displayed right-derived functor. -/
theorem finiteDiscrete_serreHeart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime] (htors : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : X.HasTorsionEtaleCohomologicalDimensionLE d)
    (M : Internal A X)
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible (coefficient A) X) M)
    (q : ℕ) (hq : d < q) :
    IsZero (((condensedModuleSections (coefficient A) X).rightDerived q).obj M) := by
  let e := (encoding_exists A X).some
  let E := e.ordinary.trans e.fixed
  let Γ : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} A) :=
    globalSectionsFunctor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let U : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤ Ab.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}
  have : PreservesColimitsOfSize.{0, 0} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} (ULift.{u + 1} A)
  have : PreservesFiniteColimits U :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} U
  have : E.functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  obtain ⟨F, ⟨i⟩⟩ := serre_etaleOrigin A X e M hM
  have hz := isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X F q
    (etale_sections_isZero A ℓ htors X d hcd F q hq)
  have hz' : IsZero ((Γ.rightDerived q).obj (E.functor.obj M)) :=
    hz.of_iso ((Γ.rightDerived q).mapIso i.symm)
  have hz'' : IsZero (U.obj ((Γ.rightDerived q).obj (E.functor.obj M))) :=
    U.map_isZero hz'
  let j := Functor.rightDerivedObjIsoOfIso (sectionsIso A X e) q M
  let k : ((E.functor ⋙ (Γ ⋙ U)).rightDerived q).obj M ≅
      ((Γ ⋙ U).rightDerived q).obj (E.functor.obj M) :=
    Functor.compRightDerivedObjIso E.functor (Γ ⋙ U)
      (fun I _ ↦ Functor.rightAcyclic_of_injective (F := Γ ⋙ U) (E.functor.obj I)) q M
  let l : ((Γ ⋙ U).rightDerived q).obj (E.functor.obj M) ≅
      U.obj ((Γ.rightDerived q).obj (E.functor.obj M)) :=
    Functor.rightDerivedCompObjIso Γ U q (E.functor.obj M)
  exact hz''.of_iso (j ≪≫ k ≪≫ l)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
