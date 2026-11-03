/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantCokernel
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-! # Native bounded constructibility under finite encoding

Source: blueprint det-def-sf-operations (vi), Stacks 09AK and 09AL.
(blueprint: lem-sf-native-finite-encoding-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private def encodedRegular (T : Scheme.{u}) (e : Encoding A T) :
    (e.ordinary.functor ⋙ e.fixed.functor).obj
        (Mod.regular (condensedRingObj (coefficient A) T)) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)) := by
  letI := (ordinary_monoidal A T e).some
  letI := (fixed_monoidal A T e).some
  exact (Functor.Monoidal.εIso (e.ordinary.functor ⋙ e.fixed.functor)).symm

private def encodedFree (T : Scheme.{u}) (e : Encoding A T) (n : ℕ) :
    (e.ordinary.functor ⋙ e.fixed.functor).obj
        (Mod.finiteFree (condensedRingObj (coefficient A) T) n) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
        (ModuleCat.of (ULift.{u + 1} A) (Fin n → ULift.{u + 1} A)) := by
  let H := e.ordinary.functor ⋙ e.fixed.functor
  let C := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))
  exact H.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ encodedRegular A T e) ≪≫
    (C.mapBiproduct _).symm ≪≫ C.mapIso (ModuleCat.biproductIsoPi _)

private theorem encodedFP [Finite A] (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T)
    (hM : Mod.IsFinitelyPresented (condensedRingObj (coefficient A) T) M) :
    IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  obtain ⟨n, m, f, ⟨j⟩⟩ := hM
  let H := e.ordinary.functor ⋙ e.fixed.functor
  let P := ModuleCat.of (ULift.{u + 1} A) (Fin m → ULift.{u + 1} A)
  let Q := ModuleCat.of (ULift.{u + 1} A) (Fin n → ULift.{u + 1} A)
  let fm := encodedFree A T e m
  let fn := encodedFree A T e n
  let g := fm.inv ≫ H.map f ≫ fn.hom
  let j' : H.obj M ≅ cokernel g := H.mapIso j ≪≫ PreservesCokernel.iso H f ≪≫
    cokernel.mapIso _ _ fm fn (by simp [g])
  exact isFiniteLocallyConstant_of_iso j'.symm
    (isFiniteLocallyConstant_cokernel_constant T P Q g)
private theorem encodedLFP [Finite A] [DiscreteTopology A] (T : Scheme.{u})
    (e : Encoding A T) (M : Internal A T)
    (hM : IsLocallyFinitelyPresented (condensedRingObj (coefficient A) T) M) :
    IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  obtain ⟨C, hC⟩ := hM
  apply finiteLocallyConstant_of_cover _ C
  intro i
  let eU := (encoding_exists A (C.X i)).some
  exact isFiniteLocallyConstant_of_iso
    (encoding_pullback_fixed A (C.f i) e eU M).some
    (encodedFP A (C.X i) eU _
      ((CondensedRing.isFinitelyPresented_mapMod_iff (coefficient A) (C.f i) M).mp (hC i)))

private theorem encodedConstructible [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T)
    (hM : IsConstructibleModuleObject (condensedRingObj (coefficient A) T) M) :
    IsConstructible (ULift.{u + 1} A)
      ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun i ↦ ?_⟩
  let eU := (encoding_exists A (S.domain i)).some
  exact isFiniteLocallyConstant_of_iso
    (encoding_pullback_fixed A (S.immersion i) e eU M).some
    (encodedLFP A (S.domain i) eU _
      ((CondensedRing.isLocallyFinitelyPresented_mapMod_iff
        (coefficient A) (S.immersion i) M).mp (hS i)))

private theorem encodedConstantFP [Finite A] (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T) (P : ModuleCat.{u + 1} (ULift.{u + 1} A)) [Finite P]
    (j : (e.ordinary.functor ⋙ e.fixed.functor).obj M ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P) :
    Mod.IsFinitelyPresented (condensedRingObj (coefficient A) T) M := by
  let H := e.ordinary.functor ⋙ e.fixed.functor
  let C := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))
  have : Module.FinitePresentation (ULift.{u + 1} A) P :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' (ULift.{u + 1} A) P
  let f' := ModuleCat.ofHom f
  let g' := ModuleCat.ofHom g
  let ec : P ≅ cokernel g' :=
    (ModuleCat.isColimitCokernelCofork g' f' hg hf).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let c := encodedFree A T e
  let d := H.preimage ((c m).hom ≫ C.map g' ≫ (c n).inv)
  refine ⟨n, m, d, ⟨H.preimageIso ?_⟩⟩
  exact j ≪≫ C.mapIso ec ≪≫ PreservesCokernel.iso C g' ≪≫
    cokernel.mapIso _ (H.map d) (c m).symm (c n).symm (by simp [d]) ≪≫
    (PreservesCokernel.iso H d).symm

private theorem encodedEtaleLisseFP [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    [Scheme.IsFiniteLocallyConstantSheaf F]
    (M : Internal A T)
    (j : (e.ordinary.functor ⋙ e.fixed.functor).obj M ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).obj F) :
    IsLocallyFinitelyPresented (condensedRingObj (coefficient A) T) M := by
  classical
  obtain ⟨⟨C₀, hC⟩⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  let C := C₀.nonemptyMembers
  let D : Scheme.Cover.{u} Scheme.proetalePrecoverage T :=
    ⟨C.toPreZeroHypercover, Scheme.etalePrecoverage_le_proetalePrecoverage _ C.mem₀⟩
  refine ⟨D, ?_⟩
  rintro ⟨i, hi⟩
  have hc : ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C₀.f i)).obj F).IsConstant
      (C₀.X i).smallEtaleTopology :=
    (Scheme.isConstant_over_iff_upperStar _ (C₀.etalePrecoverageToEtale i) F).mp (hC i)
  obtain ⟨P, ⟨eP⟩⟩ :=
    (((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (C₀.f i)).obj F).mem_essImage_of_isConstant)
  have : Scheme.IsFiniteSheaf
      ((constantSheaf (C₀.X i).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P) := by
    have := Scheme.IsFiniteSheaf.upperStar (C₀.f i) F
    exact Scheme.IsFiniteSheaf.of_iso eP.symm
  have : Nonempty (C₀.X i) := hi
  have : Module.Finite (ULift.{u + 1} A) P :=
    Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf (Y := C₀.X i) P
  have : Finite P := Module.finite_of_finite (ULift.{u + 1} A)
  let eU := (encoding_exists A (C₀.X i)).some
  apply (CondensedRing.isFinitelyPresented_mapMod_iff (coefficient A) (C₀.f i) M).mpr
  apply encodedConstantFP A (C₀.X i) eU _ P
  exact (encoding_pullback_fixed A (C₀.f i) e eU M).some ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C₀.f i)).mapIso j ≪≫
    (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C₀.f i)).app F ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C₀.X i)).mapIso eP.symm ≪≫
    (comparisonUpperStarConstantSheafIso (ULift.{u + 1} A) (C₀.X i)).app P

private theorem encodedEtaleConstructible [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    [Scheme.IsConstructibleSheaf F]
    (M : Internal A T)
    (j : (e.ordinary.functor ⋙ e.fixed.functor).obj M ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).obj F) :
    IsConstructibleModuleObject (condensedRingObj (coefficient A) T) M := by
  obtain ⟨S, hS⟩ := Scheme.IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} A) ↦ M →ₗ[ULift.{u + 1} A] N)
    (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} A) ↦ M) (F := F)
  refine ⟨S, fun i ↦ ?_⟩
  have := hS i
  let eU := (encoding_exists A (S.domain i)).some
  apply (CondensedRing.isLocallyFinitelyPresented_mapMod_iff
    (coefficient A) (S.immersion i) M).mpr
  apply encodedEtaleLisseFP A (S.domain i) eU
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion i)).obj F)
  exact (encoding_pullback_fixed A (S.immersion i) e eU M).some ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion i)).mapIso j ≪≫
    (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion i)).app F

private theorem encodedConstructibleIff [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T) :
    IsConstructibleModuleObject (condensedRingObj (coefficient A) T) M ↔
      IsConstructible (ULift.{u + 1} A)
        ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  refine ⟨encodedConstructible A T e M, fun h ↦ ?_⟩
  obtain ⟨F, hF, ⟨j⟩⟩ :=
    exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} A) h
  let := hF
  exact encodedEtaleConstructible A T e F M j.symm

/-- The normalized finite section-action encoding preserves and reflects native bounded
constructibility, on every scheme, without a separatedness hypothesis.

Source: blueprint det-def-sf-operations (vi), finite etale-origin comparison;
Stacks 09AK and 09AL (blueprint: lem-sf-native-finite-encoding-constructibility).
Proof: the encoded regular module is the constant free rank-one module. Exactness
carries finite presentations to cokernels of finite constant sheaves. The normalized
pullback comparison applies this observation on covers and strata. Conversely descend
a fixed constructible sheaf to an etale constructible sheaf and trivialize its lisse
strata. On nonempty cover members finite stalks give finite modules, hence finite
presentations; pull these presentations back through the full faithful encoding.
Exact derivation commutes with homology and preserves and reflects cohomological bounds.
The construction also covers the empty scheme and the zero ring. -/
theorem native_boundedConstructible_encoding_iff [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (K : DerivedCategory (Internal A T)) :
    boundedConstructible (condensedRingObj (coefficient A) T) K ↔
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) T (e.fixedDerived.functor.obj K) := by
  let H := e.ordinary.functor ⋙ e.fixed.functor
  rw [← ProEtale.DerivedCategory.boundedConstructibleIntrinsic_eq]
  change (_ ∧ _) ↔ (_ ∧ _)
  refine and_congr
    ⟨H.bounded_mapDerivedCategory_obj, H.bounded_of_bounded_mapDerivedCategory_obj⟩ ?_
  refine forall_congr' fun n ↦ ?_
  exact (encodedConstructibleIff A T e _).trans
    ⟨isConstructible_of_iso ((H.mapDerivedCategoryHomologyFunctorIso n).app K),
      isConstructible_of_iso ((H.mapDerivedCategoryHomologyFunctorIso n).app K).symm⟩


end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
