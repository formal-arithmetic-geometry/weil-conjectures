/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CondensedBridge.CompositionTensorMateData2
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantCokernel
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Module.FinitePresentation

/-! # Intrinsic finite presentations in normalized coefficient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CompositionTensorMate
open FiniteDiscreteOrdinary

-- Prefer the site-size witness whose coefficient universe is fixed by this module.
private local instance (priority := 20000) siteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  WeilConjectures.scalarReductionSiteSmall.{u, u} T

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A]

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private def freeEncoding (T : Scheme.{u}) (e : Encoding A T) (n : ℕ) :
    (e.ordinary.functor ⋙ e.fixed.functor).obj
        (Mod.finiteFree (condensedRingObj (coefficient A) T) n) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
          (ModuleCat.of (ULift.{u + 1} A) (Fin n → ULift.{u + 1} A)) := by
  let H := e.ordinary.functor ⋙ e.fixed.functor
  let S : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
    constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))
  letI := FiniteNativeTensor.heartMonoidal A T e
  exact H.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ (Functor.Monoidal.εIso H).symm ≪≫
      Functor.Monoidal.εIso S) ≪≫
    (S.mapBiproduct _).symm ≪≫ S.mapIso (ModuleCat.biproductIsoPi _)

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
omit [DiscreteTopology A] in
private theorem encodedPresentation (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T)
    (hM : Mod.IsFinitelyPresented (condensedRingObj (coefficient A) T) M) :
    IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  let H := e.ordinary.functor ⋙ e.fixed.functor
  let S : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
    constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))
  obtain ⟨n, m, d, ⟨j⟩⟩ := hM
  let em := freeEncoding A T e m
  let en := freeEncoding A T e n
  let d' := em.inv ≫ H.map d ≫ en.hom
  let j' : H.obj M ≅ cokernel d' :=
    H.mapIso j ≪≫ PreservesCokernel.iso H d ≪≫
      cokernel.mapIso _ _ em en (by simp [d'])
  exact isFiniteLocallyConstant_of_iso j'.symm
    (isFiniteLocallyConstant_cokernel_constant T _ _ d')

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
omit [DiscreteTopology A] in
private theorem inverseConstantPresentation (T : Scheme.{u}) (e : Encoding A T)
    (P : ModuleCat.{u + 1} (ULift.{u + 1} A)) [Finite P] :
    Mod.IsFinitelyPresented (condensedRingObj (coefficient A) T)
      ((e.ordinary.trans e.fixed).inverse.obj
        ((constantSheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)) := by
  let H := (e.ordinary.trans e.fixed).functor
  let S : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
    constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))
  let : IsNoetherianRing (ULift.{u + 1} A) := isNoetherian_of_finite _ _
  have : Module.FinitePresentation (ULift.{u + 1} A) P :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' (ULift.{u + 1} A) P
  let g' := ModuleCat.ofHom g
  let f' := ModuleCat.ofHom f
  let j : P ≅ cokernel g' :=
    (ModuleCat.isColimitCokernelCofork g' f' hg hf).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let em := freeEncoding A T e m
  let en := freeEncoding A T e n
  let d := H.preimage (em.hom ≫ S.map g' ≫ en.inv)
  refine ⟨n, m, d, ⟨?_⟩⟩
  apply (e.ordinary.trans e.fixed).fullyFaithfulFunctor.preimageIso
  exact (e.ordinary.trans e.fixed).counitIso.app _ ≪≫ S.mapIso j ≪≫
    PreservesCokernel.iso S g' ≪≫
    cokernel.mapIso _ (H.map d) em.symm en.symm (by simp [d]) ≪≫
    (PreservesCokernel.iso H d).symm


omit [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] in
private theorem finiteLocallyConstant_of_cover
    {T : Scheme.{u}}
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    (hC : ∀ i : C.I₀, IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C.f i)).obj M)) :
    IsFiniteLocallyConstant (ULift.{u + 1} A) M := by
  classical
  choose I W g hg h using hC
  let D (i : C.I₀) : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (C.X i) :=
    ⟨⟨I i, W i, g i⟩, hg i⟩
  let E := C.bind D
  refine ⟨E.I₀, E.X, E.f, E.mem₀, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := h i j
  exact ⟨P, hP, ⟨(upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A))
    (g i j) (C.f i)).app M ≪≫ e⟩⟩

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem localPresentationEncoding (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T)
    (hM : IsLocallyFinitelyPresented (condensedRingObj (coefficient A) T) M) :
    IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  classical
  obtain ⟨C, hC⟩ := hM
  apply finiteLocallyConstant_of_cover A _ C
  intro i
  let eU := Classical.choice (encoding_exists A (C.X i))
  let φ := condensedPullbackHom (coefficient A) (C.f i)
  let raw := ((upperStar Ab.{u + 1} (C.f i)).mapMod
    (condensedRingObj (coefficient A) T)).obj M
  have hn := Mod.IsFinitelyPresented.comap (asIso φ).inv (hC i)
  have hi : Mod.IsFinitelyPresented (condensedRingObj (coefficient A) (C.X i))
      ((CondensedRing.upperStar (coefficient A) (C.f i)).obj M) :=
    Mod.IsFinitelyPresented.of_iso ((Mod.extendScalarsIsoComapInv φ).app raw).symm hn
  exact isFiniteLocallyConstant_of_iso (encoding_pullback_fixed A (C.f i) e eU M).some
    (encodedPresentation A (C.X i) eU _ hi)

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem localPresentation_of_encoding (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T)
    (hM : IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((e.ordinary.functor ⋙ e.fixed.functor).obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj (coefficient A) T) M := by
  classical
  obtain ⟨I, W, g, hg, h⟩ := hM
  let C₀ : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage T := ⟨⟨I, W, g⟩, hg⟩
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  let C := C₀.restrictIndexOfSmall.{u}
  refine ⟨C, fun i ↦ ?_⟩
  let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} C₀ i
  obtain ⟨P, hP, ⟨jP⟩⟩ := h j
  let : Finite P := hP
  let eU := Classical.choice (encoding_exists A (C.X i))
  let N := (CondensedRing.upperStar (coefficient A) (C.f i)).obj M
  let ep : (eU.ordinary.functor ⋙ eU.fixed.functor).obj N ≅
      (constantSheaf (Scheme.ProEt.topology (C.X i))
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P :=
    (encoding_pullback_fixed A (C.f i) e eU M).some ≪≫ jP
  have hn := Mod.IsFinitelyPresented.of_iso
    ((eU.ordinary.trans eU.fixed).inverse.mapIso ep.symm ≪≫
      ((eU.ordinary.trans eU.fixed).unitIso.app N).symm)
    (inverseConstantPresentation A (C.X i) eU P)
  let φ := condensedPullbackHom (coefficient A) (C.f i)
  let raw := ((upperStar Ab.{u + 1} (C.f i)).mapMod
    (condensedRingObj (coefficient A) T)).obj M
  have hr := Mod.IsFinitelyPresented.of_iso
    ((Mod.extendScalarsIsoComapInv φ).app raw) hn
  exact finitePresentation_of_comap (asIso φ).inv hr

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem intrinsicConstructibleEncoding (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T) :
    IsConstructibleModuleObject (condensedRingObj (coefficient A) T) M ↔
      IsConstructible (ULift.{u + 1} A)
        ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    let eS := Classical.choice (encoding_exists A (S.domain a))
    have hl := (CondensedRing.isLocallyFinitelyPresented_mapMod_iff
      (coefficient A) (S.immersion a) M).mp (hS a)
    exact isFiniteLocallyConstant_of_iso
      (encoding_pullback_fixed A (S.immersion a) e eS M).some
      (localPresentationEncoding A _ eS _ hl)
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    let eS := Classical.choice (encoding_exists A (S.domain a))
    apply (CondensedRing.isLocallyFinitelyPresented_mapMod_iff
      (coefficient A) (S.immersion a) M).mpr
    exact localPresentation_of_encoding A _ eS _
      (isFiniteLocallyConstant_of_iso
        (encoding_pullback_fixed A (S.immersion a) e eS M).some.symm (hS a))

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem intrinsicBoundedConstructibleEncoding (T : Scheme.{u}) (e : Encoding A T)
    (K : _root_.DerivedCategory (Internal A T)) :
    boundedConstructible (condensedRingObj (coefficient A) T) K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
        (e.fixedDerived.functor.obj K) := by
  let H := e.ordinary.functor ⋙ e.fixed.functor
  constructor
  · intro h
    apply DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic
    refine ⟨H.bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    exact isConstructible_of_iso ((H.mapDerivedCategoryHomologyFunctorIso n).app K)
      ((intrinsicConstructibleEncoding A T e _).mp (h.2 n))
  · intro h
    have hi := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ h
    refine ⟨H.bounded_of_bounded_mapDerivedCategory_obj hi.1, fun n ↦ ?_⟩
    exact (intrinsicConstructibleEncoding A T e _).mpr
      (isConstructible_of_iso ((H.mapDerivedCategoryHomologyFunctorIso n).app K).symm
        (hi.2 n))

omit [Finite A] [DiscreteTopology A] in
private theorem encodedHom_isIso (E : ∀ T : Scheme.{u}, Encoding A T)
    (T : Scheme.{u}) (K L : CondensedBridge.Native A T) :
    letI := FiniteNativeTensor.encodingMonoidal A T (E T)
    let H := ((CondensedRing.derivedHom (coefficient A) T).obj (Opposite.op K)).obj L
    IsIso ((ProEtale.derivedTensorHomAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) ((CondensedBridge.N A E T).obj K)).homEquiv _ _
        ((Functor.Monoidal.μIso (CondensedBridge.N A E T) K H).hom ≫
          (CondensedBridge.N A E T).map
            ((CondensedRing.derivedTensorHomAdjunction (coefficient A) K).counit.app L))) := by
  let := FiniteNativeTensor.encodingMonoidal A T (E T)
  change IsIso (MonoidalClosed.curry
    (Functor.LaxMonoidal.μ (CondensedBridge.N A E T) K _ ≫
      (CondensedBridge.N A E T).map ((ihom.ev K).app L)))
  rw [← Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  infer_instance

attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
/-- Normalized finite coefficients preserve intrinsic constructibility, Tor amplitude,
and the evaluation comparison, including the zero ring and empty schemes.
Source: Bhatt--Scholze, Section 6.8; the finite coefficient comparison in the composition
proof, Step 2 (blueprint: lem-pur-composition-tensor-coefficient-objects).

Proof: the heart tensor-unit comparison and finite biproduct comparison identify the
images of finite free internal modules with finite constant sheaves. Exactness carries
finite presentations to cokernels of maps of finite constant sheaves, which are finite
locally constant. Conversely, a finite module over the finite ring has a finite free
presentation. Apply the inverse exact equivalence and the same free-module comparison.
Use the normalized pullback comparison on the members of each cover and each stratum.
Thus intrinsic constructibility is preserved and reflected. The homology comparison
of an exact equivalence preserves boundedness and transfers the sheaf result to every
cohomology object. The existing Tor-interval comparison transfers each interval after
enlarging unordered witnesses to their minimum and maximum. Finally the encoded
evaluation transpose is the internal-Hom comparison of a monoidal equivalence, hence
is invertible by the closed monoidal equivalence theorem. -/
theorem compositionTensorCoefficientObjects (E : ∀ T : Scheme.{u}, Encoding A T)
    (T : Scheme.{u}) : CondensedBridge.Objects A E T := by
  refine ⟨fun K ↦ ?_, encodedHom_isIso A E T⟩
  refine and_congr (intrinsicBoundedConstructibleEncoding A T (E T) K) ?_
  have ht := (encoding_tensor_tor A T (E T)).2.2 K
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨min a b, max a b, (ht _ _ min_le_max).mp
      (h.mono (min_le_left _ _) (le_max_right _ _))⟩
  · rintro ⟨a, b, h⟩
    exact ⟨min a b, max a b, (ht _ _ min_le_max).mpr
      (h.mono (min_le_left _ _) (le_max_right _ _))⟩

end AlgebraicGeometry.ProEtale.CompositionTensorMate
