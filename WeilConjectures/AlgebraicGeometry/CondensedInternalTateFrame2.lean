/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Monoidal.Internal.Limits
import WeilConjectures.AlgebraicGeometry.Sites.GenericKummer
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFreeTensorLinear
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction

/-! # Root-normalized frames of the internal Tate module

Source: current blueprint, coefficient twists (order 1251) and Frobenius on coefficient
 twists (order 2855). (blueprint: lem-pur-condensed-internal-tate-frame).

All lines below are the published internal-module constructions. Positive root levels
are indexed by n : N with exponent n+1; the upstream Tate tower also has its zero level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  Functor.LaxMonoidal
open scoped TensorProduct
open scoped CategoryTheory.Obj CategoryTheory.MonObj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private local instance purFrameSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

private def purFrameFreeUnitIso {C : Type v} [Category.{w} C] [MonoidalCategory C]
    (R : C) [MonObj R] : (Mod.free R).obj (𝟙_ C) ≅ Mod.regular R :=
  Mod.isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ C)).inv ≫ MonObj.mul ▷ (𝟙_ C)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ MonObj.mul
    rw [Category.assoc, rightUnitor_naturality, ← Category.assoc]
    congr 1
    monoidal)

private def purFrameCyclicIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (r : ℕ) :
    purZlQuotient l X r ≅
      (Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)).obj
        ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ r))))) := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.free R
  let : (Mod.free R).Additive :=
    { map_add := fun {M N f g} ↦ Mod.hom_ext _ _
        (MonoidalPreadditive.whiskerLeft_add f g) }
  let : PreservesColimitsOfSize.{u + 1, u + 1} (Mod.free R) :=
    (Mod.freeForgetAdjunction R).leftAdjoint_preservesColimits
  let e : Mod.regular R ≅ F.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
    (purFrameFreeUnitIso R).symm ≪≫
      (Mod.free R).mapIso
        (asIso (ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})))
  let h := Functor.isColimitCokernelCoforkNSMulMap (l ^ r) F
    (AddCommGrpCat.isColimitUliftIntToZMod.{u} (l ^ r))
  exact (Mod.isColimitCokernelCofork (purZlPowerMultiplication l X r)).coconePointUniqueUpToIso
    (Limits.CokernelCofork.isColimitNSMulOfIso (l ^ r) e h)

private def purFrameFiniteMap {C : Type v} [Category.{w} C] [MonoidalCategory C]
    (R : C) [MonObj R] {U : C} (a : 𝟙_ C ⟶ U) :
    Mod.regular R ⟶ (Mod.free R).obj U :=
  (purFrameFreeUnitIso R).inv ≫ (Mod.free R).map a

private theorem purFrameFiniteMap_unit {C : Type v} [Category.{w} C]
    [MonoidalCategory C] (R : C) [MonObj R] {U : C} (a : 𝟙_ C ⟶ U) :
    η[R] ≫ (purFrameFiniteMap R a).hom = (λ_ (𝟙_ C)).inv ≫ (η[R] ⊗ₘ a) := by
  change η[R] ≫ ((ρ_ R).inv ≫ R ◁ a) = _
  rw [← Category.assoc, rightUnitor_inv_naturality, ← unitors_inv_equal,
    Category.assoc, MonoidalCategory.tensorHom_def]

private theorem purFrameFiniteMap_natural {C : Type v} [Category.{w} C]
    [MonoidalCategory C] (R : C) [MonObj R] {U V : C}
    (a : 𝟙_ C ⟶ U) (f : U ⟶ V) :
    purFrameFiniteMap R a ≫ (Mod.free R).map f = purFrameFiniteMap R (a ≫ f) := by
  unfold purFrameFiniteMap
  rw [Category.assoc, ← Functor.map_comp]

private theorem purFrameCyclicIso_projection (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (r : ℕ) :
    purZlQuotientProjection l X r ≫ (purFrameCyclicIso l X r).hom =
      (purFrameFreeUnitIso
        (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)).inv ≫
      (Mod.free _).map
        (ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
          (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
            (AddCommGrpCat.uliftIntToZMod (l ^ r))) := by
  dsimp only [purFrameCyclicIso]
  change (Mod.cokernelCofork (purZlPowerMultiplication l X r)).ι.app
    WalkingParallelPair.one ≫ _ = _
  rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  change ((purFrameFreeUnitIso R).inv ≫ (Mod.free R).map (ε F)) ≫
    (Mod.free R).map (F.map (AddCommGrpCat.uliftIntToZMod (l ^ r))) = _
  rw [Category.assoc, ← Functor.map_comp]

private theorem purFrameRoot_presheaf (D : WeilConjectures.FiniteFieldDatum.{u})
    (m : ℕ) (z : rootsOfUnity m D.k) :
    ε (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ≫
      (purFrameRoot D m z).hom =
    Sheaf.unitPresheafHomOfSection (Scheme.ProEt.isTerminalMkId (Spec (.of D.k)))
      (P := rootsOfUnityPresheaf (Spec (.of D.k)) m)
      (ULift.up (Additive.ofMul
        (restrictRootsOfUnity (Scheme.ΓSpecIso (.of D.k)).inv.hom m z))) ≫
      toSheafify (Scheme.ProEt.topology (Spec (.of D.k)))
        (rootsOfUnityPresheaf (Spec (.of D.k)) m) := by
  let J := Scheme.ProEt.topology (Spec (.of D.k))
  let adj := sheafificationAdjunction J Ab.{u + 1}
  have hε : ε (sheafToPresheaf J Ab.{u + 1}) ≫
      (sheafToPresheaf J Ab.{u + 1}).map (ε (presheafToSheaf J Ab.{u + 1})) =
        adj.unit.app (𝟙_ _) := by
    rw [← adj.unit_app_unit_comp_map_η, Category.assoc, Functor.Monoidal.map_η_ε]
    exact Category.comp_id _
  unfold purFrameRoot
  change ε (sheafToPresheaf J Ab.{u + 1}) ≫
    (sheafToPresheaf J Ab.{u + 1}).map (ε (presheafToSheaf J Ab.{u + 1}) ≫ _) = _
  rw [Functor.map_comp, ← Category.assoc, hε]
  exact (adj.unit.naturality _).symm

private theorem purFrame_lax_tensor_unit
    {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {B : Type v} [Category.{w} B] [MonoidalCategory B]
    (F : C ⥤ B) [F.LaxMonoidal] {R U : C}
    (a : 𝟙_ C ⟶ R) (b : 𝟙_ C ⟶ U) :
    ε F ≫ F.map ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b)) =
      (λ_ (𝟙_ B)).inv ≫ ((ε F ≫ F.map a) ⊗ₘ (ε F ≫ F.map b)) ≫
        Functor.LaxMonoidal.μ F R U := by
  symm
  rw [← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural]
  rw [tensorHom_def'_assoc, ← leftUnitor_inv_naturality_assoc,
    Functor.LaxMonoidal.left_unitality_inv_assoc, ← F.map_comp]


private theorem purFrameRoot_eval (D : WeilConjectures.FiniteFieldDatum.{u})
    (m : ℕ) [NeZero m] (z : rootsOfUnity m D.k)
    (hz : IsPrimitiveRoot (z : D.kˣ) m) (U : (Spec (.of D.k)).ProEtᵒᵖ) :
    (ε (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ≫
      (purFrameRoot D m z).hom).app U (ULift.up 1) =
      condensedRootFrameSection D.k m (z : D.kˣ) (IsPrimitiveRoot.coe_units_iff.mpr hz) U := by
  rw [purFrameRoot_presheaf]
  change (toSheafify (Scheme.ProEt.topology (Spec (.of D.k)))
    (rootsOfUnityPresheaf (Spec (.of D.k)) m)).app U
      ((1 : ℤ) • (rootsOfUnityPresheaf (Spec (.of D.k)) m).map
        ((Scheme.ProEt.isTerminalMkId (Spec (.of D.k))).from U.unop).op
        (ULift.up (Additive.ofMul
          (restrictRootsOfUnity (Scheme.ΓSpecIso (.of D.k)).inv.hom m z)))) = _
  rw [one_zsmul]
  unfold condensedRootFrameSection
  apply congrArg ((toSheafify (Scheme.ProEt.topology (Spec (.of D.k)))
    (rootsOfUnityPresheaf (Spec (.of D.k)) m)).app U)
  apply ULift.ext
  apply rootsOfUnity.coe_injective
  change (U.unop.hom.appTop).hom
      ((Scheme.ΓSpecIso (.of D.k)).inv.hom ((z : D.kˣ) : D.k)) =
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ U.unop.hom.appTop).hom
      ((((IsPrimitiveRoot.coe_units_iff.mpr hz).toRootsOfUnity : D.kˣ) : D.k))
  rw [IsPrimitiveRoot.val_toRootsOfUnity_coe]
  rfl


private theorem purFrameFreeRoot_eval (D : WeilConjectures.FiniteFieldDatum.{u})
    (m : ℕ) [NeZero m] (z : rootsOfUnity m D.k)
    (hz : IsPrimitiveRoot (z : D.kˣ) m)
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (U : (Spec (.of D.k)).ProEtᵒᵖ) :
    (ε (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ≫
      (purFrameFreeRoot D m z R).hom).app U (ULift.up 1) =
    condensedRootFrameTensor _ R m U (condensedRootFrameOne _ R U)
      (condensedRootFrameSection D.k m (z : D.kˣ)
        (IsPrimitiveRoot.coe_units_iff.mpr hz) U) := by
  change (ε (sheafToPresheaf _ _) ≫
    (sheafToPresheaf _ _).map ((λ_ _).inv ≫ (η[R] ⊗ₘ purFrameRoot D m z))).app U
      (ULift.up 1) = _
  rw [purFrame_lax_tensor_unit]
  change (Functor.LaxMonoidal.μ (sheafToPresheaf _ _) R _).app U
    ((_ : R.obj.obj U) ⊗ₜ[ℤ]
      ((ε (sheafToPresheaf _ _) ≫ (purFrameRoot D m z).hom).app U (ULift.up 1))) = _
  rw [purFrameRoot_eval D m z hz U]
  rfl

set_option maxHeartbeats 800000 in
-- Unfolding the sheaf unit and constant-section comparison needs extra elaboration.
private theorem purFrameConstantRoot_normalized (D : WeilConjectures.FiniteFieldDatum.{u})
    (m : ℕ) [NeZero m] (hm : 1 < m) (z : rootsOfUnity m D.k)
    (hz : IsPrimitiveRoot (z : D.kˣ) m)
    (b : (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))) ≅
      rootsOfUnitySheaf (Spec (.of D.k)) m)
    (hb : ∀ (U : (Spec (.of D.k)).ProEtᵒᵖ) (j : ZMod m),
      b.hom.hom.app U (condensedRootFrameLabel _ m U j) =
        j.val • condensedRootFrameSection D.k m (z : D.kˣ)
          (IsPrimitiveRoot.coe_units_iff.mpr hz) U) :
    (ε (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ≫
      (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}).map
        (AddCommGrpCat.uliftIntToZMod m)) ≫ b.hom = purFrameRoot D m z := by
  have h : AddCommGrpCat.uliftIntToZMod.{u + 1} m =
      AddCommGrpCat.unitHom (ULift.up (1 : ZMod m)) := by
    ext x
    change (Int.cast (show ℤ from x.down) : ZMod m) =
      (show ℤ from x.down) • (1 : ZMod m)
    simp
  rw [h]
  apply Sheaf.unitHomEval_injective (J := Scheme.ProEt.topology (Spec (.of D.k)))
    (Scheme.ProEt.isTerminalMkId (Spec (.of D.k))) _
  change b.hom.hom.app _ (Sheaf.unitHomEval
    (J := Scheme.ProEt.topology (Spec (.of D.k))) _
    (Sheaf.constRingSheafSection (Scheme.ProEt.topology (Spec (.of D.k)))
      (ULift.up (1 : ZMod m) : ULift.{u + 1} (ZMod m)))) = _
  unfold Sheaf.unitHomEval
  erw [Sheaf.ε_comp_constRingSheafSection]
  change b.hom.hom.app _
    ((toSheafify (Scheme.ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app _
          ((1 : ℤ) • (ULift.up (1 : ZMod m) : ULift.{u + 1} (ZMod m)))) = _
  rw [one_zsmul]
  change b.hom.hom.app _ (condensedRootFrameLabel _ m _ 1) = _
  rw [hb, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hm, one_nsmul]
  exact (purFrameRoot_eval D m z hz _).symm

private theorem purFrameRootFrames_exists (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (hprim : ∀ n : ℕ, IsPrimitiveRoot (z n : D.kˣ) (l ^ (n + 1)))
    (hcompat : ∀ n : ℕ, (z (n + 1) : D.kˣ) ^ l = (z n : D.kˣ)) :
    ∃ b : ∀ n : ℕ,
      (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) ≅
        rootsOfUnitySheaf (Spec (.of D.k)) (l ^ (n + 1)),
      (∀ n : ℕ,
        (ε (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ≫
          (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}).map
            (AddCommGrpCat.uliftIntToZMod (l ^ (n + 1)))) ≫ (b n).hom =
          purFrameRoot D _ (z n)) ∧
      ∀ n : ℕ, (b (n + 1)).hom ≫ condensedRootFramePower _ l n =
        condensedRootFrameReduction _ l n ≫ (b n).hom := by
  let : FiniteDimensional ℚ_[l] (ULift.{u} ℚ_[l]) :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := ℚ_[l])).symm.finiteDimensional
  let ζ : ℕ → D.k := fun n ↦ (z n : D.kˣ)
  have hζ (n : ℕ) : IsPrimitiveRoot (ζ n) (l ^ (n + 1)) :=
    IsPrimitiveRoot.coe_units_iff.mpr (hprim n)
  obtain ⟨b, _, _, hb, hbc, _⟩ :=
    (condensedFiniteIntegralRootFrame D l hl (ULift.{u} ℚ_[l])).2 ζ hζ
      (fun n ↦ congrArg Units.val (hcompat n))
  refine ⟨b, fun n ↦ ?_, hbc⟩
  let : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact purFrameConstantRoot_normalized D _
    (one_lt_pow₀ (Fact.out : l.Prime).one_lt (Nat.succ_ne_zero n)) (z n) (hprim n)
    (b n) (hb n)

private theorem purFrameTate_unique (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (b c : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
      (Spec (.of D.k))) ≅ tateModule (Spec (.of D.k)) l)
    (hb : PurFrameTateNormalized D l z b)
    (hc : PurFrameTateNormalized D l z c) : b = c := by
  apply Iso.ext
  apply limit.hom_ext
  intro n
  have h (i : ℕ) : b.hom ≫ limit.π (tateModuleSystem (Spec (.of D.k)) l)
        (op (i + 1)) = c.hom ≫ limit.π (tateModuleSystem (Spec (.of D.k)) l)
          (op (i + 1)) := Mod.regular_hom_ext ((hb i).trans (hc i).symm)
  cases n using Opposite.rec with | _ n =>
    cases n with
    | zero =>
      rw [← limit.w (tateModuleSystem (Spec (.of D.k)) l)
        (homOfLE (Nat.zero_le 1)).op, ← Category.assoc, ← Category.assoc, h 0]
    | succ n => exact h n

private def purFrameRingModuleMap {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {R B S : C} [MonObj R] [MonObj B] [MonObj S]
    (f : R ⟶ B) [IsMonHom f] (g : R ⟶ S) [IsMonHom g]
    (h : B ⟶ S) [IsMonHom h] (hf : f ≫ h = g) :
    (Mod.comap f).obj (Mod.regular B) ⟶ (Mod.comap g).obj (Mod.regular S) :=
  Mod.homMk h (by
    change (f ▷ B ≫ MonObj.mul) ≫ h = R ◁ h ≫ g ▷ S ≫ MonObj.mul
    calc
      _ = (f ⊗ₘ 𝟙 B) ≫ (h ⊗ₘ h) ≫ MonObj.mul := by
        rw [tensorHom_id, Category.assoc, IsMonHom.mul_hom]
      _ = (g ⊗ₘ h) ≫ MonObj.mul := by
        rw [tensorHom_comp_tensorHom_assoc, hf, Category.id_comp]
      _ = _ := by rw [tensorHom_def', Category.assoc])

private def purFrameRingConeModules {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {J : Type*} [Category J] (F : J ⥤ Mon C) (c : Cone F) : J ⥤ Mod C c.pt.X where
  obj j := (Mod.comap (c.π.app j).hom).obj (Mod.regular (F.obj j).X)
  map {i j} f := purFrameRingModuleMap (c.π.app i).hom (c.π.app j).hom
    (F.map f).hom (congrArg Mon.Hom.hom (c.w f))
  map_id j := Mod.hom_ext _ _ (congrArg Mon.Hom.hom (F.map_id j))
  map_comp f g := Mod.hom_ext _ _ (congrArg Mon.Hom.hom (F.map_comp f g))

private def purFrameRingModuleCone {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {J : Type*} [Category J] (F : J ⥤ Mon C) (c : Cone F) :
    Cone (purFrameRingConeModules F c) where
  pt := Mod.regular c.pt.X
  π :=
    { app j := Mod.regularToComapRegular (c.π.app j).hom
      naturality i j f := Mod.hom_ext _ _ (by
        change 𝟙 _ ≫ (c.π.app j).hom = (c.π.app i).hom ≫ (F.map f).hom
        rw [Category.id_comp]
        exact (congrArg Mon.Hom.hom (c.w f)).symm) }

private def purFrameRingModuleCone_isLimit
    {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {J : Type*} [Category J] (F : J ⥤ Mon C) [PreservesLimit F (Mon.forget C)]
    (c : Cone F) (hc : IsLimit c) :
    IsLimit (purFrameRingModuleCone F c) := by
  apply isLimitOfReflects (Mod.forget c.pt.X)
  exact isLimitOfPreserves (Mon.forget C) hc

private theorem purFrameReduction_natural (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (a b : ℕᵒᵖ) (f : a ⟶ b) :
    purZlReduction l X a.unop ≫
      (sfbZModCoefficientTower l ⋙ sfbConstantRing X).map f = purZlReduction l X b.unop := by
  let P := (upperStarFromPoint X).mapMon
  let C := sfbConstantRing X
  let e := purZlConstantPullbackIso l X
  let d := purZlResidueTowerIso l
  have hρ := (purZlPointReduction l).naturality f
  erw [Category.id_comp] at hρ
  have he := e.hom.naturality f
  have hd := d.hom.naturality f
  change P.map ((purZlPointReduction l).app a) ≫ e.hom.app a ≫
      C.map (d.hom.app a) ≫ C.map ((sfbZModCoefficientTower l).map f) =
    P.map ((purZlPointReduction l).app b) ≫ e.hom.app b ≫ C.map (d.hom.app b)
  rw [← C.map_comp, ← hd, C.map_comp]
  change P.map _ ≫ e.hom.app b = e.hom.app a ≫ C.map _ at he
  rw [← reassoc_of% he, ← P.map_comp_assoc]
  change (purZlPointReduction l).app b = (purZlPointReduction l).app a ≫
    sfbPointConstantRing.map ((sfbCoefficientQuotientTower ℤ_[l]
      (Ideal.span ({(l : ℤ_[l])} : Set ℤ_[l]))).map f) at hρ
  rw [← hρ]

private def purFrameResidueCone (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Cone (sfbZModCoefficientTower l ⋙ sfbConstantRing X) where
  pt := coefficientRing X (Mon.mk (Profinite.continuousMapRingObj ℤ_[l]))
  π :=
    { app n := purZlReduction l X n.unop
      naturality i j f := by
        rw [Functor.const_obj_map]
        erw [Category.id_comp]
        exact (purFrameReduction_natural l X i j f).symm }

set_option maxHeartbeats 800000 in
-- Transporting this cone unfolds the normalized coefficient and pullback comparisons.
private def purFrameResidueCone_isLimit (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsLimit (purFrameResidueCone l X) := by
  let c := (upperStarFromPoint X).mapMon.mapCone
    (Cone.mk (Mon.mk (Profinite.continuousMapRingObj ℤ_[l])) (purZlPointReduction l))
  let e := (purZlConstantPullbackIso l X) ≪≫
    Functor.isoWhiskerRight (purZlResidueTowerIso l) (sfbConstantRing X)
  have hρ : (sfb_completed_coefficients.{u} l).2.1.choose = purZlPointReduction l := by
    apply NatTrans.ext
    funext n
    apply Mon.Hom.ext
    let d := (Mon.forget _).mapIso
      (sfbPointConstantRing.mapIso ((purZlResidueTowerIso l).app n)) ≪≫
        purFinitePointIso (ZMod (l ^ n.unop))
    apply (Iso.cancel_iso_hom_right _ _ d).mp
    change ((sfb_completed_coefficients.{u} l).2.1.choose.app n).hom ≫
        (sfbPointConstantRing.map ((purZlResidueTowerIso l).hom.app n)).hom ≫
          (purFinitePointIso (ZMod (l ^ n.unop))).hom =
      ((purZlPointReduction l).app n).hom ≫
        (sfbPointConstantRing.map ((purZlResidueTowerIso l).hom.app n)).hom ≫
          (purFinitePointIso (ZMod (l ^ n.unop))).hom
    rw [purPointReduction_normalized]
    apply purPointMap_ext
    rw [← Category.assoc, ← Category.assoc,
      (sfb_completed_coefficients.{u} l).2.1.choose_spec.1 n.unop]
    let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
    change (C.map _ ≫ C.map _) ≫ _ = C.map _ ≫ _
    rw [← C.map_comp, purResidueComposite, purFinitePointIso_hom]
  let hc : IsLimit c := by
    dsimp only [c]
    rw [← hρ]
    exact ((sfb_completed_coefficients.{u} l).2.1.choose_spec.2.1 X).1.some
  apply ((IsLimit.postcomposeHomEquiv e c).symm hc).ofIsoLimit
  refine Cone.ext (Iso.refl _) (fun n ↦ ?_)
  change (purZlReduction l X n.unop) = _
  simp only [purZlReduction, e, c, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Iso.refl_hom, Category.id_comp, purFrameResidueCone]

private def purFramePositiveShift : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show Monotone (fun n : ℕ ↦ n + 1) from fun _ _ h ↦ Nat.add_le_add_right h 1).functor.op

private instance : purFramePositiveShift.Initial := by
  let h : Monotone (fun n : ℕ ↦ n + 1) := fun _ _ h ↦ Nat.add_le_add_right h 1
  let : h.functor.Final := h.final_functor_iff.mpr (fun n ↦ ⟨n, Nat.le_succ n⟩)
  exact inferInstanceAs h.functor.op.Initial

set_option maxHeartbeats 1200000 in
-- The tower comparison elaborates several large monoidal coefficient functors.
private theorem purFrameTate_exists (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (hprim : ∀ n : ℕ, IsPrimitiveRoot (z n : D.kˣ) (l ^ (n + 1)))
    (hcompat : ∀ n : ℕ, (z (n + 1) : D.kˣ) ^ l = (z n : D.kˣ)) :
    ∃ b : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
        (Spec (.of D.k))) ≅ tateModule (Spec (.of D.k)) l,
      PurFrameTateNormalized D l z b := by
  let X := Spec (.of D.k)
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let gen (n : ℕ) := ε F ≫ F.map (AddCommGrpCat.uliftIntToZMod (l ^ (n + 1)))
  obtain ⟨b, hb, hbc⟩ := purFrameRootFrames_exists D l hl z hprim hcompat
  have hg (n : ℕ) : gen (n + 1) ≫ condensedRootFrameReduction X l n = gen n := by
    dsimp only [gen, condensedRootFrameReduction]
    rw [Category.assoc, ← F.map_comp]
    apply congrArg (fun t ↦ ε F ≫ F.map t)
    ext a
    change ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) _
        (Int.cast a.down : ZMod (l ^ (n + 1 + 1))) =
      (Int.cast a.down : ZMod (l ^ (n + 1)))
    exact map_intCast _ _
  have hzpow (n : ℕ) : purFrameRoot D _ (z (n + 1)) ≫
      condensedRootFramePower X l n = purFrameRoot D _ (z n) := by
    rw [← hb (n + 1), Category.assoc, hbc, ← Category.assoc, hg, hb]
  obtain ⟨_, q, hq, _, _⟩ := pur_condensed_zl_reduction_mod_ell_power l X
  let K := purFramePositiveShift ⋙ sfbZModCoefficientTower l ⋙ sfbConstantRing X
  let c := (purFrameResidueCone l X).whisker purFramePositiveShift
  let M := purFrameRingConeModules K c
  let cM := purFrameRingModuleCone K c
  let hcM : IsLimit cM := purFrameRingModuleCone_isLimit K c
    ((Functor.Initial.isLimitWhiskerEquiv purFramePositiveShift _).symm
      (purFrameResidueCone_isLimit l X))
  let V (n : ℕ) := purFrameFiniteMap R (purFrameRoot D _ (z n))
  let e (n : ℕ) : M.obj (op n) ≅ tateModuleLevel X l (n + 1) :=
    (q n).symm ≪≫ purFrameCyclicIso l X (n + 1) ≪≫ (Mod.free R).mapIso (b n)
  have hq' (n : ℕ) : purZlQuotientProjection l X (n + 1) ≫ (q n).hom =
      cM.π.app (op n) := Mod.hom_ext _ _ (hq n).2.2.2
  have hv (n : ℕ) : cM.π.app (op n) ≫ (e n).hom = V n := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← hq', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, purFrameCyclicIso_projection, Category.assoc,
      ← Functor.map_comp, hb n]
    rfl
  have hepi (n : ℕ) : Epi (cM.π.app (op n)) := by
    rw [← hq']
    have hπ : Epi (purZlQuotientProjection l X (n + 1)) :=
      (Mod.forget R).epi_of_epi_map
        (inferInstanceAs (Epi (cokernel.π (purZlPowerMultiplication l X (n + 1)).hom)))
    let : IsIso (q n).hom := (q n).isIso_hom
    exact epi_comp' hπ (inferInstance : Epi (q n).hom)
  let a : M ⟶ purFramePositiveShift ⋙ tateModuleSystem X l :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
      intro n
      let := hepi (n + 1)
      apply (cancel_epi (cM.π.app (op (n + 1)))).mp
      rw [← Category.assoc, cM.w, hv n, ← Category.assoc, hv (n + 1)]
      rw [Functor.comp_map]
      have hs : purFramePositiveShift.map (homOfLE (Nat.le_succ n)).op =
          (homOfLE (Nat.le_succ (n + 1))).op := Subsingleton.elim _ _
      rw [hs]
      change V n = V (n + 1) ≫ (tateModuleSystem X l).map
        (homOfLE (Nat.le_succ (n + 1))).op
      simp only [tateModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
      change V n = V (n + 1) ≫ (Mod.free R).map (condensedRootFramePower X l n)
      rw [purFrameFiniteMap_natural, hzpow])
  let : ∀ n, IsIso (a.app n) := fun n ↦ (e n.unop).isIso_hom
  let : IsIso a := NatIso.isIso_of_isIso_app a
  let cT := (Cone.postcompose a).obj cM
  let hcT : IsLimit cT := (IsLimit.postcomposeHomEquiv (asIso a) cM).symm hcM
  let hc := (Functor.Initial.isLimitWhiskerEquiv purFramePositiveShift
    (limit.cone (tateModuleSystem X l))).symm (limit.isLimit _)
  let B : Mod.regular R ≅ tateModule X l := hcT.conePointUniqueUpToIso hc
  refine ⟨B, fun n ↦ ?_⟩
  have h := hcT.conePointUniqueUpToIso_hom_comp hc (op n)
  change B.hom ≫ limit.π (tateModuleSystem X l) (op (n + 1)) =
    cM.π.app (op n) ≫ (e n).hom at h
  change η[R] ≫ (B.hom ≫ limit.π (tateModuleSystem X l) (op (n + 1))).hom = _
  rw [h, hv n, purFrameFiniteMap_unit]
  rfl

private theorem purFrameIntegral_unique (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (b c : Mod.regular (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) ≅
      coefficientIntegralTwistOne l E (Spec (.of D.k)))
    (hb : PurFrameIntegralNormalized D l z E b)
    (hc : PurFrameIntegralNormalized D l z E c) : b = c := by
  apply Iso.ext
  apply limit.hom_ext
  intro n
  apply Mod.regular_hom_ext
  exact (hb n.unop).trans (hc n.unop).symm

private theorem purFrameIntegral_exists (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (hprim : ∀ n : ℕ, IsPrimitiveRoot (z n : D.kˣ) (l ^ (n + 1)))
    (hcompat : ∀ n : ℕ, (z (n + 1) : D.kˣ) ^ l = (z n : D.kˣ))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ b : Mod.regular (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) ≅
      coefficientIntegralTwistOne l E (Spec (.of D.k)),
      PurFrameIntegralNormalized D l z E b := by
  let ζ : ℕ → D.k := fun n ↦ (z n : D.kˣ)
  have hζ (n : ℕ) : IsPrimitiveRoot (ζ n) (l ^ (n + 1)) :=
    IsPrimitiveRoot.coe_units_iff.mpr (hprim n)
  have hζc (n : ℕ) : ζ (n + 1) ^ l = ζ n := congrArg Units.val (hcompat n)
  obtain ⟨_, _, b, _, _, _, _, _, hb, _⟩ :=
    (condensedFiniteIntegralRootFrame D l hl E).2 ζ hζ hζc
  refine ⟨b, fun n ↦ ?_⟩
  let : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  apply Sheaf.unitHomEval_injective (J := Scheme.ProEt.topology (Spec (.of D.k)))
    (Scheme.ProEt.isTerminalMkId (Spec (.of D.k))) _
  change (limit.π (coefficientIntegralTwistSystem l E (Spec (.of D.k)))
      (op n)).hom.hom.app _
      (b.hom.hom.hom.app _ (condensedRootFrameOne _
        (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) _)) = _
  rw [hb n]
  exact (purFrameFreeRoot_eval D _ (z n) (hprim n)
    (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))) _).symm

private theorem purFrameExtend_normalized {C : Type v} [Category.{w} C]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (f : R ⟶ S) [IsMonHom f] {M : Mod C R} (b : Mod.regular R ≅ M) :
    η[S] ≫ (purFrameExtend f b).hom.hom =
      η[R] ≫ b.hom.hom ≫ Mod.extendUnitHom f M := by
  dsimp only [purFrameExtend, Iso.trans_hom, Iso.symm_hom, Mod.comp_hom',
    Functor.mapIso_hom]
  rw [Mod.one_comp_extendScalarsObjRegularIso_inv_hom_assoc,
    Mod.extendUnitHom_naturality]

private theorem purFrameCompare_normalized {C : Type v} [Category.{w} C]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (f : R ⟶ S) [IsMonHom f] {M : Mod C R} {N : Mod C S}
    (b : Mod.regular R ≅ M) (c : Mod.regular S ≅ N) :
    PurFrameComparisonNormalized f b c (purFrameCompare f b c) := by
  unfold PurFrameComparisonNormalized
  calc
    _ = (η[R] ≫ b.hom.hom ≫ Mod.extendUnitHom f M) ≫
        (purFrameCompare f b c).hom.hom := by simp only [Category.assoc]
    _ = (η[S] ≫ (purFrameExtend f b).hom.hom) ≫
        (purFrameCompare f b c).hom.hom :=
      congrArg (fun t ↦ t ≫ (purFrameCompare f b c).hom.hom)
        (purFrameExtend_normalized f b).symm
    _ = _ := by
      dsimp only [purFrameCompare, Iso.trans_hom, Iso.symm_hom, Mod.comp_hom']
      rw [Category.assoc, ← Category.assoc (purFrameExtend f b).hom.hom,
        ← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom', Category.id_comp]

private theorem purFrameCompare_unique {C : Type v} [Category.{w} C]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (f : R ⟶ S) [IsMonHom f] {M : Mod C R} {N : Mod C S}
    (b : Mod.regular R ≅ M) (c : Mod.regular S ≅ N)
    (e : (Mod.extendScalars f).obj M ≅ N)
    (he : PurFrameComparisonNormalized f b c e) : e = purFrameCompare f b c := by
  apply Iso.ext
  apply (cancel_epi (purFrameExtend f b).hom).mp
  apply Mod.regular_hom_ext
  change η[S] ≫ ((purFrameExtend f b).hom.hom ≫ e.hom.hom) =
    η[S] ≫ ((purFrameExtend f b).hom.hom ≫ (purFrameCompare f b c).hom.hom)
  simp only [← Category.assoc]
  rw [purFrameExtend_normalized f b]
  simp only [Category.assoc]
  exact he.trans (purFrameCompare_normalized f b c).symm

private theorem purFrameExtendUnit_comp {C : Type v} [Category.{w} C]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S T : C} [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ T) [IsMonHom g] (M : Mod C R) :
    Mod.extendUnitHom (f ≫ g) M ≫ ((Mod.extendScalarsComp f g).hom.app M).hom =
      Mod.extendUnitHom f M ≫ Mod.extendUnitHom g ((Mod.extendScalars f).obj M) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Mod.extendRestrictAdjunction (f ≫ g))
    (((Mod.extendRestrictAdjunction f).comp (Mod.extendRestrictAdjunction g)).ofNatIsoRight
      (Mod.comapComp f g).symm) M
  have h' := congrArg Mod.Hom.hom h
  simp only [Mod.comp_hom', Mod.comap_map_hom,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Adjunction.comp_unit_app,
    Mod.comapComp_inv_app_hom,
    Mod.extendRestrictAdjunction_unit_app_hom] at h'
  erw [Category.comp_id] at h'
  exact h'

private theorem purFrameCompare_comp {C : Type v} [Category.{w} C]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S T : C} [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ T) [IsMonHom g]
    {M : Mod C R} {N : Mod C S} {P : Mod C T}
    (b : Mod.regular R ≅ M) (c : Mod.regular S ≅ N) (d : Mod.regular T ≅ P) :
    PurFrameComparisonComp f g b c d := by
  let e := (Mod.extendScalarsComp f g).app M ≪≫
    (Mod.extendScalars g).mapIso (purFrameCompare f b c) ≪≫ purFrameCompare g c d
  have he : PurFrameComparisonNormalized (f ≫ g) b d e := by
    unfold PurFrameComparisonNormalized
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom']
    rw [← Category.assoc (Mod.extendUnitHom (f ≫ g) M)]
    erw [purFrameExtendUnit_comp]
    simp only [Category.assoc]
    erw [Mod.extendUnitHom_naturality_assoc]
    have hfc := purFrameCompare_normalized f b c
    unfold PurFrameComparisonNormalized at hfc
    calc
      _ = (η[R] ≫ b.hom.hom ≫ Mod.extendUnitHom f M ≫
          (purFrameCompare f b c).hom.hom) ≫ Mod.extendUnitHom g N ≫
            (purFrameCompare g c d).hom.hom := by simp only [Category.assoc]
      _ = _ := by
        erw [hfc]
        simpa only [PurFrameComparisonNormalized, Category.assoc] using
          purFrameCompare_normalized g c d
  exact congrArg Iso.hom (purFrameCompare_unique (f ≫ g) b d e he)

private def purFrameFreeCoefficientMap {C : Type v} [Category.{w} C]
    [MonoidalCategory C] {R S : C} [MonObj R] [MonObj S]
    (f : R ⟶ S) [IsMonHom f] (U : C) :
    (Mod.free R).obj U ⟶ (Mod.comap f).obj ((Mod.free S).obj U) :=
  (Mod.comapId R).inv.app _ ≫
    (coefficientFreeTensor_linear (𝟙 R) f f (Category.id_comp f) (𝟙 U)).choose

private theorem purFrameFreeCoefficientMap_hom {C : Type v} [Category.{w} C]
    [MonoidalCategory C] {R S : C} [MonObj R] [MonObj S]
    (f : R ⟶ S) [IsMonHom f] (U : C) :
    (purFrameFreeCoefficientMap f U).hom = f ▷ U := by
  rw [purFrameFreeCoefficientMap, Mod.comp_hom', Mod.comapId_inv_app_hom,
    Category.id_comp,
    (coefficientFreeTensor_linear (𝟙 R) f f (Category.id_comp f) (𝟙 U)).choose_spec.1,
    tensorHom_id]

private theorem purFrameFreeRoot_coefficient {C : Type v} [Category.{w} C]
    [MonoidalCategory C] {R S : C} [MonObj R] [MonObj S]
    (f : R ⟶ S) [IsMonHom f] {U : C} (z : 𝟙_ C ⟶ U) :
    ((λ_ (𝟙_ C)).inv ≫ (η[R] ⊗ₘ z)) ≫ f ▷ U =
      (λ_ (𝟙_ C)).inv ≫ (η[S] ⊗ₘ z) := by
  rw [Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    IsMonHom.one_hom, Category.comp_id]

private theorem purFrameFiniteProjection_generic
    {C : Type v} [Category.{w} C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S Q : C} [MonObj R] [MonObj S] [MonObj Q] [IsCommMonObj R]
    (f : R ⟶ S) [IsMonHom f] (q : S ⟶ Q) [IsMonHom q]
    {M : Mod C R} {N : Mod C S} (b : Mod.regular R ≅ M) (c : Mod.regular S ≅ N)
    {U : C} (p : M ⟶ (Mod.free R).obj U)
    (r : N ⟶ (Mod.comap q).obj ((Mod.free Q).obj U)) (z : 𝟙_ C ⟶ U)
    (hp : η[R] ≫ b.hom.hom ≫ p.hom = (λ_ (𝟙_ C)).inv ≫ (η[R] ⊗ₘ z))
    (hr : η[S] ≫ c.hom.hom ≫ r.hom = (λ_ (𝟙_ C)).inv ≫ (η[Q] ⊗ₘ z)) :
    Mod.extendπ f M ≫ (purFrameCompare f b c).hom.hom ≫ r.hom =
      (𝟙 S ⊗ₘ p.hom) ≫ (α_ S R U).inv ≫
        ((q ⊗ₘ (f ≫ q)) ▷ U) ≫ MonObj.mul ▷ U := by
  let P := (Mod.comap q).obj ((Mod.free Q).obj U)
  let h : M ⟶ (Mod.comap f).obj P := p ≫ purFrameFreeCoefficientMap (f ≫ q) U ≫
    (Mod.comapComp f q).hom.app ((Mod.free Q).obj U)
  have hh : h.hom = p.hom ≫ (f ≫ q) ▷ U := by
    dsimp only [h, Mod.comp_hom']
    rw [Mod.comapComp_hom_app_hom]
    erw [Category.comp_id]
    rw [purFrameFreeCoefficientMap_hom]
  let L : (Mod.extendScalars f).obj M ⟶ P := Mod.extendHom f h
  have hL : (purFrameExtend f b).hom ≫ L = c.hom ≫ r := by
    apply Mod.regular_hom_ext
    change η[S] ≫ ((purFrameExtend f b).hom.hom ≫ L.hom) =
      η[S] ≫ (c.hom.hom ≫ r.hom)
    calc
      _ = (η[S] ≫ (purFrameExtend f b).hom.hom) ≫ L.hom := by
        simp only [Category.assoc]
      _ = (η[R] ≫ b.hom.hom ≫ Mod.extendUnitHom f M) ≫ L.hom := by
        rw [purFrameExtend_normalized]
      _ = (η[R] ≫ b.hom.hom ≫ p.hom) ≫ (f ≫ q) ▷ U := by
        dsimp only [L]
        rw [Category.assoc, Category.assoc, Mod.extendUnitHom_extendHom, hh]
        simp only [Category.assoc]
      _ = _ := by
        rw [hp, purFrameFreeRoot_coefficient, hr]
  have he : (purFrameCompare f b c).hom ≫ r = L := by
    apply (cancel_epi (purFrameExtend f b).hom).mp
    rw [hL]
    dsimp only [purFrameCompare, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, Iso.hom_inv_id_assoc]
  change Mod.extendπ f M ≫ ((purFrameCompare f b c).hom ≫ r).hom = _
  rw [he, Mod.extendπ_extendHom, hh, MonoidalCategory.whiskerLeft_comp_assoc]
  change S ◁ p.hom ≫ S ◁ ((f ≫ q) ▷ U) ≫
    q ▷ (Q ⊗ U) ≫ (α_ Q Q U).inv ≫ MonObj.mul ▷ U = _
  calc
    _ = S ◁ p.hom ≫ (q ⊗ₘ ((f ≫ q) ⊗ₘ 𝟙 U)) ≫
        (α_ Q Q U).inv ≫ MonObj.mul ▷ U := by
      simp only [tensorHom_def', MonoidalCategory.whiskerLeft_id,
        Category.id_comp, Category.assoc]
    _ = _ := by
      rw [associator_inv_naturality_assoc]
      simp only [id_tensorHom, tensorHom_id]

/-- The prescribed compatible roots frame the internal Tate limit and all its
coefficient comparisons.

Source: current blueprint, coefficient twists (order 1251), integral-limit comparison,
and Frobenius coefficient twists (order 2855).
(blueprint: lem-pur-condensed-internal-tate-frame).

Proof: (1) Root coordinates j |-> z_n^j identify each abelian root sheaf with its
constant cyclic residue sheaf and intertwine the power maps and reduction.
(2) Tensor with R_s. The balanced map a tensor z_n^j |-> rho_n(a)j identifies
F_n with R_s/l^n. Locally lift coefficients for its inverse; changing a lift by
l^n changes the tensor by zero. (3) These maps intertwine the entire towers.
(4) The normalized condensed integral-limit comparison identifies their limit
with R_s. Its inverse gives b_T. Linearity and joint faithfulness of the limit
projections give uniqueness. The extra zero level in the upstream tower is zero.
(5) At each finite E coefficient, a |-> z_n tensor a is an isomorphism with inverse
z_n^j tensor a |-> ja, since l^n annihilates O_E/pi_E^n even for ramified E.
(6) These finite maps commute with coefficient reduction and root powers. Their
inverse limit and the condensed O_E limit comparison give b_E, with the specified
finite projections and uniqueness. No tensor is commuted with an infinite limit.
(7) Tensor b_T inverse with O_E and compose with b_E to obtain c_E. Its inverse
sends a e_E to a tensor e_T. Balancing gives precisely the finite-projection map
written above, and a map out of a free rank-one module is fixed by its generator.
(8) Extend the integral frame to E and the internal Tate frame to the actual
finite-subextension-valued Omega coefficient. The comparison sends z tensor
(a e_E) to z i_E(a)(1 tensor e_T), with inverse w(1 tensor e_T) |-> w tensor e_E.
This is the scalar extension of c_E inverse, characterized by that root formula.
(9) For E in F the same formula sends z tensor (a e_E) to z f(a)e_F.
For chains both composites send w tensor (z tensor (a e_E)) to w g(z)gf(a)e_G.
The same computation with final coefficient Omega proves its compatibility.
The balancing associator includes identity inclusions. All maps are on the
pulled-back condensed rings, and their restriction maps commute with these formulas. -/
theorem pur_condensed_internal_tate_frame (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (hprim : ∀ n : ℕ, IsPrimitiveRoot (z n : D.kˣ) (l ^ (n + 1)))
    (hcompat : ∀ n : ℕ, (z (n + 1) : D.kˣ) ^ l = (z n : D.kˣ)) :
    ∃ bT : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
        (Spec (.of D.k))) ≅ tateModule (Spec (.of D.k)) l,
      PurFrameTateNormalized D l z bT ∧
      (∀ bT', PurFrameTateNormalized D l z bT' → bT' = bT) ∧
      ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (iE : E →ₐ[ℚ_[l]] PadicAlgCl l),
        ∃ bE : Mod.regular (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) ≅
          coefficientIntegralTwistOne l E (Spec (.of D.k)),
          PurFrameIntegralNormalized D l z E bE ∧
          (∀ bE', PurFrameIntegralNormalized D l z E bE' → bE' = bE) ∧
          PurFrameCoefficientLaws D l z bT E iE bE := by
  obtain ⟨bT, hbT⟩ := purFrameTate_exists D l hl z hprim hcompat
  refine ⟨bT, hbT, fun bT' h ↦ purFrameTate_unique D l z bT' bT h hbT, ?_⟩
  intro E _ _ _ iE
  obtain ⟨bE, hbE⟩ := purFrameIntegral_exists D l hl z hprim hcompat E
  refine ⟨bE, hbE, fun bE' h ↦ purFrameIntegral_unique D l z E bE' bE h hbE, ?_⟩
  refine ⟨purFrameCompare_normalized _ _ _, purFrameCompare_unique _ _ _, ?_,
    purFrameCompare_normalized _ _ _, ?_⟩
  · intro n
    exact purFrameFiniteProjection_generic
      (coefficientMap (purFrameIntCondensedMap l E) (Spec (.of D.k)))
      (coefficientMap (twistReduction l E n) (Spec (.of D.k))) bT bE
      (limit.π (tateModuleSystem (Spec (.of D.k)) l) (op (n + 1)))
      (limit.π (coefficientIntegralTwistSystem l E (Spec (.of D.k))) (op n))
      (purFrameRoot D _ (z n)) (hbT n) (hbE n)
  · intro F _ _ _ iF f _ bF _
    refine ⟨purFrameCompare_normalized _ _ _, purFrameCompare_comp _ _ _ _ _, ?_⟩
    intro G _ _ _ iG g _ bG _
    exact purFrameCompare_comp _ _ _ _ _

end AlgebraicGeometry.ProEtale
