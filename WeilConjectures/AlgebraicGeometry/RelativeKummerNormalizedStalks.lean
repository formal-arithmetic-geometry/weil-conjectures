/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKummerNormalizedStalkDefinitions
import WeilConjectures.AlgebraicGeometry.RelativeKummerNormalizedStalksLocal
import WeilConjectures.AlgebraicGeometry.RelativeKummerNormalizedStalksGlobal
import WeilConjectures.AlgebraicGeometry.NormalizedKummerConstantMapIsIso
import WeilConjectures.AlgebraicGeometry.RelativeKummerConstantPullback
import WeilConjectures.AlgebraicGeometry.ModuleStrictLocalThetaIsIso
import WeilConjectures.AlgebraicGeometry.RelativeKummerNormalizedPullbackIsIso
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! Canonical normalized stalk comparison for the two line families.
(blueprint: lem-pur-relative-kummer-normalized-stalks). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
namespace AlgebraicGeometry.Etale

private theorem kummer_isZero_of_stalk
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}}
    (M : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hz : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      IsZero (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)).obj M)) :
    IsZero M := by
  have : IsIso (0 : M ⟶ 0) := Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦
    (NatIso.isIso_map_iff (GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
      (Scheme.pointSmallEtale (B.algClosurePoint x)) (ModuleCat.{u + 1} A)) _).2
        (isIso_of_source_target_iso_zero _
          (hz _ (B.algClosurePoint x)).isoZero
          (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))

private theorem kummer_vanishing_of_comparison
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (G : DerivedCategory.Plus (ModuleCat.{u + 1} A))
    (hΦ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      Nonempty (((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus.obj K ≅ G))
    (q : ℤ) (hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj G)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K) := by
  apply kummer_isZero_of_stalk A
  intro Ω _ _ s
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)
  obtain ⟨e⟩ := hΦ Ω s
  exact (hz.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e)).of_iso
    ((F.mapDerivedCategoryPlusHomologyFunctorIso q).app K)

private theorem kummer_isIso_of_stalk
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}}
    {M N : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)} (f : M ⟶ N)
    (hi : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      IsIso (((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} A)).map f)) : IsIso f := by
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro x
  exact (NatIso.isIso_map_iff (GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
    (Scheme.pointSmallEtale (B.algClosurePoint x)) (ModuleCat.{u + 1} A)) f).2
    (hi _ (B.algClosurePoint x))

private theorem kummer_homologyMap_of_stalkMap
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (μ : K ⟶ L) (q : ℤ)
    (hi : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
        (((Scheme.pointSmallEtale s).sheafFiber
          (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus.map μ))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map μ) := by
  apply kummer_isIso_of_stalk A
  intro Ω _ _ s
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)
  apply (NatIso.isIso_map_iff (F.mapDerivedCategoryPlusHomologyFunctorIso q) μ).2
  exact hi Ω s

private theorem kummer_zero_map_isIso
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] (hmk : IsUnit (m : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {B : Scheme.{u}} (p : B ⟶ Spec (.of k)) (b : Bool)
    (hs : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      RelativeKummerNormalizedStalk A m hm hA hmk hζ p b s)
    (ha : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerGlobalSection A m hA _
        (normalizedKummerConstantMap A m hm hA hζ _ (KummerLine.structureMap k b))))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerUntwistedUnit A m hm hA hζ p
        (normalizedKummerProjection p b) (relativeKummerExponentUnit m hmk B p)
        (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)))) := by
  apply kummer_homologyMap_of_stalkMap A
  intro Ω _ _ s
  have hss := hs Ω s
  rw [RelativeKummerNormalizedStalk] at hss
  obtain ⟨_, Φ, _, _, hu, _⟩ := hss
  have hu0 := congrArg ((DerivedCategory.Plus.homologyFunctor _ 0).map) hu
  simp only [Functor.map_comp] at hu0
  have hi : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerUnitGerm A m hm hA hζ p (normalizedKummerProjection p b)
        (relativeKummerExponentUnit m hmk B p)
        (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)) s)) := by
    have : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
          (normalizedKummerUnitGerm A m hm hA hζ p (normalizedKummerProjection p b)
            (relativeKummerExponentUnit m hmk B p)
            (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)) s) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map Φ.hom) := hu0.symm ▸ ha
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.homologyFunctor _ 0).map Φ.hom)
  rw [normalizedKummerUnitGerm] at hi
  simp only [Functor.map_comp] at hi
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) 0
  have : IsIso (H.map ((Functor.mapDerivedCategoryPlusSingleFunctor F 0).inv.app _)
      ≫ H.map (F.mapDerivedCategoryPlus.map
        (normalizedKummerUntwistedUnit A m hm hA hζ p (normalizedKummerProjection p b)
          (relativeKummerExponentUnit m hmk B p)
          (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b))))) := by
    exact IsIso.of_isIso_comp_left
      (H.map ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of A A)).inv)) _
  exact IsIso.of_isIso_comp_left
    (H.map ((Functor.mapDerivedCategoryPlusSingleFunctor F 0).inv.app _)) _

private theorem kummer_untwistedUnit_isIso
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] (hmk : IsUnit (m : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {B : Scheme.{u}} (p : B ⟶ Spec (.of k))
    (hzero : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerUntwistedUnit A m hm hA hζ p
        (normalizedKummerProjection p false) (relativeKummerExponentUnit m hmk B p)
        (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p false)))))
    (hvan : ∀ q : ℕ, q ≠ 0 → IsZero
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (normalizedKummerImage A m hA (normalizedKummerProjection p false)))) :
    IsIso (normalizedKummerUntwistedUnit A m hm hA hζ p
      (normalizedKummerProjection p false) (relativeKummerExponentUnit m hmk B p)
      (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p false))) := by
  apply (DerivedCategory.Plus.isIso_iff _).mpr
  intro q
  by_cases hq : q = 0
  · subst q; exact hzero
  · apply isIso_of_source_target_iso_zero
    · by_cases hneg : q < 0
      · exact (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hneg).isoZero
      · exact (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q
          (lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hq))).isoZero
    · by_cases hneg : q < 0
      · exact (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
          (lowerStar (ModuleCat.{u + 1} A) (normalizedKummerProjection p false))
          (relativeKummerLinePlus A m hA _) 0 hneg).isoZero
      · have hnat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (le_of_not_gt hneg)
        have hnz : q.toNat ≠ 0 := by
          intro heq
          have : q = 0 := by simpa only [heq, Nat.cast_zero] using hnat.symm
          exact hq this
        exact (hnat ▸ hvan q.toNat hnz).isoZero

private theorem normalizedKummerStalk_of_comparison
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] (hmk : IsUnit (m : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {B : Scheme.{u}} (p : B ⟶ Spec (.of k)) (b : Bool)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)
    (hg : match b with
      | false => True
      | true =>
        normalizedKummerGeneratorPlusMap A m hA _
            (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))
            (Units.map (pullback.fst (KummerLine.structureMap k true) p).appTop.hom.toMonoidHom
              (KummerLine.coordinateUnit k)) ≫
          (DerivedCategory.Plus.homologyFunctor _ 1).map
            (normalizedKummerV A m hm hA hmk p true s) =
        normalizedKummerGeneratorPlusMap A m hA _
            (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k true))
            (KummerLine.coordinateUnit k) ≫
          (DerivedCategory.Plus.homologyFunctor _ 1).map
            (normalizedKummerH A m hm hA hmk p true s))
    (hh : IsIso (normalizedKummerH A m hm hA hmk p b s))
    (ht : IsIso (normalizedKummerTheta A m hm hA hmk p b s))
    (he : ∀ q : ℕ,
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerEdgeGerm A m hA (normalizedKummerProjection p b) s) ≫
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerTheta A m hm hA hmk p b s) =
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerV A m hm hA hmk p b s))
    (hu : normalizedKummerUnitGerm A m hm hA hζ p (normalizedKummerProjection p b)
        (relativeKummerExponentUnit m hmk B p)
        (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)) s ≫
        normalizedKummerTheta A m hm hA hmk p b s =
      normalizedKummerGlobalSection A m hA _
          (normalizedKummerConstantMap A m hm hA hζ _ (KummerLine.structureMap k b)) ≫
        normalizedKummerH A m hm hA hmk p b s) :
    RelativeKummerNormalizedStalk A m hm hA hmk hζ p b s := by
  let Φ := asIso (normalizedKummerTheta A m hm hA hmk p b s) ≪≫
    (asIso (normalizedKummerH A m hm hA hmk p b s)).symm
  have hΦ : Φ.hom ≫ normalizedKummerH A m hm hA hmk p b s =
      normalizedKummerTheta A m hm hA hmk p b s := by
    simp [Φ]
  rw [RelativeKummerNormalizedStalk]
  refine ⟨hh, Φ, hΦ, ?_, ?_, ?_⟩
  · intro q
    rw [← Functor.map_comp, hΦ]
    exact he q
  · apply (cancel_mono (normalizedKummerH A m hm hA hmk p b s)).1
    simpa only [Category.assoc, hΦ] using hu
  · cases b with
    | false => trivial
    | true =>
      apply (cancel_mono ((DerivedCategory.Plus.homologyFunctor _ 1).map
        (normalizedKummerH A m hm hA hmk p true s))).1
      calc
        _ = normalizedKummerGeneratorPlusMap A m hA _
              (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))
              (Units.map
                (pullback.fst (KummerLine.structureMap k true) p).appTop.hom.toMonoidHom
                (KummerLine.coordinateUnit k)) ≫
            (DerivedCategory.Plus.homologyFunctor _ 1).map
              (normalizedKummerV A m hm hA hmk p true s) := by
          rw [Category.assoc, Category.assoc, ← Functor.map_comp, hΦ]
          erw [he 1]
          rfl
        _ = _ := hg

private theorem kummer_relativeGenerator_isIso
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] (hmk : IsUnit (m : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {B : Scheme.{u}} (p : B ⟶ Spec (.of k))
    (hs : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      RelativeKummerNormalizedStalk A m hm hA hmk hζ p true s)
    (ha : IsIso (normalizedKummerGeneratorMap A m hA _
      (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k true))
      (KummerLine.coordinateUnit k))) :
    IsIso (normalizedKummerRelativeGenerator A m hA p
      (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))) := by
  apply kummer_isIso_of_stalk A
  intro Ω _ _ s
  have hss := hs Ω s
  rw [RelativeKummerNormalizedStalk] at hss
  obtain ⟨_, Φ, _, _, _, hg⟩ := hss
  have he := relativeKummer_normalized_stalks_global A m hA hmk p Ω s
  have hi : IsIso (normalizedKummerGeneratorPlusMap A m hA _
      (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k true))
      (KummerLine.coordinateUnit k)) := by
    rw [normalizedKummerGeneratorPlusMap]
    infer_instance
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)
  let c := (Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of A A)
  let μ := normalizedKummerRelativeGenerator A m hA p
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))
  let t := F.map ((DerivedCategory.homologyFunctor _ 1).map
      ((lowerStar (ModuleCat.{u + 1} A)
        (normalizedKummerProjection p true)).rightDerivedFunctorPlusCompatibility.inv.app
          (relativeKummerLinePlus A m hA _))) ≫
    (F.mapDerivedCategoryPlusHomologyFunctorIso 1).hom.app
      (normalizedKummerImage A m hA (normalizedKummerProjection p true)) ≫
    (DerivedCategory.Plus.homologyFunctor _ 1).map Φ.hom
  have hcomp : c.inv ≫ F.map μ ≫ t =
      normalizedKummerGeneratorPlusMap A m hA _
        (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k true))
        (KummerLine.coordinateUnit k) := by
    have hep := congrArg
      (fun f => f ≫ (DerivedCategory.Plus.homologyFunctor _ 1).map Φ.hom) he
    have hepg := hep.trans (by simpa only [Category.assoc] using hg)
    simpa only [t, c, μ, F, Category.assoc] using hepg
  have : IsIso (c.inv ≫ F.map μ ≫ t) := hcomp.symm ▸ hi
  have : IsIso (F.map μ ≫ t) := IsIso.of_isIso_comp_left c.inv _
  exact IsIso.of_isIso_comp_right _ t

/-- The canonical normalized comparison for every geometric stalk of either line
family, including its conservative-stalk consequences and restriction of constants.
Source: blueprint latest, prop-pur-gm-relative-kummer.proof.md, Step 2; Stacks 03Q9
(blueprint: lem-pur-relative-kummer-normalized-stalks).

Proof plan: The projections are affine and hence qcqs. The small affine-neighbourhood
strict localization is strictly henselian, so its section functor is exact. Restriction
followed by exchange and Leray is the abelian strict-local stalk comparison after
forgetting scalars; scalar forgetting detects its invertibility. Strict-local Kummer
invariance makes the actual h-pullback invertible. Compose the first comparison with
its inverse to obtain Phi. Restriction of a global cocycle, exchange, and exact sections
carry its edge germ to v-pullback, proving the all-degree formula. The unit sends a to
zeta tensor a. Naturality of the ordinary abelian Kummer boundary, then the scalar
insertion, gives the coordinate formula. Conservative geometric stalks now detect the
asserted relative isomorphisms and vanishings. The connective derived criterion gives
both line units. Finally localization k[t] -> k[t,t^-1] fixes the constant root and its
scalar multiples. No geometric-fibre base-change theorem defines Phi.
-/
theorem relativeKummer_normalized_stalks (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (_hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Free (ZMod (ℓ ^ N)) A] [Module.Finite (ZMod (ℓ ^ N)) A]
    (ζ : k) (hζ : IsPrimitiveRoot ζ (ℓ ^ N))
    (B : Scheme.{u}) (p : B ⟶ Spec (.of k)) :
    let m := ℓ ^ N
    let hm := relativeKummerPositive ℓ N hℓ
    let hA := relativeKummerAnnihilator A m
    let hmk := relativeKummerFieldExponentUnit ℓ N hℓk
    let hB := relativeKummerExponentUnit m hmk B p
    let hC := fun b => relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k b)
    let hCB := fun b => relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)
    let abs0 := fun b => (DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerGlobalSection A m hA _
        (normalizedKummerConstantMap A m hm hA hζ _ (KummerLine.structureMap k b)))
    let rel0 := fun b => (DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerUntwistedUnit A m hm hA hζ p
        (normalizedKummerProjection p b) hB (hCB b))
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      ∀ b : Bool, RelativeKummerNormalizedStalk A m hm hA hmk hζ p b s) ∧
    ((IsIso (abs0 false) ∧
      (∀ q : ℕ, q ≠ 0 → IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (normalizedKummerGlobal A m hA (KummerLine.curve k false))))) →
      IsIso (relativeKummerUnit A m hm hA (normalizedKummerProjection p false)
        hB (hCB false)) ∧
      IsIso (normalizedKummerUntwistedUnit A m hm hA hζ p
        (normalizedKummerProjection p false) hB (hCB false)) ∧
      IsIso (rel0 false) ∧
      (∀ q : ℕ, q ≠ 0 → IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (normalizedKummerImage A m hA (normalizedKummerProjection p false))))) ∧
    ((IsIso (abs0 true) ∧
      IsIso (normalizedKummerGeneratorMap A m hA _ (hC true) (KummerLine.coordinateUnit k)) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 1 →
        IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (normalizedKummerGlobal A m hA (KummerLine.curve k true))))) →
      IsIso (rel0 true) ∧
      IsIso (normalizedKummerRelativeGenerator A m hA p (hCB true)) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 1 →
        IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (normalizedKummerImage A m hA (normalizedKummerProjection p true))))) ∧
    (∀ a : A,
      relativeKummerCohomologyPullback A m hm hA (normalizedKummerInclusion p)
        (hCB false) (hCB true) 0
        (relativeKummerConstant A m hm hA hζ _ (normalizedKummerStructure p false) a) =
      relativeKummerConstant A m hm hA hζ _ (normalizedKummerStructure p true) a) := by
  dsimp only
  have hs : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      ∀ b : Bool, RelativeKummerNormalizedStalk A (ℓ ^ N) (relativeKummerPositive ℓ N hℓ)
        (relativeKummerAnnihilator A (ℓ ^ N)) (relativeKummerFieldExponentUnit ℓ N hℓk)
        hζ p b s := by
    intro Ω _ _ s b
    obtain ⟨he, hu, hg⟩ := relativeKummer_normalized_stalks_local A (ℓ ^ N)
      (relativeKummerPositive ℓ N hℓ) (relativeKummerAnnihilator A (ℓ ^ N))
      (relativeKummerFieldExponentUnit ℓ N hℓk) hζ p Ω s b
    have hh := normalizedKummerH_isIso k ℓ N hℓ _hN hℓk A ζ hζ B p s b
    have : IsAffine (KummerLine.curve k b) := by
      cases b <;> dsimp [KummerLine.curve] <;> infer_instance
    have : IsAffineHom (KummerLine.structureMap k b) := inferInstance
    have : IsAffineHom (normalizedKummerProjection p b) :=
      MorphismProperty.pullback_snd _ _ ‹_›
    exact normalizedKummerStalk_of_comparison A (ℓ ^ N) (relativeKummerPositive ℓ N hℓ)
      (relativeKummerAnnihilator A (ℓ ^ N)) (relativeKummerFieldExponentUnit ℓ N hℓk)
      hζ p b s hg hh (by
        rw [normalizedKummerTheta]
        exact moduleStrictLocalTheta_isIso A _ s _ _ _) he hu
  let m := ℓ ^ N
  let hm := relativeKummerPositive ℓ N hℓ
  let hA := relativeKummerAnnihilator A m
  let hmk := relativeKummerFieldExponentUnit ℓ N hℓk
  have hc := normalizedKummerConstantMap_isIso A m hm hA hζ B p
  have hiOver : normalizedKummerInclusion p ≫ normalizedKummerStructure p false =
      normalizedKummerStructure p true := by
    simp only [normalizedKummerInclusion, normalizedKummerStructure, Category.assoc,
      pullback.map, pullback.lift_fst_assoc, normalizedKummerInclusion_over]
  have hconst (a : A) := relativeKummer_constant_pullback A m hm hA hζ
    (normalizedKummerInclusion p) (normalizedKummerStructure p false)
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p false))
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true)) a
  simp only [hiOver] at hconst
  have hv (b : Bool) (q : ℕ)
      (hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (normalizedKummerGlobal A m hA (KummerLine.curve k b)))) :
      IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (normalizedKummerImage A m hA (normalizedKummerProjection p b))) := by
    apply kummer_vanishing_of_comparison A _ _ ?_ (q : ℤ) hz
    intro Ω _ _ s
    have hss := hs Ω s b
    rw [RelativeKummerNormalizedStalk] at hss
    obtain ⟨_, Φ, _⟩ := hss
    exact ⟨Φ⟩
  refine ⟨hs, ?_, ?_, hconst⟩
  · rintro ⟨ha, hz⟩
    have hrel0 := kummer_zero_map_isIso A m hm hA hmk hζ p false
      (fun Ω _ _ s => hs Ω s false) ha
    have hvan := fun q hq => hv false q (hz q hq)
    have hi := kummer_untwistedUnit_isIso A m hm hA hmk hζ p hrel0 hvan
    refine ⟨?_, hi, hrel0, hvan⟩
    rw [normalizedKummerUntwistedUnit] at hi
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.Plus.singleFunctor _ 0).map
        (normalizedKummerConstantMap A m hm hA hζ B p)) _
  · rintro ⟨ha, hg, hz⟩
    refine ⟨kummer_zero_map_isIso A m hm hA hmk hζ p true
      (fun Ω _ _ s => hs Ω s true) ha, ?_, ?_⟩
    · exact kummer_relativeGenerator_isIso A m hm hA hmk hζ p
        (fun Ω _ _ s => hs Ω s true) hg
    · intro q hq0 hq1
      exact hv true q (hz q hq0 hq1)

end AlgebraicGeometry.Etale
