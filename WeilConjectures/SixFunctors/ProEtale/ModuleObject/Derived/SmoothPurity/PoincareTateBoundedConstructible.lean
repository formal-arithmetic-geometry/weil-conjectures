/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.AlgebraicGeometry.Tate.TateTwistOneLocalLine
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleShiftSingle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian

/-!
# Bounded constructibility of shifted condensed Tate twists

Source: archived upstream `WeilConjectures/PoincareDuality/Poincare.lean`,
`boundedConstructible_tateTwistDerived`, with the invertibility hypothesis of the current
blueprint `sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md`
(blueprint: nt-target-poincare-tate-bc).

The conclusion uses the ordinary unbounded derived category of internal modules over the
finite-subextension-valued condensed coefficient ring. Constructibility is the upstream
finite-stratification predicate, without any finiteness assumption on the scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonoidalClosed Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Mod.monoidalClosed

private noncomputable def concreteHomIso
    {Y : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) :
    ihom M ≅ Mod.ihom' R M :=
  (ihom.adjunction M).rightAdjointUniq
    ((Mod.ihom'Adjunction R M).ofNatIsoLeft
      (Mod.relativeTensorRightIso M ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight M).symm))

private theorem nonempty_pullback_ihom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Nonempty (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj ((ihom M).obj N) ≅
      (ihom (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj M)).obj
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj N)) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let F := G.mapMod R
  let : G.Braided := {}
  let e : F ⋙ Mod.comap (𝟙 (G.obj R)) ≅ F :=
    Functor.isoWhiskerLeft F (Mod.comapId _) ≪≫ Functor.rightUnitor F
  have : ∀ Z, IsIso (Functor.LaxMonoidal.ihomComparison G Z).natTrans :=
    ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} f
  have := Mod.isIso_mapIhom'Hom G (𝟙 (G.obj R)) M N
  exact ⟨F.mapIso ((concreteHomIso R M).app N) ≪≫
    (e.app ((Mod.ihom' R M).obj N)).symm ≪≫
    asIso (Mod.mapIhom'Hom G (𝟙 (G.obj R)) M N) ≪≫
    ((concreteHomIso _ _).app _).symm ≪≫
    asIso ((pre (e.app M).inv).app _) ≪≫ (ihom _).mapIso (e.app N)⟩

private theorem powers_image_regular
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    {Z : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]
    (e : (((ProEtale.upperStar Ab.{u + 1} g).mapMod
      ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))).obj
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj
          (tateTwistOne X ℓ))) ≅ 𝟙_ _) (d : ℤ) :
    Nonempty ((((ProEtale.upperStar Ab.{u + 1} g).mapMod
      ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))).obj
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj
          (tateTwist X ℓ d))) ≅ 𝟙_ _) := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
  let F := ProEtale.upperStar Ab.{u + 1} f
  let G := ProEtale.upperStar Ab.{u + 1} g
  let : F.Braided := {}
  let : G.Braided := {}
  let H := F.mapMod R ⋙ G.mapMod (F.obj R)
  have hn (n : ℕ) : Nonempty (H.obj (tateTwistNat X ℓ n) ≅ 𝟙_ _) := by
    induction n with
    | zero => exact ⟨Functor.Monoidal.εIso H |>.symm⟩
    | succ n hn =>
      exact ⟨(Functor.Monoidal.μIso H _ _).symm ≪≫
        tensorIso hn.some e ≪≫ λ_ _⟩
  cases d with
  | ofNat n => exact hn n
  | negSucc n =>
    obtain ⟨hf⟩ := nonempty_pullback_ihom f R (tateTwistNat X ℓ (n + 1)) (𝟙_ _)
    obtain ⟨hg⟩ := nonempty_pullback_ihom g (F.obj R)
      ((F.mapMod R).obj (tateTwistNat X ℓ (n + 1))) ((F.mapMod R).obj (𝟙_ _))
    exact ⟨(G.mapMod (F.obj R)).mapIso hf ≪≫ hg ≪≫
      asIso ((pre (hn (n + 1)).some.inv).app _) ≪≫
      (ihom _).mapIso (Functor.Monoidal.εIso H).symm ≪≫
      MonoidalClosed.unitIsoSelf _⟩

private lemma finitelyPresented_of_regular_iso
    {Y : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R}
    (e : M ≅ Mod.regular R) : Mod.IsFinitelyPresented R M := by
  refine ⟨1, 0, 0, ⟨?_⟩⟩
  exact e ≪≫ (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular R)).symm ≪≫
    (cokernelZeroIsoTarget (X := Mod.finiteFree R 0)).symm

/-- Every integer shift of the actual condensed Tate twist is bounded constructible when
ell is invertible on the scheme. Source: archived upstream Poincare.lean, the lemma
`boundedConstructible_tateTwistDerived`, and current blueprint `sk-def-sp-tate-twist`
(blueprint: nt-target-poincare-tate-bc).

Proof (the five steps of the node):
1. The residue-field hypothesis makes ell a unit in every stalk, hence in Gamma(X, O_X) by
   the ringed-space stalk criterion. The proved first-twist local line
   `lem-poincare-first-twist-pullback-local-line`, applied to id_X, gives a pro-etale
   cover on whose members the two raw inverse images of tateTwistOne are regular.
2. By induction on n, using the unit and tensor comparisons of the monoidal inverse
   images, the image of tateTwistNat n is regular (`powers_image_regular`).
3. For a weakly etale inverse image the internal-Hom comparison is an isomorphism
   (`nonempty_pullback_ihom`, through the concrete module internal Hom `Mod.ihom'`);
   with `MonoidalClosed.unitIsoSelf` the negative signed twists are regular on the
   same cover.
4. On the single stratum X with identity immersion, a regular module has the rank-one
   presentation with zero relations, so every signed twist is constructible in the
   sense of `def-sfb-constructible-module`, with no finiteness assumption on X.
5. `lem-poincare-constructible-shift-single` turns this into bounded constructibility of
   every shift of the degree-zero single complex tateTwistDerived.
-/
theorem boundedConstructible_tateTwistDerived_of_invertible
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((shiftFunctor _ n).obj (tateTwistDerived X ℓ d)) := by
  classical
  have hℓ : IsUnit (ℓ : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simp only [map_natCast]
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (ℓ : X.residueField x)).ne_zero
  obtain ⟨𝒰, h𝒰⟩ := tateTwistOne_pullback_locally_trivial X ℓ hℓ (𝟙 X)
  have hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (tateTwist X ℓ d) := by
    let S : Scheme.Stratification X :=
      { n := 1
        stratum := fun _ ↦ Set.univ
        isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
        isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
        iUnion_stratum_eq_univ := Set.iUnion_const _
        pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
        domain := fun _ ↦ X
        immersion := fun _ ↦ 𝟙 X
        range_immersion := fun _ ↦ Set.range_id' }
    refine ⟨S, fun a ↦ ⟨𝒰, fun i ↦ ?_⟩⟩
    have : WeaklyEtale (𝒰.f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
    exact finitelyPresented_of_regular_iso _
      (powers_image_regular X ℓ (𝟙 X) (𝒰.f i) (h𝒰 i).some d).some
  exact boundedConstructible_shift_single _ (tateTwist X ℓ d) hM n

end AlgebraicGeometry.ProEtale.CondensedRing
