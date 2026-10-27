/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R5
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import Sheaf.SixFunctors.GrothendieckTorsionProperBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-! # Objectwise compact-support comparisons for constructible torsion coefficients -/

@[expose] public section

set_option autoImplicit false

universe u' u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

private def StalkwiseFiniteExponent {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  ∀ (n : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
    ∃ N : ℕ, 0 < N ∧ N • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj
      ((_root_.DerivedCategory.homologyFunctor _ n).obj K))) = 0

omit [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [HasSmallSiteSheafify A] in
private lemma finiteExponent_of_iso {M N : A} (e : M ≅ N)
    (h : ∃ n : ℕ, 0 < n ∧ n • (𝟙 N) = 0) :
    ∃ n : ℕ, 0 < n ∧ n • (𝟙 M) = 0 := by
  obtain ⟨n, hn, he⟩ := h
  refine ⟨n, hn, ?_⟩
  apply (cancel_mono e.hom).1
  calc
    (n • 𝟙 M) ≫ e.hom = e.hom ≫ (n • 𝟙 N) := by simp
    _ = (0 : M ⟶ M) ≫ e.hom := by rw [he]; simp

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
private lemma stalkwiseFiniteExponent_of_iso {X : Scheme.{u}}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (e : K ≅ L) (h : StalkwiseFiniteExponent A L) : StalkwiseFiniteExponent A K := by
  intro n Ω _ _ t
  exact finiteExponent_of_iso A ((Scheme.pointSmallEtale t).sheafFiber.mapIso
    ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e)) (h n Ω t)

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
private lemma stalkwiseFiniteExponent_mapDerivedUpperStar {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : StalkwiseFiniteExponent A K) :
    StalkwiseFiniteExponent A (D((f)^*[A]).obj K) := by
  intro n Ω _ _ s
  exact finiteExponent_of_iso A
    (((Scheme.pointSmallEtale s).sheafFiber.mapIso
      ((((f)^*[A]).mapDerivedCategoryHomologyFunctorIso n).symm.app K)) ≪≫
      (upperStarCompSheafFiberIso A f s).app
        ((_root_.DerivedCategory.homologyFunctor _ n).obj K)) (h n Ω (s ≫ f))

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
private lemma stalkwiseFiniteExponent_openImmersionLowerShriek {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : StalkwiseFiniteExponent A K) :
    StalkwiseFiniteExponent A (D((j)_!open[A]).obj K) := by
  intro n Ω _ _ s
  let F := (_root_.DerivedCategory.homologyFunctor _ n).obj K
  apply finiteExponent_of_iso A
    ((Scheme.pointSmallEtale s).sheafFiber.mapIso
      ((((j)_!open[A]).mapDerivedCategoryHomologyFunctorIso n).symm.app K))
  by_cases hs : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range j.base
  · have hr : Set.range s.base ⊆ Set.range j.base := by
      rintro _ ⟨p, rfl⟩
      simpa only [Subsingleton.elim p (IsLocalRing.closedPoint Ω)] using hs
    let t := IsOpenImmersion.lift j s hr
    have ht : t ≫ j = s := IsOpenImmersion.lift_fac j s hr
    rw [← ht]
    exact finiteExponent_of_iso A
      (((Scheme.pointSmallEtale (t ≫ j)).uliftSheafFiberIso.{u + 1} A).symm.app _ ≪≫
        (openImmersionLowerShriekCompUliftSheafFiberIso A j t).app F ≪≫
        ((Scheme.pointSmallEtale t).uliftSheafFiberIso.{u + 1} A).app F) (h n Ω t)
  · have hz := isZero_uliftSheafFiber_openImmersionLowerShriek_obj A j s hs F
    have hz' := hz.of_iso (((Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1} A).symm.app _)
    exact ⟨1, by omega, by simpa using hz'.eq_of_src (𝟙 _) 0⟩

private lemma unit_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hT : StalkwiseFiniteExponent A K) :
    IsIso ((mapDerivedUpperStarLowerStarAdjunction A r.hom).unit.app
      (D((d.i)_!open[A]).obj K)) := by
  apply (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar' A d.i d.i.closedComplement
    d.i.range_closedComplement).isIso_of_pairFunctor
  · have : D((d.i)_!open[A]).Full :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).fullyFaithfulLOfIsIsoUnit.full
    have : D((d.i)_!open[A]).Faithful :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).fullyFaithfulLOfIsIsoUnit.faithful
    have : D((c.i)_!open[A]).Full :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).fullyFaithfulLOfIsIsoUnit.full
    have : D((c.i)_!open[A]).Faithful :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).fullyFaithfulLOfIsIsoUnit.faithful
    have : (D((d.i)_!open[A]) ⋙ D((r.hom)^*[A])).Full :=
      Functor.Full.of_iso (refinementLowerShriekBaseChangeDerivedIso A r hcart)
    have : (D((d.i)_!open[A]) ⋙ D((r.hom)^*[A])).Faithful :=
      Functor.Faithful.of_iso (refinementLowerShriekBaseChangeDerivedIso A r hcart)
    exact Adjunction.isIso_map_unit_app_obj _
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i) K
  · have hdisj : Disjoint (Set.range d.i.closedComplement.base) (Set.range d.i.base) := by
      rw [d.i.range_closedComplement]
      exact disjoint_compl_left
    refine isIso_of_source_target_iso_zero _
      (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range A d.i
        d.i.closedComplement hdisj K).isoZero (IsZero.isoZero ?_)
    let sq := IsPullback.of_hasPullback r.hom d.i.closedComplement
    let N := D((r.hom)^*[A]).obj (D((d.i)_!open[A]).obj K)
    have hNb : _root_.DerivedCategory.TStructure.t.bounded N :=
      Functor.bounded_mapDerivedCategory_obj _ (Functor.bounded_mapDerivedCategory_obj _ hK)
    have hNt : StalkwiseFiniteExponent A N :=
      stalkwiseFiniteExponent_mapDerivedUpperStar A r.hom _
        (stalkwiseFiniteExponent_openImmersionLowerShriek A d.i K hT)
    have := isIso_derivedBaseChangeMap_of_bounded_stalkwise_finite_exponent A sq N hNb hNt
    have hN : IsZero (L((pullback.fst r.hom d.i.closedComplement)^*[A]).obj N) := by
      refine IsZero.of_iso ?_
        ((leftDerivedUpperStarIsoMapDerivedCategory A _).app N ≪≫
          ((Functor.mapDerivedCategoryNatIso (upperStarComp A
            (pullback.fst r.hom d.i.closedComplement) r.hom) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).app _).symm)
      refine isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
        A d.i _ (hdisj.mono_left ?_) K
      rw [pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp]
      exact Set.range_comp_subset_range _ _
    exact IsZero.of_iso
      ((R((pullback.snd r.hom d.i.closedComplement)_*[A])).map_isZero hN)
      ((leftDerivedUpperStarIsoMapDerivedCategory A _).symm.app _ ≪≫
        asIso ((derivedBaseChangeMap A sq.toCommSq).app N))

private lemma comparison_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hT : StalkwiseFiniteExponent A K) :
    IsIso ((rightDerivedLowerShriekOfCompactificationComparison A r hcart).app K) := by
  have := unit_isIso A r hcart K hK hT
  dsimp [rightDerivedLowerShriekOfCompactificationComparison]
  infer_instance

private noncomputable def compactificationIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hT : StalkwiseFiniteExponent A K) :
    (Rf_!(c)[A]).obj K ≅ (Rf_!(d)[A]).obj K := by
  have := comparison_isIso A (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) K hK hT
  have := comparison_isIso A (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) K hK hT
  exact asIso ((rightDerivedLowerShriekOfCompactificationComparison A
    (Compactification.infFst c d) (Compactification.isPullback_infFst c d)).app K) ≪≫
    (asIso ((rightDerivedLowerShriekOfCompactificationComparison A
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d)).app K)).symm

/-- Compact-support base change at a finite-Tor constructible input.

Source: the current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
proof step (3), using compact-support base change sk-prop-sf-cbc.
(blueprint: lem-sf-constructible-compact-support-base-change).

Proof: base change a compactification of f along g. For the proper factor apply torsion
proper base change; for the open factor apply exact base change for extension by zero.
These comparisons identify the pullback of the chosen compact-support candidate for f
with the candidate for the base-changed compactification. Compare this latter candidate
with the chosen compactification of the second projection, using a common proper
refinement. Its comparison is invertible by the same proper base-change theorem, since
the geometric homology stalks have the explicit positive annihilators in the hypothesis.
Composition of these comparisons yields the asserted exchange isomorphism at K. -/
theorem nonempty_iso_constructible_compact_support_base_change
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hT : ∀ (n : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ X), ∃ N : ℕ, 0 < N ∧
        N • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj
          ((_root_.DerivedCategory.homologyFunctor _ n).obj K))) = 0) :
    Nonempty ((L((g)^*[A])).obj ((R(f)_![A]).obj K) ≅
      (R(pullback.snd f g)_![A]).obj ((L((pullback.fst f g)^*[A])).obj K)) := by
  let c := HasCompactification.compactification f
  let sq := IsPullback.of_hasPullback f g
  have hb : _root_.DerivedCategory.TStructure.t.bounded
      (D((c.i)_!open[A]).obj K) := Functor.bounded_mapDerivedCategory_obj _ hK.1.1
  have ht := stalkwiseFiniteExponent_openImmersionLowerShriek A c.i K hT
  have := isIso_derivedBaseChangeMap_of_bounded_stalkwise_finite_exponent A
    (IsPullback.of_hasPullback c.g g) _ hb ht
  have hx : IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c).app K) := by
    dsimp [rightDerivedLowerShriekOfCompactificationBaseChangeMap]
    infer_instance
  let M := (L((pullback.fst f g)^*[A])).obj K
  let e := (leftDerivedUpperStarIsoMapDerivedCategory A (pullback.fst f g)).app K
  have hMb : _root_.DerivedCategory.TStructure.t.bounded M :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm
      (Functor.bounded_mapDerivedCategory_obj _ hK.1.1)
  have hMt : StalkwiseFiniteExponent A M :=
    stalkwiseFiniteExponent_of_iso A e
      (stalkwiseFiniteExponent_mapDerivedUpperStar A _ K hT)
  exact ⟨asIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c).app K) ≪≫
    compactificationIso A (c.ofIsPullback sq)
      (HasCompactification.compactification (pullback.snd f g)) M hMb hMt⟩

end AlgebraicGeometry.Etale
