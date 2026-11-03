/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale

import WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeLineTensorFiniteness

/-! # Tate twists preserve finiteness conditions

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/sk-prop-sp-et-proet/
prop-weil-twist-preserves.md` (blueprint: prop-weil-twist-preserves).

The four coefficient families are the finite, integral, rational and algebraically closed
pulled-back condensed rings from `def-coefficient-twists-detailed`. The statement records,
for every signed twist, local triviality, invertibility, preservation of finite constant
scalar-model bounded constructibility, and preservation of finite Tor amplitude.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem firstLine_scalarExtension {X : Scheme.{u}}
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (h : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Nonempty (((upperStar Ab.{u + 1} (C.f i)).mapMod R).obj L ≅ Mod.regular _)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Nonempty (((upperStar Ab.{u + 1} (C.f i)).mapMod S).obj
        ((Mod.extendScalars.{u + 1, u + 2} a).obj L) ≅ Mod.regular _) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ⟨?_⟩⟩
  exact (pullbackExtendScalarsComparison (C.f i) R S a).app L ≪≫
    (Mod.extendScalars.{u + 1, u + 2} ((upperStar Ab.{u + 1} (C.f i)).map a)).mapIso (hC i).some ≪≫
    Mod.regularExtensionIso.{u + 2, u + 1} _

-- Prove the cover argument here: the interface snapshot lacks the private main helpers.

private theorem signed_finiteness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Nonempty (((upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj Λ X)).obj
        L ≅ Mod.regular _)) :
    (∀ m : ℤ, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Nonempty (((upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj Λ X)).obj
        (coefficientSignedTwist X (condensedRingObj Λ X) L m) ≅ Mod.regular _)) ∧
    (∀ m : ℤ, IsInvertible (coefficientSignedTwist X (condensedRingObj Λ X) L m)) ∧
    (∀ m K, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X
        (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
          (coefficientSignedTwist X (condensedRingObj Λ X) L m))) ∧
    (∀ m K, _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
      _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
        (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
          (coefficientSignedTwist X (condensedRingObj Λ X) L m))) := by
  have h := nativeSignedLine (condensedRingObj Λ X) L hL
  exact ⟨h.1, h.2.2.1,
    fun m ↦ (line_finiteness Λ _ (h.2.1 m)).1,
    fun m ↦ (line_finiteness Λ _ (h.2.1 m)).2⟩

private theorem constructible_tensor_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsConstantModelConstructible Λ X F) (hL : IsLisseCoefficientModule Λ L) :
    IsConstantModelConstructible Λ X (F ⊗ L) := by
  classical
  unfold IsConstantModelConstructible at hF ⊢
  split_ifs at hF ⊢ with hX
  · exact stratified_tensor_lisse Λ F L hF hL
  · intro U hU
    let H := CondensedRing.upperStar Λ U.ι
    have hLU : IsLisseCoefficientModule Λ (H.obj L) :=
      (isLocallyFree_iff _).mp (((isLocallyFree_iff L).mpr hL).upperStar Λ _)
    exact stratified_of_iso Λ (Functor.Monoidal.μIso H F L)
      (stratified_tensor_lisse Λ (H.obj F) (H.obj L) (hF U hU) hLU)

private theorem stratified_tensor_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsFiniteConstantStratified Λ X F) (hL : IsLisseCoefficientModule Λ L) :
    IsFiniteConstantStratified Λ X (F ⊗ L) := by
  obtain ⟨S, hS⟩ := hF
  refine ⟨S, fun a ↦ ?_⟩
  let H := CondensedRing.upperStar Λ (S.immersion a)
  have hLa : IsLisseCoefficientModule Λ (H.obj L) :=
    (isLocallyFree_iff _).mp (((isLocallyFree_iff L).mpr hL).upperStar Λ _)
  exact model_of_iso Λ (Functor.Monoidal.μIso H F L)
    (model_tensor_lisse Λ (H.obj F) (H.obj L) (hS a) hLa)

private theorem stratified_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦
    model_of_iso Λ ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private theorem model_tensor_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : HasFiniteConstantLocalModel Λ X F) (hL : IsLisseCoefficientModule Λ L) :
    HasFiniteConstantLocalModel Λ X (F ⊗ L) := by
  obtain ⟨U, hU⟩ := hL
  apply model_of_cover Λ (F ⊗ L) U
  intro i
  let H := CondensedRing.upperStar Λ (U.f i)
  exact model_of_iso Λ (Functor.Monoidal.μIso H F L)
    (model_tensor_free Λ (H.obj F) (H.obj L)
      (pullback_finiteConstantLocalModel Λ (U.f i) F hF) (hU i))

private theorem model_tensor_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : HasFiniteConstantLocalModel Λ X F)
    (hL : Mod.IsFree (condensedRingObj Λ X) L) :
    HasFiniteConstantLocalModel Λ X (F ⊗ L) := by
  obtain ⟨U, hU⟩ := hF
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  let H := CondensedRing.upperStar Λ (U.f i)
  let G := (upperStarFromPoint (U.X i)).mapMod Λ
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := tensor_model Λ G (H.obj F) (H.obj L) P hP eP
    (IsFree.upperStar Λ (U.f i) hL)
  exact ⟨Q, hQ, ⟨(Functor.Monoidal.μIso H F L).symm ≪≫ eQ⟩⟩

private theorem model_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, HasFiniteConstantLocalModel Λ (U.X i)
      ((CondensedRing.upperStar Λ (U.f i)).obj M)) :
    HasFiniteConstantLocalModel Λ X M := by
  apply cover_of_local_models
    (fun {Y} f ↦ ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
        Nonempty ((CondensedRing.upperStar Λ f).obj M ≅
          ((upperStarFromPoint Y).mapMod Λ).obj P)) U
  intro i
  obtain ⟨V, hV⟩ := h i
  refine ⟨V, fun j ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hV j
  exact ⟨P, hP, ⟨model_comp_iso Λ (V.f j) (U.f i) M ≪≫ e⟩⟩

@[irreducible] private noncomputable def model_comp_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.upperStar Λ (g ≫ f)).obj M ≅
      (CondensedRing.upperStar Λ g).obj ((CondensedRing.upperStar Λ f).obj M) :=
  (CondensedRing.upperStarComp Λ g f).app M

private theorem cover_of_local_models {X : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage (U.X i),
      ∀ j, P (V.f j ≫ U.f i)) :
    ∃ W : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ a, P (W.f a) := by
  choose V hV using h
  exact cover_of_composite_models P U V hV

private theorem cover_of_composite_models {X : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (V : ∀ i, Scheme.Cover.{u} Scheme.proetalePrecoverage (U.X i))
    (h : ∀ i j, P ((V i).f j ≫ U.f i)) :
    ∃ W : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ a, P (W.f a) :=
  ⟨U.bind V, fun a ↦ h a.1 a.2⟩

private instance pointModAdditive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).Additive := by
  have : PreservesBinaryBiproducts ((upperStarFromPoint X).mapMod Λ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private instance pointColimits (X : Scheme.{u}) :
    PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits

private theorem tensor_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (G : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    [G.Monoidal] [G.Additive]
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : Mod.IsFinitelyPresented Λ P) (eF : F ≅ G.obj P)
    (hL : Mod.IsFree (condensedRingObj Λ X) L) :
    ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ Q ∧ Nonempty (F ⊗ L ≅ G.obj Q) := by
  obtain ⟨n, ⟨eL⟩⟩ := hL
  let Q := Mod.finiteFree Λ n
  have hQ : Mod.IsFree Λ Q := ⟨n, ⟨Iso.refl _⟩⟩
  have hQP : Mod.IsFinitelyPresented Λ (Q ⊗ P) :=
    hP.map_of_isFree (MonoidalCategory.tensorLeft Q) (hQ.of_iso (ρ_ Q).symm)
  have hPQ : Mod.IsFinitelyPresented Λ (P ⊗ Q) := hQP.of_iso (β_ Q P)
  let eG : G.obj Q ≅ Mod.finiteFree (condensedRingObj Λ X) n :=
    Mod.finiteFreeIsoMap G (Functor.Monoidal.εIso G).symm n
  exact ⟨P ⊗ Q, hPQ,
    ⟨tensorIso eF (eL ≪≫ eG.symm) ≪≫ Functor.Monoidal.μIso G P Q⟩⟩

private theorem model_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ eP⟩⟩

/--
For a prime `l`, a finite extension `E` of `ℚ_[l]`, and a scheme `X` on which `l` is
invertible, every signed coefficient twist is locally trivial and invertible. Tensoring
by its degree-zero derived object preserves the finite constant scalar-model bounded
constructibility predicate and finite Tor amplitude.

Source: blueprint `prop-weil-twist-preserves`, entire proposition
(blueprint: prop-weil-twist-preserves). The four conjuncts render the finite, integral,
rational, and algebraically closed coefficient cases from `def-coefficient-twists-detailed`.

Proof steps for stage 3:
1. On the pro-etale site, use the first lines from `def-coefficient-twists-detailed`.
   The finite and integral lines have local regular bases by
   `lem-twist-native-finite-local-line` and `lem-twist-native-integral-local-line`;
   scalar extension carries an integral basis to an `E`-basis, while
   `lem-poincare-integral-tate-local-basis` trivializes the actual `ℤ_l(1)` line;
   scalar extension then trivializes the prescribed algebraically closed coefficient line.
2. By `lem-twist-native-signed-line`, signed tensor and internal-Hom powers are locally
   regular and invertible, with the opposite power as dual. Applying
   `lem-pur-line-unbounded-derived-tensor` to the pulled-back coefficient ring gives the
   ordinary tensor comparison and the homology formula for every unbounded complex.
3. Refine each finite constant scalar-model cover from `sk-def-sfb-constructible` by a
   trivializing cover for the twist. Pullback commutes with tensor by
   `lem-weil-pbc-ringed-topoi-module-pullback-tensor`, so the finite scalar model remains
   valid; the same argument on affine opens handles arbitrary schemes. At finite
   coefficients this keeps the finite strata, local constancy and finite stalks of
   `def-weil-finite-torsion-constructibility`. Step 2 preserves constructible cohomology
   and its finite vanishing interval, which proves bounded constructibility.
4. For finite Tor amplitude from `def-weil-finite-tor-amplitude`, derived associativity
   from `lem-sfb-derived-monoidal` identifies tensoring first by the twist and then by any
   degree-zero module with the reverse order. Step 2 preserves the cohomological vanishing
   interval, so the same interval proves the finite Tor clause for all four coefficient rings.
-/
theorem twist_preserves_finiteness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    (∀ n : ℕ,
      (∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (twistFiniteRing l E n) X)).obj
            (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
              (coefficientFiniteTwistOne l E X n) m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (twistFiniteRing l E n) X)))) ∧
      (∀ m : ℤ, IsInvertible
        (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
          (coefficientFiniteTwistOne l E X n) m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistFiniteRing l E n) X))),
        constantModelBoundedConstructible (twistFiniteRing l E n) X K →
          constantModelBoundedConstructible (twistFiniteRing l E n) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
                (coefficientFiniteTwistOne l E X n) m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistFiniteRing l E n) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
                (coefficientFiniteTwistOne l E X n) m)))) ∧
    ((∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (twistIntegralRing l E) X)).obj
            (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
              (coefficientIntegralTwistOne l E X) m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (twistIntegralRing l E) X)))) ∧
      (∀ m : ℤ, IsInvertible
        (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
          (coefficientIntegralTwistOne l E X) m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistIntegralRing l E) X))),
        constantModelBoundedConstructible (twistIntegralRing l E) X K →
          constantModelBoundedConstructible (twistIntegralRing l E) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
                (coefficientIntegralTwistOne l E X) m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistIntegralRing l E) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
                (coefficientIntegralTwistOne l E X) m)))) ∧
    ((∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (twistRationalRing l E) X)).obj
            (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
              (coefficientRationalTwistOne l E X) m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (twistRationalRing l E) X)))) ∧
      (∀ m : ℤ, IsInvertible
        (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
          (coefficientRationalTwistOne l E X) m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistRationalRing l E) X))),
        constantModelBoundedConstructible (twistRationalRing l E) X K →
          constantModelBoundedConstructible (twistRationalRing l E) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
                (coefficientRationalTwistOne l E X) m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistRationalRing l E) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
                (coefficientRationalTwistOne l E X) m)))) ∧
    ((∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (Profinite.padicAlgClRingObj l) X)).obj
            (tateTwist X l m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (Profinite.padicAlgClRingObj l) X)))) ∧
      (∀ m : ℤ, IsInvertible (tateTwist X l m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (Profinite.padicAlgClRingObj l) X))),
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) X K →
          constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (tateTwist X l m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (Profinite.padicAlgClRingObj l) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (tateTwist X l m)))) := by
  have hl : IsUnit (l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    have h : IsUnit (l : X.presheaf.stalk x) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      change (X.residue x).hom (l : X.presheaf.stalk x) ≠ 0
      simpa only [map_natCast] using
        (isUnit_of_invertible (l : X.residueField x)).ne_zero
    simpa only [map_natCast] using h
  have hI := coefficientIntegralTwistOne_locally_trivial l E X hl
  have hR := firstLine_scalarExtension _ _
    (coefficientMap (twistIntegralToRational l E) X) (coefficientIntegralTwistOne l E X) hI
  have hQ := firstLine_scalarExtension _ _
    (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X) (tateModule X l)
      (tateModule_locally_trivial X l hl)
  refine ⟨fun n ↦ signed_finiteness _ X _
      (coefficientFiniteTwistOne_locally_trivial l E X hl n),
    signed_finiteness _ X _ hI, signed_finiteness _ X _ hR, ?_⟩
  have hn (n : ℕ) : coefficientTwistNat X
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) (tateTwistOne X l) n =
        tateTwistNat X l n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [coefficientTwistNat, tateTwistNat, ih]
  have hs : coefficientSignedTwist X
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) (tateTwistOne X l) =
        tateTwist X l := by
    funext m
    cases m with
    | ofNat n => exact hn n
    | negSucc n =>
      dsimp only [coefficientSignedTwist, tateTwist]
      rw [hn (n + 1)]
  simpa only [hs] using signed_finiteness _ X (tateTwistOne X l) hQ

end AlgebraicGeometry.ProEtale
