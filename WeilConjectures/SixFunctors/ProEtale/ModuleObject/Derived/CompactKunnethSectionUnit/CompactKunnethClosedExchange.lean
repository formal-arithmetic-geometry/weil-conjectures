/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RelativeKunneth.CondensedRelativeKunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing

/-!
# Normalization of compact Künneth on closed sections

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
  thm-pur-vector-bundle-thom.proof.md`, Steps 1 and 2
(blueprint: lem-pur-compact-kunneth-section-unit).

The source isomorphism is the closed direct-image exchange followed by the
compact-support projection formula and the coefficient unitors.  Its compact image is
then compared by the native relative Künneth isomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethSectionUnit

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.leftAdjoint Functor.rightAdjoint Functor.mapDerivedCategory
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarTensor
  leftDerivedUpperStarComp pullbackSquareComparison
  AlgebraicGeometry.ProEtale.CondensedRing.baseChangeMap
  condensedAmbientExchange condensedAmbientPullbackComparison

private theorem isIso_last_of_word {C : Type*} [Category* C]
    {A B D E : C} {f : A ⟶ E} {g₁ : A ⟶ B} {g₂ : B ⟶ D} {g₃ : D ⟶ E}
    [IsIso f] [IsIso (g₁ ≫ g₂)]
    (h : f = g₁ ≫ g₂ ≫ g₃) : IsIso g₃ := by
  letI : IsIso ((g₁ ≫ g₂) ≫ g₃) := by
    rw [Category.assoc, ← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (g₁ ≫ g₂) _

private theorem isIso_first_of_word {C : Type*} [Category* C]
    {A B D E : C} {f : A ⟶ E} {g₁ : A ⟶ B} {g₂ : B ⟶ D} {g₃ : D ⟶ E}
    [IsIso f] [IsIso g₂] [IsIso g₃]
    (h : f = g₁ ≫ g₂ ≫ g₃) : IsIso g₁ := by
  letI : IsIso (g₁ ≫ g₂ ≫ g₃) := h ▸ (inferInstance : IsIso f)
  exact IsIso.of_isIso_comp_right g₁ (g₂ ≫ g₃)

private theorem mate_eq_exchangeRight
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    (mateEquiv af af' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans =
      Adjunction.exchangeRight af af' θ := by
  ext K
  simp [Adjunction.exchangeRight, mateEquiv, Functor.squareTransport, Category.assoc]

set_option maxHeartbeats 800000 in
-- Match the two native derived-functor presentations before taking components.
private theorem ambientExchange_eq_baseChange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare w f' f v) :
    condensedAmbientExchange Λ sq = baseChangeMap Λ sq.toCommSq := by
  unfold condensedAmbientExchange baseChangeMap
  rw [mate_eq_exchangeRight]
  congr 1
  unfold condensedAmbientPullbackComparison pullbackSquareComparison
  rfl

private theorem ambientExchange_isIso_baseChange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare w f' f v)
    (K : CompactificationReindexing.D Λ X)
    (h : IsIso ((condensedAmbientExchange Λ sq).app K)) :
    IsIso ((baseChangeMap Λ sq.toCommSq).app K) := by
  rw [ambientExchange_eq_baseChange] at h
  exact h

private theorem directExchange_isoSides
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsIso w] [IsIso v] (sq : CommSq w f' f v) :
    IsIso (baseChangeMap Λ sq) := by
  unfold baseChangeMap
  exact Adjunction.isIso_exchangeRight_of_isEquivalence
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq)

private theorem identitySquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CommSq (𝟙 X) f f (𝟙 Y) := ⟨by simp⟩

private theorem transportPrefix_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y)
    (K : CompactificationReindexing.D Λ X) :
    IsIso ((pullbackSquareComparison Λ (identitySquare v)).inv.app
        ((CompactificationReindexing.R Λ f).obj K) ≫
      (CompactificationReindexing.P Λ v).map
        ((baseChangeMap Λ (identitySquare f)).app K)) := by
  letI : IsIso (baseChangeMap Λ (identitySquare f)) :=
    directExchange_isoSides Λ (identitySquare f)
  infer_instance

private theorem transportRight {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback w f' f v) :
    CommSq sq.isoPullback.hom f' (pullback.snd f v) (𝟙 Y') :=
  ⟨by simp [sq.isoPullback_hom_snd]⟩

private theorem transportTop {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback w f' f v) :
    CommSq sq.isoPullback.hom w (pullback.fst f v) (𝟙 X) :=
  ⟨by simp [sq.isoPullback_hom_fst]⟩

set_option maxHeartbeats 400000 in
-- Keep the three invertible front factors separate from cancellation in the cube.
private theorem transportWord_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (K : CompactificationReindexing.D Λ X)
    (h : IsIso ((baseChangeMap Λ (IsPullback.of_hasPullback f v).toCommSq).app K)) :
    IsIso ((CompactificationReindexing.P Λ (𝟙 Y')).map
        ((baseChangeMap Λ (IsPullback.of_hasPullback f v).toCommSq).app K) ≫
      (baseChangeMap Λ (transportRight sq)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K) ≫
      (CompactificationReindexing.R Λ f').map
        ((pullbackSquareComparison Λ (transportTop sq)).inv.app K)) := by
  letI := h
  letI : IsIso (baseChangeMap Λ (transportRight sq)) :=
    directExchange_isoSides Λ (transportRight sq)
  infer_instance

set_option maxHeartbeats 400000 in
-- Specialize the native cube before cancelling its invertible factors.
private theorem transportCube_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (K : CompactificationReindexing.D Λ X) :
    (CompactificationReindexing.P Λ (𝟙 Y')).map
        ((baseChangeMap Λ (IsPullback.of_hasPullback f v).toCommSq).app K) ≫
      (baseChangeMap Λ (transportRight sq)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K) ≫
      (CompactificationReindexing.R Λ f').map
        ((pullbackSquareComparison Λ (transportTop sq)).inv.app K) =
    (pullbackSquareComparison Λ (identitySquare v)).inv.app
        ((CompactificationReindexing.R Λ f).obj K) ≫
      (CompactificationReindexing.P Λ v).map
        ((baseChangeMap Λ (identitySquare f)).app K) ≫
      (baseChangeMap Λ sq.toCommSq).app
        ((CompactificationReindexing.P Λ (𝟙 X)).obj K) := by
  exact CompactificationReindexing.direct_cube Λ
    (IsPullback.of_hasPullback f v).toCommSq sq.toCommSq
    (identitySquare f) (transportRight sq) (transportTop sq) (identitySquare v) K

private theorem directExchange_transport_atId
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (K : CompactificationReindexing.D Λ X)
    (h : IsIso ((baseChangeMap Λ (IsPullback.of_hasPullback f v).toCommSq).app K)) :
    IsIso ((baseChangeMap Λ sq.toCommSq).app
      ((CompactificationReindexing.P Λ (𝟙 X)).obj K)) := by
  letI := transportWord_isIso Λ sq K h
  letI := transportPrefix_isIso Λ f v K
  exact isIso_last_of_word (transportCube_eq Λ sq K)

private noncomputable def nativePullbackIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    CompactificationReindexing.P Λ (𝟙 X) ≅ 𝟭 (CompactificationReindexing.D Λ X) :=
  Functor.leftDerivedFunctorIdIso (upperStarId Λ X)

private theorem isIso_app_of_nativeIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) {C : Type*} [Category* C]
    {F G : CompactificationReindexing.D Λ X ⥤ C} (α : F ⟶ G)
    (K : CompactificationReindexing.D Λ X)
    (h : IsIso (α.app ((CompactificationReindexing.P Λ (𝟙 X)).obj K))) :
    IsIso (α.app K) :=
  (NatTrans.isIso_app_iff_of_iso α ((nativePullbackIdentity Λ X).app K)).mp h

private theorem isIso_app_of_comparison {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} {α : F ⟶ G} {K L : C} (e : K ≅ L) (h : IsIso (α.app K)) :
    IsIso (α.app L) :=
  (NatTrans.isIso_app_iff_of_iso α e).mp h

private noncomputable def nativeOpenIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    CompactificationReindexing.J Λ (𝟙 X) ≅ 𝟭 (CompactificationReindexing.D Λ X) :=
  derivedOpenImmersionLowerShriekId Λ X

private theorem isIso_app_of_nativeOpenIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) {C : Type*} [Category* C]
    {F G : CompactificationReindexing.D Λ X ⥤ C} (α : F ⟶ G)
    (K : CompactificationReindexing.D Λ X)
    (h : IsIso (α.app ((CompactificationReindexing.J Λ (𝟙 X)).obj K))) :
    IsIso (α.app K) :=
  (NatTrans.isIso_app_iff_of_iso α ((nativeOpenIdentity Λ X).app K)).mp h

private theorem directExchange_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (K : CompactificationReindexing.D Λ X)
    (h : IsIso ((baseChangeMap Λ (IsPullback.of_hasPullback f v).toCommSq).app K)) :
    IsIso ((baseChangeMap Λ sq.toCommSq).app K) := by
  exact isIso_app_of_nativeIdentity Λ X (baseChangeMap Λ sq.toCommSq) K
    (directExchange_transport_atId Λ sq K h)

-- These private proof definitions retain the exact inferred native functor instances.
-- Reconstructing their result types independently causes kernel normalization timeouts.
set_option warn.classDefReducibility false in
set_option linter.defProp false in
set_option warn.classDefReducibility false in
set_option linter.defProp false in
/-- The actual direct-image exchange on the closed section square is invertible.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 3.
Proof: The section square is Cartesian by pullback uniqueness. Use the proper
identity-open compactifications of s and a. The exchange-normalization law in H
expresses the coherent compact exchange as the ambient direct-image exchange,
followed by the open comparison and compactification comparison. Both following
comparisons and the compact exchange are isomorphisms; cancellation makes the
ambient factor invertible on the identity open extension of the coefficient unit.
Remove that extension using derivedOpenImmersionLowerShriekId and naturality.
Identify the ambient mate with baseChangeMap, and transport the canonical
pullback square to the section square using direct_cube and sq.isoPullback.
Finally compose with the mapped equality A_spec and the pulled-back coefficient
unit comparison, both of which are isomorphisms. The proof uses no invertibility
of ell in the field: the supplied coherent exchange and constructible unit are
its inputs. Empty schemes give the same identities in the zero category.
(blueprint: lem-pur-compact-kunneth-closed-exchange). -/
theorem closed_exchange_isIso {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) : IsIso (closedExchange I) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethSectionUnit
