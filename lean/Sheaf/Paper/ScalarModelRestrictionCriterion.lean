/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.Order.CompletePartialOrder

/-!
# Scalar models on an extended stratification

Source: blueprint main-20261015, sk-lem-integral-models-operations.proof.md,
paragraph (3), restriction of extension by zero and closed direct image
(blueprint: lem-sfb-scalar-model-restriction-criterion).

The complementary stratum is indexed first; the old strata follow it. The index-count
equality and the heterogeneous equalities of its domain and immersion families identify it
with exactly these schemes and immersions, without choosing new structures on the images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

private theorem zero_presentation {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasFiniteBiproducts C] [HasCokernels C] (F : Fin 0 → C) :
    Nonempty ((0 : C) ≅ cokernel (0 : (⨁ F) ⟶ (⨁ F))) := by
  have hz : IsZero (⨁ F) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro j
    exact Fin.elim0 j
  exact ⟨(isZero_zero C).iso hz ≪≫ cokernelZeroIsoTarget.symm⟩

private structure LocalModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (W : Scheme.{u}) (f : W ⟶ T) : Prop where
  model : HasFiniteConstantLocalModel Λ W ((CondensedRing.upperStar Λ f).obj H)

private theorem cons_family {A : Type*} {B : A → Type*}
    (Q : ∀ a, B a → Prop) {n : ℕ} (D : Fin n → A) (Y : A)
    (f : ∀ a, B (D a)) (g : B Y) (hy : Q Y g) (hold : ∀ a, Q (D a) (f a)) :
    ∀ a : Fin (n + 1), Q (Fin.cases (motive := fun _ ↦ A) Y D a)
      (Fin.cases (motive := fun a ↦ B (Fin.cases (motive := fun _ ↦ A) Y D a)) g f a) :=
  Fin.cases (motive := fun a ↦ Q (Fin.cases (motive := fun _ ↦ A) Y D a)
    (Fin.cases (motive := fun a ↦ B (Fin.cases (motive := fun _ ↦ A) Y D a)) g f a))
    hy hold

private theorem transfer_family {A : Type*} {B : A → Type*}
    (Q : ∀ a, B a → Prop) {n m : ℕ} (D : Fin n → A) (f : ∀ a, B (D a))
    (E : Fin m → A) (g : ∀ a, B (E a)) (hn : m = n) (hd : HEq E D)
    (hf : HEq g f) (hh : ∀ a, Q (D a) (f a)) : ∀ a, Q (E a) (g a) := by
  subst m
  cases eq_of_heq hd
  cases eq_of_heq hf
  exact hh

attribute [local irreducible] CondensedRing.upperStar upperStarFromPoint pointUpperStar
  ProEtale.upperStar

set_option backward.isDefEq.respectTransparency true in
/-- Specified scalar models transfer through restriction isomorphisms, and the
complementary stratum has the rank-zero model on its identity cover.

Source: blueprint main-20261015, sk-lem-integral-models-operations.proof.md,
paragraph (3) (blueprint: lem-sfb-scalar-model-restriction-criterion).

Proof: (1) Compose `upperStarComp` at H with the image under each stratum pullback
of the supplied isomorphism h*H ≅ M. The inverse is the reverse composite of the
inverse isomorphisms, so these are isomorphisms of internal modules.
(2) Pull each resulting isomorphism along the given cover map, and compose with
its supplied model isomorphism. The covers and finitely presented point modules
are unchanged, giving the same scalar presentations on all old strata.
(3) The zero scalar module has the rank-zero presentation: the cokernel of the
zero map between two rank-zero free modules is zero. Scalar extension preserves
initial objects by the extension/restriction adjunction, so its extension is zero.
(4) The identity of Y is a pro-etale cover. Its pullback preserves zero by its
adjunction; compose with k*H ≅ 0 and the inverse of the scalar-extension zero
isomorphism. This gives the specified zero model on the identity cover.
(5) Apply the finite constant local model definition to every stratum of the
supplied extended stratification, and then the qcqs branch of constructibility.
These are the five elementary steps of the DAG proof; the composition step uses
[def-sfb-module-upper-star-comp], and the zero scalar-extension step uses
[sk-def-sfb-change-of-scalars]. -/
theorem scalarModelRestrictionCriterion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T X Y : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : X ⟶ T) (k : Y ⟶ T) [IsImmersion h] [IsImmersion k]
    (_hdisjoint : Disjoint (Set.range h) (Set.range k))
    (_hcover : Set.range h ∪ Set.range k = Set.univ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (eh : (CondensedRing.upperStar Λ h).obj H ≅ M)
    (ek : (CondensedRing.upperStar Λ k).obj H ≅ 0)
    (S : Scheme.FiniteLocallyClosedStratification X)
    (E : Scheme.Stratification T)
    (hE_n : E.n = S.n + 1)
    (hE_domain : HEq E.domain (fun a : Fin (S.n + 1) ↦
      Fin.cases (motive := fun _ ↦ Scheme.{u}) Y S.domain a))
    (hE_immersion : HEq E.immersion
      (fun a : Fin (S.n + 1) ↦
        Fin.cases (motive := fun b ↦
          Fin.cases (motive := fun _ ↦ Scheme.{u}) Y S.domain b ⟶ T)
          k (fun b ↦ S.immersion b ≫ h) a))
    (C : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (P : ∀ a : Fin S.n, (C a).I₀ →
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : ∀ (a : Fin S.n) (r : (C a).I₀), Mod.IsFinitelyPresented Λ (P a r))
    (models : ∀ (a : Fin S.n) (r : (C a).I₀),
      (CondensedRing.upperStar Λ ((C a).f r)).obj
          ((CondensedRing.upperStar Λ (S.immersion a)).obj M) ≅
        ((upperStarFromPoint ((C a).X r)).mapMod Λ).obj (P a r)) :
    (∀ a : Fin S.n, Nonempty
      ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M)) ∧
    (∀ (a : Fin S.n) (r : (C a).I₀), Nonempty
      ((CondensedRing.upperStar Λ ((C a).f r)).obj
          ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H) ≅
        ((upperStarFromPoint ((C a).X r)).mapMod Λ).obj (P a r))) ∧
    Nonempty ((0 : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ≅
      cokernel (0 : Mod.finiteFree Λ 0 ⟶ Mod.finiteFree Λ 0)) ∧
    Nonempty (((upperStarFromPoint Y).mapMod Λ).obj 0 ≅ 0) ∧
    Nonempty ((CondensedRing.upperStar Λ (𝟙 Y)).obj
        ((CondensedRing.upperStar Λ k).obj H) ≅
      ((upperStarFromPoint Y).mapMod Λ).obj 0) ∧
    (∀ a : Fin E.n, HasFiniteConstantLocalModel Λ (E.domain a)
      ((CondensedRing.upperStar Λ (E.immersion a)).obj H)) ∧
    IsConstantModelConstructible Λ T H := by
  classical
  have e (a : Fin S.n) : Nonempty
      ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M) :=
    by
      exact ⟨(CondensedRing.upperStarComp Λ (S.immersion a) h).app H ≪≫
        (CondensedRing.upperStar Λ (S.immersion a)).mapIso eh⟩
  have em (a : Fin S.n) (r : (C a).I₀) : Nonempty
      ((CondensedRing.upperStar Λ ((C a).f r)).obj
          ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H) ≅
        ((upperStarFromPoint ((C a).X r)).mapMod Λ).obj (P a r)) := by
    obtain ⟨ea⟩ := e a
    exact
      ⟨(CondensedRing.upperStar Λ ((C a).f r)).mapIso ea ≪≫ models a r⟩
  have ep : Nonempty
      ((0 : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ≅
        cokernel (0 : Mod.finiteFree Λ 0 ⟶ Mod.finiteFree Λ 0)) :=
    by exact zero_presentation (fun _ : Fin 0 ↦ Mod.regular Λ)
  have ez : Nonempty (((upperStarFromPoint Y).mapMod Λ).obj 0 ≅ 0) := by
    have : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    have : PreservesFiniteColimits (upperStarFromPoint Y) := by
      unfold upperStarFromPoint
      infer_instance
    exact ⟨(((upperStarFromPoint Y).mapMod Λ).map_isZero (isZero_zero _)).isoZero⟩
  have ey : Nonempty ((CondensedRing.upperStar Λ (𝟙 Y)).obj
      ((CondensedRing.upperStar Λ k).obj H) ≅
        ((upperStarFromPoint Y).mapMod Λ).obj 0) := by
    obtain ⟨ez⟩ := ez
    exact ⟨(CondensedRing.upperStar Λ (𝟙 Y)).mapIso ek ≪≫
      ((CondensedRing.upperStar Λ (𝟙 Y)).map_isZero (isZero_zero _)).isoZero ≪≫ ez.symm⟩
  have old (a : Fin S.n) : HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H) := by
    exact ⟨C a, fun r ↦ ⟨P a r, hP a r, em a r⟩⟩
  have extra : HasFiniteConstantLocalModel Λ Y
      ((CondensedRing.upperStar Λ k).obj H) := by
    refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 Y)
      (Precoverage.mem_coverings_of_isIso (J := Scheme.proetalePrecoverage) _), ?_⟩
    intro i
    exact ⟨0, ⟨0, 0, 0, ep⟩, ey⟩
  have hx : LocalModel Λ (T := T) H Y k := ⟨extra⟩
  have ho (a : Fin S.n) : LocalModel Λ (T := T) H (S.domain a) (S.immersion a ≫ h) := ⟨old a⟩
  have extended := cons_family (B := fun W : Scheme.{u} ↦ W ⟶ T)
    (LocalModel Λ (T := T) H) S.domain Y (fun a ↦ S.immersion a ≫ h) k hx ho
  have extendedE := transfer_family (B := fun W : Scheme.{u} ↦ W ⟶ T)
    (LocalModel Λ (T := T) H) _ _ E.domain E.immersion hE_n hE_domain hE_immersion extended
  have adapted : ∀ a : Fin E.n, HasFiniteConstantLocalModel Λ (E.domain a)
      ((CondensedRing.upperStar Λ (E.immersion a)).obj H) :=
    fun a ↦ (extendedE a).model
  refine ⟨e, em, ep, ez, ey, adapted, ?_⟩
  exact (show IsConstantModelConstructible Λ T H = IsFiniteConstantStratified Λ T H from
    if_pos ⟨inferInstance, inferInstance⟩).mpr ⟨E, adapted⟩

end AlgebraicGeometry.ProEtale
