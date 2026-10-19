/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.Devissage
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Constant scalar models under open and closed immersion functors

Source: blueprint main-20261015, sk-lem-integral-models-operations,
parent proof step 3 (blueprint: lem-sfb-constant-model-immersion-images).
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek


universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma localModel_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 a
  exact ⟨P, hP, ⟨(upperStar Λ (𝒰.f a)).mapIso e.symm ≪≫ eP⟩⟩

private lemma constantConstructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ localModel_iso Λ ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  · intro U hU
    obtain ⟨S, hS⟩ := hM U hU
    exact ⟨S, fun a ↦ localModel_iso Λ
      ((upperStar Λ (S.immersion a)).mapIso ((upperStar Λ U.ι).mapIso e)) (hS a)⟩

private lemma localModel_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  let P := cokernel (𝟙 (Mod.finiteFree Λ 1))
  have hP : IsZero P := isZero_cokernel_of_epi _
  have hfp : Mod.IsFinitelyPresented Λ P := ⟨1, 1, 𝟙 _, ⟨Iso.refl _⟩⟩
  have hAdj (T : Scheme.{u}) : (upperStarFromPoint T).IsLeftAdjoint :=
    by
      unfold upperStarFromPoint
      exact (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).isLeftAdjoint
  have hAdd (T : Scheme.{u}) : (upperStarFromPoint T).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : Scheme.proetalePrecoverage.{u}.HasIsos := inferInstance
  refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 X)
    (Precoverage.mem_coverings_of_isIso _), fun a ↦ ?_⟩
  exact ⟨P, hfp, ⟨((upperStar Λ _).map_isZero hM).iso
    (((upperStarFromPoint _).mapMod Λ).map_isZero hP)⟩⟩

private lemma constructible_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  dsimp only [IsConstantModelConstructible]
  rw [if_pos ⟨inferInstance, inferInstance⟩]
  refine ⟨Scheme.Stratification.trivial X, fun a ↦ ?_⟩
  exact localModel_zero Λ _ ((upperStar Λ (𝟙 X)).map_isZero hM)

private lemma stratified_openClosed
    {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : ∀ T : Scheme.{u}, (T ⟶ X) → Prop)
    (SU : Scheme.Stratification U) (SZ : Scheme.Stratification Z)
    (hSU : ∀ a, P _ (SU.immersion a ≫ j))
    (hSZ : ∀ a, P _ (SZ.immersion a ≫ i)) :
    ∃ S : Scheme.Stratification X, ∀ a, P _ (S.immersion a) := by
  refine ⟨Scheme.Stratification.openClosed j i hij SU SZ, fun k ↦ ?_⟩
  change P _ (Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
    (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i) (finSumFinEquiv.symm k))
  generalize finSumFinEquiv.symm k = s
  rcases s with l | l
  · exact hSU l
  · exact hSZ l

private lemma constructible_openClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z X : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian Z] [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hU : IsConstantModelConstructible Λ U ((upperStar Λ j).obj M))
    (hZ : IsConstantModelConstructible Λ Z ((upperStar Λ i).obj M)) :
    IsConstantModelConstructible Λ X M := by
  classical
  dsimp only [IsConstantModelConstructible] at hU hZ ⊢
  rw [if_pos ⟨inferInstance, inferInstance⟩] at hU hZ ⊢
  obtain ⟨SU, hSU⟩ := hU
  obtain ⟨SZ, hSZ⟩ := hZ
  apply stratified_openClosed j i hij
    (fun T f ↦ HasFiniteConstantLocalModel Λ T ((upperStar Λ f).obj M)) SU SZ
  · intro l
    exact localModel_iso Λ ((upperStarComp Λ (SU.immersion l) j).app M).symm (hSU l)
  · intro l
    exact localModel_iso Λ ((upperStarComp Λ (SZ.immersion l) i).app M).symm (hSZ l)

/-- Open extension and closed direct image preserve finite constant scalar models.
Source: integral-models-operations proof, paragraph (3), parent step 3;
Stacks Project Tags 09AA, 09BM, 09BN and 09AH
(blueprint: lem-sfb-constant-model-immersion-images).

Proof: Noetherianity makes every open immersion quasi-compact. For open extension,
append the reduced closed complement to the given finite stratification. Compose
the old stratum immersions with the open immersion. Pullback composition and the
invertible extension/restriction adjunction unit identify each old restriction with
its original sheaf, retaining the same cover and the same scalar module. On the
complement restriction is zero, modeled by the zero scalar module on the identity
cover, with its rank-zero finite presentation. For closed direct image use its
open complement. The closed restriction is the original sheaf by the invertible
counit; the open restriction is zero. Concatenate the two stratifications. Their
images are constructible locally closed subsets of the Noetherian ambient scheme.
Both arguments include empty schemes and zero sheaves; no scalar-ring condition
other than commutativity is needed. -/
theorem constantModel_immersion_images
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (∀ {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
      (j : U ⟶ X) [IsOpenImmersion j]
      (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)),
      IsConstantModelConstructible Λ U M →
      IsConstantModelConstructible Λ X ((openImmersionLowerShriek Λ j).obj M)) ∧
    (∀ {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
      (i : Z ⟶ X) [IsClosedImmersion i]
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      IsConstantModelConstructible Λ Z M →
      IsConstantModelConstructible Λ X ((lowerStar Λ i).obj M)) := by
  classical
  constructor
  · intro U X _ _ j _ M hM
    obtain ⟨Z, i, hi, hij⟩ := exists_isClosedImmersion_range_eq_compl j
    have := hi
    have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
    have hu := openUnitIsIso Λ j
    apply constructible_openClosed Λ j i hij
    · exact constantConstructible_iso Λ
        (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M)) hM
    · apply constructible_zero Λ
      apply (IsZero.iff_id_eq_zero _).2
      apply ((upperStarLowerStarAdjunction Λ i).homEquiv _ _).injective
      apply ((openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).injective
      exact (openRestrictionPushforwardZero Λ i j (by rw [hij, compl_compl]) _).eq_of_tgt _ _
  · intro Z X _ _ i _ M hM
    let V : X.Opens :=
      ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have : IsNoetherian V := isNoetherian_of_locallyOfFiniteType V.ι
    have hVi : Set.range V.ι = (Set.range i)ᶜ := by simp [V]
    have hc := moduleCounitOfAbelian Λ i (ProEtale.abelian_closed_counit i)
    apply constructible_openClosed Λ V.ι i (by rw [hVi, compl_compl])
    · exact constructible_zero Λ _ (openRestrictionPushforwardZero Λ i V.ι hVi M)
    · exact constantConstructible_iso Λ
        (asIso ((upperStarLowerStarAdjunction Λ i).counit.app M)).symm hM

end AlgebraicGeometry.ProEtale.CondensedRing
