/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q21, D2
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Defs.Filter

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Paper.ContinuousCoefficientFreeRank
import Sheaf.AlgebraicGeometry.FpqcLabelledClopenDescent
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-!
# The clopen rank decomposition of a lisse coefficient module

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-stratified-lattice/
sk-lem-stratified-lattice-rank.md (blueprint: det-lem-stratified-lattice-rank).

The coefficients are the pulled-back condensed continuous-function ring of a finite
extension of the p-adic field. Every occurrence of the continuous coefficient ring explicitly
uses the canonical spectral norm topology; no topology on E is supplied as a hypothesis.
Lissity is the existing pro-etale local finite-freeness predicate. The open subschemes in
this statement have their actual restricted structure sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem rankPullbackFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} (f : Y ⟶ Z) (n : ℕ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      (Mod.finiteFree (condensedRingObj Λ Z) n) ≅
        Mod.finiteFree (condensedRingObj Λ Y) n) := by
  let F := ProEtale.upperStar Ab.{u + 1} f
  let R := condensedRingObj Λ Z
  let φ := condensedPullbackHom Λ f
  let e : (F.mapMod R).obj (Mod.finiteFree R n) ≅
      Mod.finiteFree (F.obj R) n :=
    (F.mapMod R).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ Iso.refl _)
  exact ⟨(Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalarsIsoComapInv φ).app _ ≪≫ Mod.finiteFreeIsoComap (inv φ) n⟩

private theorem rankPullbackTrivialization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ) (e : (CondensedRing.upperStar Λ f).obj M ≅
      Mod.finiteFree (condensedRingObj Λ Y) n) :
    Nonempty ((CondensedRing.upperStar Λ (g ≫ f)).obj M ≅
      Mod.finiteFree (condensedRingObj Λ Z) n) := by
  obtain ⟨eg⟩ := rankPullbackFree Λ g n
  exact ⟨(CondensedRing.upperStarComp Λ g f).app M ≪≫
    (CondensedRing.upperStar Λ g).mapIso e ≪≫ eg⟩

private def rankIdentityCover (Y : Scheme.{u}) (p : Prop) [Decidable p]
    (hempty : ¬p → IsEmpty Y) : Scheme.Cover.{u} Scheme.proetalePrecoverage Y where
  I₀ := ULift.{u, 0} (PLift.{0} p)
  X _ := Y
  f _ := 𝟙 Y
  mem₀ := by
    change Presieve.ofArrows (fun _ : ULift.{u, 0} (PLift.{0} p) ↦ Y)
      (fun _ ↦ 𝟙 Y) ∈ Scheme.proetalePrecoverage Y
    by_cases hp : p
    · have heq : Presieve.ofArrows (fun _ : ULift.{u, 0} (PLift.{0} p) ↦ Y)
          (fun _ ↦ 𝟙 Y) = Presieve.singleton (𝟙 Y) := by
        funext Z f
        apply propext
        constructor
        · rintro ⟨i⟩
          exact Presieve.singleton_self _
        · rintro ⟨⟩
          exact ⟨⟨⟨hp⟩⟩⟩
      rw [heq]
      exact Precoverage.mem_coverings_of_isIso _
    · let := hempty hp
      have heq : Presieve.ofArrows (fun _ : ULift.{u, 0} (PLift.{0} p) ↦ Y)
          (fun _ ↦ 𝟙 Y) = ⊥ := by
        funext Z f
        apply propext
        constructor
        · rintro ⟨i⟩
          exact (hp i.down.down).elim
        · intro h
          exact h.elim
      rw [heq, Scheme.proetalePrecoverage]
      exact Scheme.bot_mem_propQCPrecoverage _

attribute [local irreducible] CondensedRing.upperStarComp
  CondensedRing.upperStarLowerStarAdjunction upperStarFromPoint
  CondensedRing.upperStar

private theorem rankCover
    {X : Scheme.{u}} (B : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (p : B.I₀ → Prop) (hempty : ∀ i, ¬p i → IsEmpty (B.X i))
    (P : ∀ (Y : Scheme.{u}), (Y ⟶ X) → Prop)
    (h : ∀ i, p i → P (B.X i) (B.f i)) :
    ∃ K : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i, P (K.X i) (K.f i) := by
  classical
  let D i := rankIdentityCover (B.X i) (p i) (hempty i)
  let K : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    { I₀ := Σ i : B.I₀, ULift.{u, 0} (PLift.{0} (p i))
      X := fun i ↦ B.X i.1
      f := fun i ↦ B.f i.1
      mem₀ := by
        convert (B.bind D).mem₀ using 1
        simp only [PreZeroHypercover.presieve₀, Precoverage.ZeroHypercover.bind,
            PreZeroHypercover.bind, D, rankIdentityCover, Category.id_comp] }
  refine ⟨K, ?_⟩
  rintro ⟨i, j⟩
  exact h i j.down.down

private theorem rankRestrictedCover
    {X : Scheme.{u}} (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (n : C.I₀ → ℕ) (R : ℕ → X.Opens)
    (hmem : ∀ i (v : C.X i) r, C.f i v ∈ R r ↔ n i = r)
    (P : ∀ (Y : Scheme.{u}), (Y ⟶ X) → ℕ → Prop)
    (hbase : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (a : ℕ),
      P Y f a → P Z (g ≫ f) a)
    (hC : ∀ i, P (C.X i) (C.f i) (n i)) (r : ℕ) :
    ∃ K : Scheme.Cover.{u} Scheme.proetalePrecoverage (R r).toScheme,
      ∀ i, P (K.X i) (K.f i ≫ (R r).ι) r := by
  classical
  let B := C.pullback₁ (R r).ι
  have hempty (i : C.I₀) (hn : n i ≠ r) : IsEmpty (B.X i) := by
    refine ⟨fun w ↦ hn ?_⟩
    apply (hmem i (pullback.snd (R r).ι (C.f i) w) r).mp
    have heq := congrArg (fun f : B.X i ⟶ X ↦ f w)
      (pullback.condition (f := (R r).ι) (g := C.f i))
    change (R r).ι (pullback.fst (R r).ι (C.f i) w) =
      C.f i (pullback.snd (R r).ι (C.f i) w) at heq
    rw [← heq]
    exact (pullback.fst (R r).ι (C.f i) w).2
  apply rankCover B (fun i ↦ n i = r) hempty (fun Y f ↦ P Y (f ≫ (R r).ι) r)
  intro i hn
  have ep := hbase (C.f i) (pullback.snd (R r).ι (C.f i)) (n i) (hC i)
  simpa only [pullback.condition, hn, B, Precoverage.ZeroHypercover.pullback₁,
    PreZeroHypercover.pullback₁] using ep

private theorem spectralRank
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [Nonempty W] (a b : ℕ)
    (e : Mod.finiteFree (condensedRingObj
        (@Profinite.continuousCoefficientRingObj E
          (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
          (@NonUnitalSeminormedRing.toIsTopologicalRing E
            (@SeminormedRing.toNonUnitalSeminormedRing E
              (spectralNorm.seminormedRing ℚ_[l] E)))) W) a ≅
      Mod.finiteFree (condensedRingObj
        (@Profinite.continuousCoefficientRingObj E
          (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
          (@NonUnitalSeminormedRing.toIsTopologicalRing E
            (@SeminormedRing.toNonUnitalSeminormedRing E
              (spectralNorm.seminormedRing ℚ_[l] E)))) W) b) : a = b := by
  let := spectralNorm.normedField ℚ_[l] E
  let := spectralNorm.normedAlgebra ℚ_[l] E
  exact continuous_coefficient_finiteFree_rank l E W a b e

private theorem rankWitness
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (P : ∀ (Z : Scheme.{u}), (Z ⟶ X) → Prop) (e : P Y f) (v : Y) :
    ∃ (U : X.ProEt) (w : U.left), U.hom w = f v ∧ P U.left U.hom := by
  exact ⟨Scheme.ProEt.mk f, v, rfl, e⟩

private theorem rankDecomposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hRank : ∀ (W : Scheme.{u}) [Nonempty W] (a b : ℕ),
      (Mod.finiteFree (condensedRingObj Λ W) a ≅
        Mod.finiteFree (condensedRingObj Λ W) b) → a = b)
    (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (hL : IsLisseCoefficientModule Λ L) :
    ∃ R : ℕ → X.Opens,
      (∀ r : ℕ, IsClosed (R r : Set X)) ∧
      (∀ (x : X) (r : ℕ), x ∈ R r ↔
        ∃ (U : X.ProEt) (v : U.left), U.hom v = x ∧
          Nonempty
            ((CondensedRing.upperStar Λ (X := U.left) (Y := X) U.hom).obj L ≅
              Mod.finiteFree
                (condensedRingObj Λ U.left) r)) ∧
      (∀ (U : X.ProEt) (n : ℕ),
        Nonempty
          ((CondensedRing.upperStar Λ (X := U.left) (Y := X) U.hom).obj L ≅
            Mod.finiteFree
              (condensedRingObj Λ U.left) n) →
        ∀ (v : U.left) (r : ℕ), U.hom v ∈ R r ↔ n = r) ∧
      (CompactSpace X → {r : ℕ | (R r : Set X).Nonempty}.Finite) ∧
      IsIso (Sigma.desc (fun r : ℕ ↦ (R r).ι)) ∧
      ∀ r : ℕ, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (R r).toScheme,
        ∀ i : C.I₀,
          Nonempty
            ((CondensedRing.upperStar Λ (X := C.X i) (Y := X)
                (C.f i ≫ (R r).ι)).obj L ≅
              Mod.finiteFree
                (condensedRingObj Λ (C.X i)) r) := by
  classical
  obtain ⟨C, hC⟩ := hL
  obtain ⟨n, e⟩ := Classical.axiomOfChoice hC
  obtain ⟨t⟩ := Classical.nonempty_pi.mpr e
  have compare {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
      (a b : ℕ)
      (ef : (CondensedRing.upperStar Λ f).obj L ≅
        Mod.finiteFree (condensedRingObj Λ Y) a)
      (eg : (CondensedRing.upperStar Λ g).obj L ≅
        Mod.finiteFree (condensedRingObj Λ Z) b)
      (w : ↑(pullback f g)) : a = b := by
    let : Nonempty ↑(pullback f g) := ⟨w⟩
    have ea := rankPullbackTrivialization Λ f (pullback.fst f g) L a ef
    have eb := rankPullbackTrivialization Λ g (pullback.snd f g) L b eg
    have ea' : Nonempty ((CondensedRing.upperStar Λ
        (pullback.snd f g ≫ g)).obj L ≅
          Mod.finiteFree (condensedRingObj Λ (pullback f g)) a) := by
      simpa only [pullback.condition] using ea
    obtain ⟨ia⟩ := ea'
    obtain ⟨ib⟩ := eb
    exact hRank _ a b (ia.symm ≪≫ ib)
  have compat (i j : C.I₀) :
      (fun _ : C.X i ↦ n i) ∘ pullback.fst (C.f i) (C.f j) =
        (fun _ : C.X j ↦ n j) ∘ pullback.snd (C.f i) (C.f j) := by
    funext w
    exact compare (C.f i) (C.f j) (n i) (n j) (t i) (t j) w
  obtain ⟨R, hR, _⟩ := labelledClopenPartition_existsUnique_of_fpqc C.f
    (Scheme.proetalePrecoverage_le_fpqcPrecoverage _ C.mem₀)
    (fun i _ ↦ n i) (by intro i a; by_cases h : n i = a <;> simp [h]) compat
  obtain ⟨hclosed, hdisjoint, hcover, hmem, htest⟩ := hR
  have mem_cover (i : C.I₀) (v : C.X i) (r : ℕ) :
      C.f i v ∈ R r ↔ n i = r := by
    exact congrArg (fun S : Set (C.X i) ↦ v ∈ S) (hmem i r) |>.to_iff
  have mem_test (V : Scheme.{u}) (f : V ⟶ X) (a : ℕ)
      (eU : Nonempty ((CondensedRing.upperStar Λ f).obj L ≅
        Mod.finiteFree (condensedRingObj Λ V) a)) (v : V) (r : ℕ) :
      f v ∈ R r ↔ a = r := by
    have hc (i : C.I₀) :
        (fun _ : C.X i ↦ n i) ∘ pullback.fst (C.f i) f =
          (fun _ : V ↦ a) ∘ pullback.snd (C.f i) f := by
      funext w
      exact compare (C.f i) f (n i) a (t i) eU.some w
    exact congrArg (fun S : Set V ↦ v ∈ S)
      ((htest V f (fun _ ↦ a) hc r).1) |>.to_iff
  refine ⟨R, hclosed, ?_, fun U ↦ mem_test U.left U.hom, ?_, ?_, ?_⟩
  · intro x r
    constructor
    · intro hx
      obtain ⟨i, v, rfl⟩ := C.forgetQc.exists_eq x
      have hn := (mem_cover i v r).mp hx
      have : WeaklyEtale (C.f i) := C.forgetQc.map_prop i
      have ee : Nonempty ((CondensedRing.upperStar Λ (C.f i)).obj L ≅
          Mod.finiteFree (condensedRingObj Λ (C.X i)) r) := by
        rw [← hn]
        exact ⟨t i⟩
      exact rankWitness (C.f i)
        (fun Y f ↦ Nonempty ((CondensedRing.upperStar Λ (X := Y) (Y := X) f).obj L ≅
          Mod.finiteFree (condensedRingObj Λ Y) r)) ee v
    · rintro ⟨U, v, rfl, he⟩
      exact (mem_test U.left U.hom r he v r).mpr rfl
  · intro hcompact
    let := hcompact
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun r ↦ (R r : Set X)) (fun r ↦ (R r).isOpen) (by rw [hcover])
    apply s.finite_toSet.subset
    rintro r ⟨x, hx⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    by_contra hr
    have hne : r ≠ a := fun h ↦ hr (h ▸ ha)
    have hb : x ∈ (⊥ : X.Opens) :=
      (show R r ⊓ R a ≤ ⊥ from (hdisjoint hne).le_bot) ⟨hx, hxa⟩
    exact hb
  · have hc : (⨆ r, ((R r).ι).opensRange) = ⊤ := by
      simpa only [Scheme.Opens.opensRange_ι, ← TopologicalSpace.Opens.coe_inj,
        TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using hcover
    have hd : Pairwise (fun r s ↦
        Disjoint (((R r).ι).opensRange) (((R s).ι).opensRange)) := by
      simpa only [Scheme.Opens.opensRange_ι] using hdisjoint
    exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk X (fun r ↦ (R r).ι))).mp
        (nonempty_isColimit_cofanMk_of (fun r ↦ (R r).ι) hc hd)
  · intro r
    apply rankRestrictedCover C n R mem_cover
      (fun Y f a ↦ Nonempty ((CondensedRing.upperStar Λ
        (X := Y) (Y := X) f).obj L ≅
          Mod.finiteFree (condensedRingObj Λ Y) a)) ?_ (fun i ↦ ⟨t i⟩) r
    intro Y Z f g a e
    exact rankPullbackTrivialization Λ f g L a e.some


/-- The rank of a lisse `E_X`-module is independent of every trivialization and every
preimage, and its rank loci are clopen. The canonical map from their scheme coproduct is an
isomorphism. On the rank-`r` open subscheme the module is pro-etale locally free of rank `r`;
only finitely many loci are nonempty when `X` is quasi-compact.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-stratified-lattice/
sk-lem-stratified-lattice-rank.md (blueprint: det-lem-stratified-lattice-rank).

Proof:
1. Choose the finite-free pro-etale trivializing cover. Pullback preserves the regular
   module and finite biproducts, hence preserves finite free modules with their ranks.
   The pullback composition isomorphism gives trivializations on each overlap.
   `continuous_coefficient_finiteFree_rank` equates their ranks on a nonempty overlap.
2. Apply `labelledClopenPartition_existsUnique_of_fpqc` to the constant rank labels.
   Its test-morphism clause, using the same overlap comparison, gives the rank formula
   for every further trivialization and every preimage. Joint surjectivity of the original
   cover supplies the existential characterization.
3. The disjoint open partition gives a coproduct cocone by
   `nonempty_isColimit_cofanMk_of`, so its canonical map is an isomorphism. On each rank
   open, base change the original pro-etale cover. Every member with a different rank is
   empty. Refine those members by empty covers and the others by identity covers; the
   composite cover carries rank-r trivializations.
4. A finite subcover of the rank opens exists when X is quasi-compact. Any nonempty
   rank piece meets a selected piece, and disjointness forces their labels to agree.
   This includes the empty scheme and rank zero, with no finite-index assumption.
-/
theorem exists_clopen_rank_decomposition_of_isLisse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (@Profinite.continuousCoefficientRingObj E
        (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
        (@NonUnitalSeminormedRing.toIsTopologicalRing E
          (@SeminormedRing.toNonUnitalSeminormedRing E
            (spectralNorm.seminormedRing ℚ_[l] E)))) X))
    (hL : IsLisseCoefficientModule (@Profinite.continuousCoefficientRingObj E
      (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
      (@NonUnitalSeminormedRing.toIsTopologicalRing E
        (@SeminormedRing.toNonUnitalSeminormedRing E
          (spectralNorm.seminormedRing ℚ_[l] E)))) L) :
    ∃ R : ℕ → X.Opens,
      (∀ r : ℕ, IsClosed (R r : Set X)) ∧
      (∀ (x : X) (r : ℕ), x ∈ R r ↔
        ∃ (U : X.ProEt) (v : U.left), U.hom v = x ∧
          Nonempty
            ((CondensedRing.upperStar (X := U.left) (Y := X)
              (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) r)) ∧
      (∀ (U : X.ProEt) (n : ℕ),
        Nonempty
          ((CondensedRing.upperStar (X := U.left) (Y := X)
              (@Profinite.continuousCoefficientRingObj E
            (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
            (@NonUnitalSeminormedRing.toIsTopologicalRing E
              (@SeminormedRing.toNonUnitalSeminormedRing E
                (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
            Mod.finiteFree
              (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                (@NonUnitalSeminormedRing.toIsTopologicalRing E
                  (@SeminormedRing.toNonUnitalSeminormedRing E
                    (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) n) →
        ∀ (v : U.left) (r : ℕ), U.hom v ∈ R r ↔ n = r) ∧
      (CompactSpace X → {r : ℕ | (R r : Set X).Nonempty}.Finite) ∧
      IsIso (Sigma.desc (fun r : ℕ ↦ (R r).ι)) ∧
      ∀ r : ℕ, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (R r).toScheme,
        ∀ i : C.I₀,
          Nonempty
            ((CondensedRing.upperStar (X := C.X i) (Y := X)
              (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E))))
                (C.f i ≫ (R r).ι)).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) (C.X i)) r) := by
  exact rankDecomposition _ (spectralRank l E) X L hL

end AlgebraicGeometry.ProEtale
