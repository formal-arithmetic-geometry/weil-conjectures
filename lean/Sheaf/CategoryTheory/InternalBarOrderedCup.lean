/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

public import Sheaf.CategoryTheory.InternalBarOrderedCupCore
import Sheaf.CategoryTheory.InternalBarEquivariantCharacterLifts
import Sheaf.CategoryTheory.InternalBarSmallHomComparison
import Sheaf.CategoryTheory.InternalBarCupBracketing

/-! # Assembly of the ordered character cup comparison

Source: the internal bar normalization argument in paragraph (3) of the
six-functors direct-image proof (blueprint: lem-sfb-internal-bar-ordered-cup).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
namespace CategoryTheory.CondensedBar.OrderedCup

private lemma sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private lemma sign_pow (n : ℕ) : (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n hn => simpa only [pow_succ] using sign_mul hn (Or.inr rfl)

private lemma characterCupSign_sign (t : ℕ → ℕ → ℤ)
    (ht : ∀ p r : ℕ, t p r = 1 ∨ t p r = -1) (q : ℕ) :
    characterCupSign t q = 1 ∨ characterCupSign t q = -1 := by
  induction q with
  | zero => exact Or.inl rfl
  | succ q hq =>
    by_cases h : q = 0
    · simp [characterCupSign, h]
    · simpa only [characterCupSign, if_neg h] using sign_mul hq (ht q 1)

private lemma sign_cancel {M : Type*} [AddCommGroup M] {s : ℤ}
    (hs : s = 1 ∨ s = -1) {x y : M} (h : x = s • y) : y = s • x := by
  rcases hs with rfl | rfl
  · simpa using h.symm
  · simpa using (congrArg Neg.neg h).symm

/-- Ordered character cocycles equal the specified derived cups up to a universal sign.
The sign is quantified before the ring, group, compatible model, resolution and characters.
Source: main-20261015 direct-images proof, paragraph (3), agent-formulated internal bar
obligation; exact reference wanted (blueprint: lem-sfb-internal-bar-ordered-cup).

Proof:
1. lem-sfb-condensed-internal-bar-resolution supplies the exact homogeneous resolution P,
   its free-module property and its inhomogeneous coordinate change.
2. For a character a put b(g,h)=a(g⁻¹h). Define L_a by deleting g_0 and multiplying
   by b(g_0,g_1). In dL+Ld the deletion terms with index at least two cancel; the
   remainder is b(g_0,g_1)+b(g_1,g_2)-b(g_0,g_2)=0. Thus P → P[1] is a chain map.
3. Compose the shifted L operators in the supplied order. Augmentation gives coefficient
   product_k a_k(g_{k-1}⁻¹g_k), whose coordinate change is precisely the displayed z.
   Its chain-map law proves cocyclicity. For q=0 use the augmentation and empty product.
4. In the character extension lift the quotient unit by [g] ↦ (a(g),1). Its boundary
   is (b(g,h),0). lem-sfb-internal-bar-roof-adjunction identifies this roof with the
   positive connecting class of lem-sfb-condensed-derived-restriction-calculus.
5. lem-sfb-internal-inflation-graded-cup identifies repeated ordered cup with shifted
   roof composition up to universal signs T_q with T_0=T_1=1. The intervening shifted
   inverse augmentations cancel, leaving the composite in step 3.
6. lem-sfb-internal-bar-roof-adjunction sends that roof to jz with universal sign s_q.
   Consequently epsilon_q=s_q T_q, independent of every input and equal to 1 at q=0,1.
   lem-sfb-condensed-derived-invariant-bar fixes the augmentation used here; its
   formula is the same in the equivalent small-Hom localization. No inverse of j or
   acyclicity of any underived internal-Hom term is used.
-/
theorem internal_bar_ordered_cup :
    ∃ ε : ℕ → ℤ, (∀ q : ℕ, ε q = 1 ∨ ε q = -1) ∧ ε 0 = 1 ∧ ε 1 = 1 ∧
    ∀ (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
      [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      (F : InternalFunctions A) (B : BarDiagram (G := G) F)
      (a : Augmentation (invariants A G) B)
      (t : TotalAugmentation (invariants A G) B a)
      (I : InjectiveResolution (regularTrivial A G)),
      IsIso (augmentationArrow t I) ∧
      ∃ j : underived B ⟶ resolved B I, IsUnderivedComparison B I j ∧
        ∀ (q : ℕ) (a : Fin q → Character A G),
          ∃ c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
              (Mod.regular A.X) ⟶ extend (underived B),
            IsCharacterCocycle B q a c ∧
            cocycleArrow j q c = (ε q) • (characterCup q a ≫ augmentationArrow t I) := by
  obtain ⟨t, ht, _, _, _, hcup⟩ := internalBarCharacterRoofCup.{u}
  let U : ℕ → ℤ := fun q ↦ (-1 : ℤ) ^ q * characterCupSign t q
  let ε : ℕ → ℤ := fun q ↦ (-1 : ℤ) ^ (q * (q + 1) / 2) * U q
  have hU (q : ℕ) : U q = 1 ∨ U q = -1 :=
    sign_mul (sign_pow q) (characterCupSign_sign t ht q)
  refine ⟨ε, fun q ↦ sign_mul (sign_pow _) (hU q), ?_, ?_, ?_⟩
  · simp [ε, U, characterCupSign]
  · simp [ε, U, characterCupSign]
  intro A G _ _ _ _ _ _ F B a tB I
  obtain ⟨R⟩ := Profinite.CondensedAction.InternalBar.exists_resolution A.toMon G
  obtain ⟨l⟩ := Profinite.CondensedAction.InternalBarCharacter.exists_lifts R B
  obtain ⟨e, he, heq, L, hL, haug⟩ := exists_equivariant_character_lifts R B l
  let : QuasiIso e := he
  obtain ⟨hiso, j, hj, hcompare⟩ := small_hom_bar_roof_comparison B a tB I R e heq
  refine ⟨hiso, j, hj, ?_⟩
  have hlist (as : List (Character A G)) :
      ∃ c : (HomologicalComplex.single (Modules A) (.up ℤ) (as.length : ℤ)).obj
          (Mod.regular A.X) ⟶ extend (underived B),
        IsCharacterCocycle B as.length (fun i ↦ as.get i) c ∧
        cocycleArrow j as.length c =
          ε as.length • (characterCup as.length (fun i ↦ as.get i) ≫ augmentationArrow tB I) := by
    refine ⟨l.cocycle as, ?_, ?_⟩
    · intro S T f g
      have hc := l.cocycle_formula as S (1 : sectionRing A S) T f g
      dsimp only [Profinite.CondensedAction.InternalBarCharacter.cocycleComponent,
        Profinite.CondensedAction.InternalBar.onSections, underived, regularTrivial,
        AddCommGrpCat.Hom.hom] at hc ⊢
      simp only [map_one, one_mul] at hc
      convert hc using 1
      rfl
    · have hc := hcompare as.length
        (orderedCharacterLift R as.length (fun i ↦ L (as.get i))) (l.cocycle as) (by
          intro S x
          rw [haug as]
          exact l.coordinates as S x)
      have hprod := ((hcup A G R e heq).2 as.length
        (fun i ↦ as.get i) (fun i ↦ L (as.get i)) (fun i ↦ hL (as.get i))).2
      rw [ordered_character_cup_eq] at hprod
      have hinv : inflationPhi A G as.length
          (characterRoof R e as.length
            (orderedCharacterLift R as.length (fun i ↦ L (as.get i)))) =
          U as.length • characterCup as.length (fun i ↦ as.get i) := by
        exact sign_cancel (hU as.length) hprod
      rw [hinv, Preadditive.zsmul_comp, smul_smul] at hc
      exact hc
  intro q a
  let P : (Σ n : ℕ, Fin n → Character A G) → Prop := fun s ↦
    ∃ c : (HomologicalComplex.single (Modules A) (.up ℤ) (s.1 : ℤ)).obj
        (Mod.regular A.X) ⟶ extend (underived B),
      IsCharacterCocycle B s.1 s.2 c ∧
      cocycleArrow j s.1 c = ε s.1 • (characterCup s.1 s.2 ≫ augmentationArrow tB I)
  obtain ⟨as, has⟩ := (List.equivSigmaTuple (α := Character A G)).surjective ⟨q, a⟩
  change P ⟨q, a⟩
  rw [← has]
  exact hlist as

end CategoryTheory.CondensedBar.OrderedCup
