/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.CategoryTheory.InternalBarRoofAdjunction
public import Sheaf.CategoryTheory.InternalInflationGradedCup
public import Sheaf.CategoryTheory.InternalShiftedRoof
import Sheaf.CategoryTheory.InternalBarCharacterLiftNormalization
import Mathlib.Tactic.Ring

/-! # Character roofs and ordered internal cup products

Source: latest blueprint, six-functors direct-images proof, paragraph (3), the
agent-formulated internal character normalization and ordered-cup induction
(blueprint: lem-sfb-internal-bar-character-roof-cup).

The character, unipotent extension, boundary, homogeneous bar complex, adjunction and
cup are the recorded dependency constructions. The helpers only assemble their actual
maps and finite ordered composites. No projectivity or Hom acyclicity is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar CategoryTheory.CondensedBarRoof
open Profinite.CondensedAction.InternalBar
namespace CategoryTheory.CondensedDerivedRestriction

variable {A : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The augmented degree-minus-one component, with the ordinary cochain shift.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def characterLiftComponent (R : Resolution A.toMon G)
    (L : complex R ⟶ (complex R)⟦(1 : ℤ)⟧) : R.objects 1 ⟶ regularTrivial A G :=
  (termIso R 1).inv ≫ L.f (-1) ≫
    (CochainComplex.shiftFunctorObjXIso (complex R) 1 (-1) 0 rfl).hom ≫
      (termIso R 0).hom ≫ R.augmentation

/-- The equation eL[g₀,g₁] = a(g₀⁻¹g₁), on all generalized generators.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def IsCharacterLift (R : Resolution A.toMon G) (a : Character A G)
    (L : complex R ⟶ (complex R)⟦(1 : ℤ)⟧) : Prop :=
  ∀ (S : Profinite.{u}) (x : Fin 2 → C(S, G)),
    onSections A.toMon (characterLiftComponent R L).val S
      (basis A.toMon G 2 (R.objects 1) (R.freeIso 1) S x) =
        a.app S ((x 0)⁻¹ * x 1)

/-- The actual localized roof Q(e[q]F)Q(e)⁻¹, with canonical localization shifts.
The augmentation is specified by augmentationEquation; its quasi-isomorphism instance
is the exactness of the recorded bar resolution, not a projectivity hypothesis.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def characterRoof (R : Resolution A.toMon G) (e : RoofAugmentation R) [QuasiIso e]
    (q : ℕ) (F : complex R ⟶ (complex R)⟦(q : ℤ)⟧) :
    coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧ :=
  localizedShiftedRoof DerivedCategory.Q.{u + 1} e
    ((DerivedCategory.singleFunctorIsoCompQ (Equivariant A G) 0).app
      (regularTrivial A G)) (q : ℤ) F

/-- F₀ is the identity, and F_q is L_q[q-1] ... L_1 with canonical shift addition.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def orderedCharacterLift (R : Resolution A.toMon G) (q : ℕ)
    (L : Fin q → (complex R ⟶ (complex R)⟦(1 : ℤ)⟧)) :
    complex R ⟶ (complex R)⟦(q : ℤ)⟧ :=
  orderedShiftedArrows (complex R) q L

/-- The ordered derived composite, with the empty composition equal to the identity.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def orderedCharacterRoofs (q : ℕ)
    (x : Fin q → (coefficient A G ⟶ (coefficient A G)⟦(1 : ℤ)⟧)) :
    coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧ :=
  orderedShiftedArrows (coefficient A G) q x

/-- The ordered cup of the positive connecting classes; its empty value is the cup unit
under the regular-unit and zero-shift identifications.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def orderedCharacterCup : (q : ℕ) → (Fin q → Character A G) →
    (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))⟦-(q : ℤ)⟧ ⟶
      cohomology A G)
  | 0, _ => (shiftFunctorZero _ ℤ).hom.app
      ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)) ≫
        (baseUnitIso A).inv ≫ cupUnit (A := A) (G := G)
  | q + 1, a => inflationGradedCup A G q 1
      (orderedCharacterCup q (fun i ↦ a i.castSucc)) (characterClass (a (Fin.last q)))

/-- The universal sign recursion T₀ = T₁ = 1, T_(q+1) = T_q t_(q,1) for q ≥ 1.
Source: latest direct-images proof, paragraph (3), internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup). -/
def characterCupSign (t : ℕ → ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | q + 1 => if q = 0 then 1 else characterCupSign t q * t q 1

private lemma characterRoof_ordered (R : Resolution A.toMon G)
    (e : RoofAugmentation R) [QuasiIso e] (q : ℕ)
    (L : Fin q → (complex R ⟶ (complex R)⟦(1 : ℤ)⟧)) :
    characterRoof R e q (orderedCharacterLift R q L) =
      orderedCharacterRoofs q (fun i ↦ characterRoof R e 1 (L i)) :=
  localizedShiftedRoof_ordered DerivedCategory.Q.{u + 1} e
    ((DerivedCategory.singleFunctorIsoCompQ (Equivariant A G) 0).app
      (regularTrivial A G)) q L

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private lemma inflationGradedCup_zsmul_neg (p q : ℕ) (z : ℤ)
    (x : ((DerivedCategory.singleFunctor (Modules A) 0).obj
      (Mod.regular A.X))⟦-(p : ℤ)⟧ ⟶ cohomology A G)
    (y : ((DerivedCategory.singleFunctor (Modules A) 0).obj
      (Mod.regular A.X))⟦-(q : ℤ)⟧ ⟶ cohomology A G) :
    inflationGradedCup A G p q (z • x) (-y) =
      (-z) • inflationGradedCup A G p q x y := by
  have hx : (z • x) ▷ _ = z • (x ▷
      (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))⟦-(q : ℤ)⟧)) :=
    (MonoidalCategory.tensorRight _).map_zsmul
  have hy : _ ◁ (-y) = -(cohomology A G ◁ y) :=
    (MonoidalCategory.tensorLeft (cohomology A G)).map_neg
  simp only [inflationGradedCup, MonoidalCategory.tensorHom_def, hx, hy,
    Category.assoc, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_smul]

private lemma characterCupSign_step (t : ℕ → ℕ → ℤ) (ht : t 0 1 = 1) (q : ℕ) :
    (-1 : ℤ) ^ (q + 1) * characterCupSign t (q + 1) =
      -((-1 : ℤ) ^ q * characterCupSign t q) * t q 1 := by
  cases q with
  | zero => simp [characterCupSign, ht]
  | succ q =>
    rw [characterCupSign, if_neg (Nat.succ_ne_zero q), pow_succ]
    ring

/-- Every allowed character lift has the negative canonical extension boundary, its
shifted adjoint is the negative positive character class, and finite ordered roofs
compute the ordered cup with universal signs. The single sign family is quantified
before all coefficients, groups, characters and lifts.
Source: latest direct-images proof, paragraph (3), agent-formulated internal normalization
(blueprint: lem-sfb-internal-bar-character-roof-cup).

Proof (the node's five steps):
1. The character laws define E_a with action g(x,y)=(x+a(g)y,y). The inclusion and
   projection are equivariant and forgetting detects the split underlying exact
   sequence (restriction calculus). Freeness of P₀ gives the equivariant lift
   ell[g]=(a(g),1); deletion gives ell partial₁=(a(g₀⁻¹g₁),0), naturally on every test.
2. The extension clause of internal-bar-roof-adjunction gives the cocycle roof equal
   to minus the canonical triangle boundary. Since A[1] is concentrated in degree -1,
   the augmented-component equation identifies e[1]L with that cocycle map for every L.
3. The canonical invariant-inclusion adjunction sends the extension boundary to the
   positive connecting class of condensed-unipotent-class, after shifting down by one.
   Additivity of derived invariants and shifts therefore gives Phi₁(x_a)=-[a].
4. Exactness of the bar augmentation makes Q(e[q]) invertible. Insert its inverse
   between successive lifted factors and cancel to obtain rho_(q+1)=x_(q+1)[q] rho_q.
   Starting at the identity gives the ordered-composition formula without homotopy
   comparisons between different lifts or projectivity of any bar term.
5. The empty cup is the unit and Phi sends the identity to that unit. The one-factor
   formula is step 3. Apply the ordered (q,1) identity of internal-inflation-graded-cup
   and bilinearity inductively: the new sign is (-1) times t_(q,1), giving (-1)^q T_q.
   The graded-cup theorem supplies a single sign family independent of all objects.
   The zero ring, trivial group, characteristic two, and empty family are included.
-/
theorem internalBarCharacterRoofCup :
    ∃ t : ℕ → ℕ → ℤ,
      (∀ p r : ℕ, t p r = 1 ∨ t p r = -1) ∧
      (∀ p : ℕ, t p 0 = 1) ∧ (∀ r : ℕ, t 0 r = 1) ∧
      (∀ (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
        [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
        (p r : ℕ) (x : coefficient A G ⟶ (coefficient A G)⟦(p : ℤ)⟧)
        (y : coefficient A G ⟶ (coefficient A G)⟦(r : ℤ)⟧),
        inflationGradedCup A G p r (inflationPhi A G p x) (inflationPhi A G r y) =
          t p r • inflationPhi A G (p + r)
            (ShiftedHom.comp x y (by simp [Nat.cast_add, add_comm]))) ∧
      ∀ (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
        [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
        (R : Resolution A.toMon G) (e : RoofAugmentation R) [QuasiIso e],
        augmentationEquation R e →
        (∀ (a : Character A G) (L : complex R ⟶ (complex R)⟦(1 : ℤ)⟧),
          IsCharacterLift R a L →
          characterRoof R e 1 L = -(extensionExact a).singleδ ∧
          inflationPhi A G 1 (characterRoof R e 1 L) = -characterClass a) ∧
        (∀ (q : ℕ) (a : Fin q → Character A G)
          (L : Fin q → (complex R ⟶ (complex R)⟦(1 : ℤ)⟧)),
          (∀ i : Fin q, IsCharacterLift R (a i) (L i)) →
          characterRoof R e q (orderedCharacterLift R q L) =
            orderedCharacterRoofs q (fun i ↦ characterRoof R e 1 (L i)) ∧
          orderedCharacterCup q a = ((-1 : ℤ) ^ q * characterCupSign t q) •
            inflationPhi A G q (characterRoof R e q (orderedCharacterLift R q L))) := by
  obtain ⟨t, ht, ht0, h0t, hcup⟩ := internalInflationGradedCup.{u}
  refine ⟨t, ht, ht0, h0t, hcup, ?_⟩
  intro A G _ _ _ _ _ _ R e _ he
  have hsingle (a : Character A G) (L : complex R ⟶ (complex R)⟦(1 : ℤ)⟧)
      (hL : IsCharacterLift R a L) :
      characterRoof R e 1 L = -(extensionExact a).singleδ ∧
        inflationPhi A G 1 (characterRoof R e 1 L) = -characterClass a :=
    internalBarCharacterLiftNormalization A G R e he a L hL
  refine ⟨hsingle, ?_⟩
  intro q a L hL
  refine ⟨characterRoof_ordered R e q L, ?_⟩
  rw [characterRoof_ordered]
  induction q with
  | zero =>
    simp only [orderedCharacterCup, characterCupSign, pow_zero, mul_one, one_smul]
    simpa [orderedCharacterRoofs, orderedShiftedArrows, ShiftedHom.mk₀,
      shiftFunctorZero'] using (inflationPhiIdentity A G).symm
  | succ q ih =>
    have ha : characterClass (a (Fin.last q)) =
        -inflationPhi A G 1 (characterRoof R e 1 (L (Fin.last q))) :=
      (neg_eq_iff_eq_neg).mp (hsingle (a (Fin.last q)) (L (Fin.last q))
        (hL (Fin.last q))).2.symm
    rw [orderedCharacterCup, ih (fun i ↦ a i.castSucc) (fun i ↦ L i.castSucc)
      (fun i ↦ hL i.castSucc), ha, inflationGradedCup_zsmul_neg,
      hcup A G q 1, smul_smul, ← characterCupSign_step t (h0t 1) q]
    rfl

end CategoryTheory.CondensedDerivedRestriction
