/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.CategoryTheory.Localization.Pi
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Derived-functor calculus in one to four variables

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md,
paragraph on two-variable derived tensor, iterated products, and descending constraints
(blueprint: lem-sfb-multivariable-derived-calculus).

The main theorem supplies product derivability, existence, the universal bijection,
and detection on resolving tuples. The second theorem records all the comparison
laws using Mathlib's canonical `Functor.leftDerivedNatTrans`.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uP vP uD vD uH vH

namespace CategoryTheory

open _root_.CategoryTheory.Functor

private theorem finitePiConnected {J : Type} [Finite J] (C : J → Type uA)
    [∀ j, Category.{vA} (C j)] [∀ j, IsConnected (C j)] :
    IsConnected (∀ j, C j) := by
  classical
  revert J
  apply Finite.induction_empty_option
  · intro J₁ J₂ e h C _ _
    have := h (fun j ↦ C (e j))
    exact isConnected_of_equivalent (Pi.equivalenceOfEquiv C e)
  · intro C _ _
    exact isConnected_of_nonempty_and_subsingleton
  · intro J _ h C _ _
    have := h (fun j ↦ C (some j))
    exact isConnected_of_equivalent (Pi.optionEquivalence C).symm

section PiSquares

variable {J : Type} {C₁ : J → Type uA} {C₂ : J → Type uP}
  {C₃ : J → Type uD} {C₄ : J → Type uH}
  [∀ j, Category.{vA} (C₁ j)] [∀ j, Category.{vP} (C₂ j)]
  [∀ j, Category.{vD} (C₃ j)] [∀ j, Category.{vH} (C₄ j)]
  {T : ∀ j, C₁ j ⥤ C₂ j} {L₀ : ∀ j, C₁ j ⥤ C₃ j}
  {R : ∀ j, C₂ j ⥤ C₄ j} {B : ∀ j, C₃ j ⥤ C₄ j}
  (w : ∀ j, TwoSquare (T j) (L₀ j) (R j) (B j))

private abbrev piSquare : TwoSquare (Functor.pi T) (Functor.pi L₀)
    (Functor.pi R) (Functor.pi B) := NatTrans.pi w

variable {X₂ : ∀ j, C₂ j} {X₃ : ∀ j, C₃ j}
  (g : (Functor.pi R).obj X₂ ⟶ (Functor.pi B).obj X₃)

set_option backward.isDefEq.respectTransparency false in
private def piTriplesTo :
    (piSquare w).StructuredArrowRightwards g ⥤
      ∀ j, (w j).StructuredArrowRightwards (g j) where
  obj X j := TwoSquare.StructuredArrowRightwards.mk (w j) (g j)
    (X.right.left j) (X.hom.left j) (X.right.hom j) (by
      have h := congrFun X.hom.w j
      dsimp [TwoSquare.costructuredArrowRightwards, piSquare,
        Comma.mapLeft, CostructuredArrow.post] at h ⊢
      change (R j).map _ ≫ (w j).app _ ≫ (B j).map _ = g j
      simpa [Functor.pi, NatTrans.pi] using h)
  map {X Y} f j := StructuredArrow.homMk
    (CostructuredArrow.homMk (f.right.left j) (by
      exact congrFun (CostructuredArrow.w f.right) j)) (by
        ext
        have eq := congrArg (fun k ↦ k.left j) (StructuredArrow.w f)
        dsimp at eq ⊢
        exact eq)
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private def piTriplesFrom :
    (∀ j, (w j).StructuredArrowRightwards (g j)) ⥤
      (piSquare w).StructuredArrowRightwards g where
  obj X := TwoSquare.StructuredArrowRightwards.mk _ _ (fun j ↦ (X j).right.left)
    (fun j ↦ (X j).hom.left) (fun j ↦ (X j).right.hom) (by
      funext j
      have h := (X j).hom.w
      dsimp [TwoSquare.costructuredArrowRightwards, piSquare,
        Comma.mapLeft, CostructuredArrow.post] at h ⊢
      change (R j).map _ ≫ (w j).app _ ≫ (B j).map _ = g j
      simpa [Functor.pi, NatTrans.pi] using h)
  map {X Y} f := StructuredArrow.homMk
    (CostructuredArrow.homMk (fun j ↦ (f j).right.left) (by
      funext j
      exact CostructuredArrow.w (f j).right)) (by
        ext j
        have eq := congrArg (fun k ↦ k.left) (StructuredArrow.w (f j))
        dsimp at eq ⊢
        exact eq)
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private def piTriplesEquivalence :
    (piSquare w).StructuredArrowRightwards g ≌
      ∀ j, (w j).StructuredArrowRightwards (g j) where
  functor := piTriplesTo w g
  inverse := piTriplesFrom w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    ext j
    simp [piTriplesTo, piTriplesFrom]

private theorem piSquareExact [Finite J] [∀ j, (w j).GuitartExact] :
    (piSquare w).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ g
  have : ∀ j, IsConnected ((w j).StructuredArrowRightwards (g j)) :=
    fun j ↦ TwoSquare.GuitartExact.isConnected_rightwards (w := w j) (g j)
  have := finitePiConnected (fun j ↦ (w j).StructuredArrowRightwards (g j))
  exact isConnected_of_equivalent (piTriplesEquivalence w g).symm

end PiSquares

variable (n : ℕ) (A : Fin n → Type uA) (P : Fin n → Type uP) (D : Fin n → Type uD)
  [∀ i, Category.{vA} (A i)] [∀ i, Category.{vP} (P i)] [∀ i, Category.{vD} (D i)]
  (I : ∀ i, P i ⥤ A i) [∀ i, (I i).Full] [∀ i, (I i).Faithful]
  (W : ∀ i, MorphismProperty (A i)) (L : ∀ i, A i ⥤ D i)
  [∀ i, (W i).ContainsIdentities] [∀ i, (L i).IsLocalization (W i)]
  {H : Type uH} [Category.{vH} H]

/-- Source: the derived-monoidal proof in the module header, sentences on two-variable
and iterated tensor descent (blueprint: lem-sfb-multivariable-derived-calculus).

Proof plan:
1. Apply `lem-sfb-product-localization` to the ambient and resolving categories,
   with the inverse-image classes on the latter. Use the products of the induced
   localized functors and comparison isomorphisms for the product square.
2. Resolutions assemble coordinatewise. The triple category testing finality is the
   finite product of the coordinate triple categories, since both equations for its
   arrows are coordinatewise. Choose an object in every nonempty factor. To join two
   tuples, concatenate coordinate zigzags, using identities in all other coordinates.
   Finiteness of `Fin n` makes this a finite zigzag. Thus the product triple category
   is nonempty and connected. This proves product left derivability.
3. For the identity inclusion, the identity resolves each object and `(X,id,b)` is
   terminal in each triple category, so it is a left derivability structure.
4. Factor each tuple of weak equivalences into arrows changing one coordinate at a
   time. The coordinate inversion hypothesis then inverts the entire product class.
   Apply `lem-sfb-unary-left-derived-calculus` to obtain the universal bijection,
   its candidate criterion, and invertibility of the counit on resolving tuples.
5. The comparison laws are stated in `multivariableDerivedComparisons` below.
6. Injectivity of the universal bijection gives cancellation against the counit.
7. By `lem-trf-localization-essentially-surjective`, each localized object is
   isomorphic to the image of an ambient object. Resolve that object in each coordinate;
   localization inverts the resolution arrows. Their product gives an isomorphism from
   a resolving tuple to the given tuple. Naturality of both transformations along this
   isomorphism and cancellation of its image show that their components agree there.
   Extensionality then gives equality of transformations.
-/
theorem multivariableDerivedCalculus
    (hn : 1 ≤ n ∧ n ≤ 4)
    (hP : ∀ i,
      (LocalizerMorphism.ofEq (F := I i) (W₂ := W i) rfl).IsLeftDerivabilityStructure)
    (F : (∀ i, A i) ⥤ H)
    (hF : ∀ (i : Fin n) (p q : ∀ j, P j)
      (f : (fun j ↦ (I j).obj (p j)) ⟶ (fun j ↦ (I j).obj (q j)))
      (h : ∀ j, j ≠ i → p j = q j),
      (∀ (j : Fin n) (hj : j ≠ i),
        f j = eqToHom (congrArg (fun x ↦ (I j).obj x) (h j hj))) →
      W i (f i) → IsIso (F.map f)) :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) ∧
    (LocalizerMorphism.ofEq (F := Functor.pi I)
      (W₂ := MorphismProperty.pi W) rfl).IsLeftDerivabilityStructure ∧
    (∀ i, (LocalizerMorphism.id (W i)).IsLeftDerivabilityStructure) ∧
    (∃ (LF : (∀ i, D i) ⥤ H) (ε : Functor.pi L ⋙ LF ⟶ F),
      (∀ V : (∀ i, D i) ⥤ H,
        Function.Bijective (fun γ : V ⟶ LF ↦ whiskerLeft (Functor.pi L) γ ≫ ε)) ∧
      (∀ p : ∀ i, P i, IsIso (ε.app (fun i ↦ (I i).obj (p i))))) ∧
    (∀ (T : (∀ i, D i) ⥤ H) (η : Functor.pi L ⋙ T ⟶ F),
      (∀ V : (∀ i, D i) ⥤ H,
        Function.Bijective (fun γ : V ⟶ T ↦ whiskerLeft (Functor.pi L) γ ≫ η)) ↔
      ∀ p : ∀ i, P i, IsIso (η.app (fun i ↦ (I i).obj (p i)))) ∧
    (∀ (V V' : (∀ i, D i) ⥤ H) (γ δ : V ⟶ V'),
      (∀ p : ∀ i, P i,
        γ.app (fun i ↦ (L i).obj ((I i).obj (p i))) =
          δ.app (fun i ↦ (L i).obj ((I i).obj (p i)))) → γ = δ) := by
  classical
  obtain ⟨_, _⟩ := hn
  let Φ := fun i ↦ LocalizerMorphism.ofEq (F := I i) (W₂ := W i) rfl
  have : ∀ i, (Φ i).IsLeftDerivabilityStructure := hP
  let WP := fun i ↦ (W i).inverseImage (I i)
  let Ψ := LocalizerMorphism.ofEq (F := Functor.pi I)
    (W₂ := MorphismProperty.pi W) rfl
  have hres : Ψ.HasLeftResolutions := by
    intro x
    let r := fun i ↦ Classical.choice
      (LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
        (Φ := Φ i) (x i))
    exact ⟨{ X₁ := fun i ↦ (r i).X₁
             w := fun i ↦ (r i).w
             hw := fun i ↦ (r i).hw }⟩
  have hprod : Ψ.IsLeftDerivabilityStructure := by
    let LP := fun i ↦ (WP i).Q
    let E := fun i ↦ (Φ i).localizedFunctor (LP i) (L i)
    let e := fun i ↦ ((Φ i).catCommSq (LP i) (L i)).iso
    have : (Functor.pi LP).IsLocalization
        ((MorphismProperty.pi W).inverseImage (Functor.pi I)) := by
      change (Functor.pi LP).IsLocalization (MorphismProperty.pi WP)
      infer_instance
    rw [Ψ.isLeftDerivabilityStructure_iff (Functor.pi LP) (Functor.pi L)
      (Functor.pi E) (NatIso.pi e)]
    have : ∀ i, TwoSquare.GuitartExact (e i).inv := fun i ↦
      (Φ i).guitartExact_of_isLeftDerivabilityStructure (LP i) (L i)
    exact piSquareExact (fun i ↦ (e i).inv)
  have hDerives : Ψ.Derives F := by
    intro p q g hg
    have aux : ∀ (s : Finset (Fin n)) (p q : ∀ i, P i)
        (f : (fun i ↦ (I i).obj (p i)) ⟶ (fun i ↦ (I i).obj (q i))),
        (∀ j, W j (f j)) →
        ∀ (heq : ∀ j, j ∉ s → p j = q j),
        (∀ (j : Fin n) (hj : j ∉ s),
          f j = eqToHom (congrArg (fun x ↦ (I j).obj x) (heq j hj))) →
        IsIso (F.map f) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro p q f hf heq hf'
        have hpq : p = q := funext (fun j ↦ heq j (by simp))
        subst q
        have hfid : f = 𝟙 _ := by
          funext j
          simpa using hf' j (by simp)
        rw [hfid, F.map_id]
        infer_instance
      | @insert i s hi ih =>
        intro p q f hf heq hf'
        let r : ∀ j, P j := fun j ↦ if j = i then q j else p j
        let a : (fun j ↦ (I j).obj (p j)) ⟶ (fun j ↦ (I j).obj (r j)) :=
          fun j ↦ by
            by_cases hj : j = i
            · simpa [r, hj] using f j
            · exact eqToHom (by simp [r, hj])
        let b : (fun j ↦ (I j).obj (r j)) ⟶ (fun j ↦ (I j).obj (q j)) :=
          fun j ↦ by
            by_cases hj : j = i
            · exact eqToHom (by simp [r, hj])
            · simpa [r, hj] using f j
        have ha : IsIso (F.map a) := by
          apply hF i p r a (fun j hj ↦ by simp [r, hj])
          · intro j hj
            simp [a, r, hj]
          · exact (W i).of_eq (hf i) rfl (by simp [r]) (by simp [a, r])
        have hb : IsIso (F.map b) := by
          refine ih r q b ?_ (fun j hj ↦ ?_) ?_
          · intro j
            by_cases hj : j = i
            · subst j
              simp only [b, ↓reduceDIte]
              exact MorphismProperty.ContainsIdentities.eqToHom (W i) _
            · exact (W j).of_eq (hf j) (by simp [r, hj]) rfl
                (by simp [b, r, hj])
          · by_cases hji : j = i
            · simp [r, hji]
            · simpa [r, hji] using heq j (by simp [hj, hji])
          · intro j hj
            by_cases hji : j = i
            · subst j
              simp [b, r]
            · dsimp [b]
              simp only [dif_neg hji]
              rw [hf' j (by simp [hj, hji])]
              apply eq_of_heq
              exact (cast_heq ..).trans
                ((eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm)
        have hab : a ≫ b = f := by
          funext j
          by_cases hj : j = i <;> simp [a, b, r, hj]
        rw [← hab, F.map_comp]
        infer_instance
    let g' : p ⟶ q := fun i ↦ (I i).preimage ((I i).map (g i))
    have hgg : g' = g := funext (fun i ↦ (I i).preimage_map (g i))
    have hg' : (MorphismProperty.pi W) ((Functor.pi I).map g') := by
      rw [hgg]
      exact hg
    have h := aux Finset.univ p q ((Functor.pi I).map g') hg'
      (fun j hj ↦ False.elim (hj (Finset.mem_univ j)))
      (fun j hj ↦ False.elim (hj (Finset.mem_univ j)))
    rw [hgg] at h
    exact h
  have := hDerives.hasLeftDerivedFunctor
  let LF := F.totalLeftDerived (Functor.pi L) (MorphismProperty.pi W)
  let ε := F.totalLeftDerivedCounit (Functor.pi L) (MorphismProperty.pi W)
  have hbij : ∀ (T : (∀ i, D i) ⥤ H) (η : Functor.pi L ⋙ T ⟶ F),
      T.IsLeftDerivedFunctor η (MorphismProperty.pi W) ↔
        ∀ V : (∀ i, D i) ⥤ H,
          Function.Bijective (fun γ : V ⟶ T ↦ whiskerLeft (Functor.pi L) γ ≫ η) := by
    intro T η
    constructor
    · intro hT V
      have := Functor.IsLeftDerivedFunctor.isRightKanExtension T η (MorphismProperty.pi W)
      exact (T.homEquivOfIsRightKanExtension η V).bijective
    · intro hb
      refine ⟨⟨⟨Limits.IsTerminal.ofUniqueHom (fun X ↦ ?_) ?_⟩⟩⟩
      · exact CostructuredArrow.homMk
          ((hb X.left).2 X.hom).choose ((hb X.left).2 X.hom).choose_spec
      · intro X m
        apply CostructuredArrow.hom_ext
        apply (hb X.left).1
        exact (CostructuredArrow.w m).trans
          ((hb X.left).2 X.hom).choose_spec.symm
  refine ⟨inferInstance, hprod, fun i ↦ inferInstance, ?_, ?_, ?_⟩
  · exact ⟨LF, ε, (hbij LF ε).mp inferInstance,
      fun p ↦ hDerives.isIso_of_isLeftDerivedFunctor ε p⟩
  · intro T η
    rw [← hbij T η]
    exact hDerives.isLeftDerivedFunctor_iff_isIso η
  · intro V V' γ δ hγ
    have : (Ψ.functor ⋙ Functor.pi L).EssSurj :=
      Ψ.essSurj_of_hasLeftResolutions (Functor.pi L)
    ext y
    let E := (Ψ.functor ⋙ Functor.pi L)
    let e := E.objObjPreimageIso y
    apply (cancel_epi (V.map e.hom)).mp
    rw [γ.naturality, δ.naturality]
    exact congrArg (fun t ↦ t ≫ V'.map e.hom) (hγ (E.objPreimage y))

/-- Source: the derived-monoidal proof in the module header, sentences on descending
constraints and coherence (blueprint: lem-sfb-multivariable-derived-calculus).

Proof plan: for `τ : F ⟶ G`, apply the universal bijection of `(LG,εG)` with test
functor `LF` to `εF ≫ τ`. Its inverse is Mathlib's `leftDerivedNatTrans`. The
bijection gives its component equation and uniqueness. The identity satisfies the
identity equation; composition satisfies the composite equation. Uniqueness gives
both functoriality laws. Applying them to `τ` and its inverse proves preservation of
isomorphisms. Finally, injectivity of the universal bijection gives cancellation
against `εF`, for every test functor `V`.

The input functors and counits are arbitrary chosen total left derived functors;
the preceding theorem supplies these choices under the coordinate hypotheses.
-/
theorem multivariableDerivedComparisons
    (hn : 1 ≤ n ∧ n ≤ 4)
    (F G K : (∀ i, A i) ⥤ H) (LF LG LK : (∀ i, D i) ⥤ H)
    (εF : Functor.pi L ⋙ LF ⟶ F) (εG : Functor.pi L ⋙ LG ⟶ G)
    (εK : Functor.pi L ⋙ LK ⟶ K)
    [LF.IsLeftDerivedFunctor εF (MorphismProperty.pi W)]
    [LG.IsLeftDerivedFunctor εG (MorphismProperty.pi W)]
    [LK.IsLeftDerivedFunctor εK (MorphismProperty.pi W)] :
    (∀ τ : F ⟶ G,
      (∀ x : ∀ i, A i,
        (Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ).app
            ((Functor.pi L).obj x) ≫ εG.app x = εF.app x ≫ τ.app x) ∧
      ∀ m : LF ⟶ LG,
        (∀ x : ∀ i, A i,
          m.app ((Functor.pi L).obj x) ≫ εG.app x = εF.app x ≫ τ.app x) →
        m = Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ) ∧
    Functor.leftDerivedNatTrans LF LF εF εF (MorphismProperty.pi W) (𝟙 F) = 𝟙 LF ∧
    (∀ (τ : F ⟶ G) (σ : G ⟶ K),
      Functor.leftDerivedNatTrans LF LK εF εK (MorphismProperty.pi W) (τ ≫ σ) =
        Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ ≫
          Functor.leftDerivedNatTrans LG LK εG εK (MorphismProperty.pi W) σ) ∧
    (∀ (τ : F ⟶ G), IsIso τ →
      IsIso (Functor.leftDerivedNatTrans LF LG εF εG (MorphismProperty.pi W) τ)) ∧
    (∀ (V : (∀ i, D i) ⥤ H) (γ₁ γ₂ : V ⟶ LF),
      whiskerLeft (Functor.pi L) γ₁ ≫ εF = whiskerLeft (Functor.pi L) γ₂ ≫ εF →
      γ₁ = γ₂) := by
  obtain ⟨_, _⟩ := hn
  refine ⟨?_, Functor.leftDerivedNatTrans_id LF εF (MorphismProperty.pi W), ?_, ?_, ?_⟩
  · intro τ
    refine ⟨Functor.leftDerivedNatTrans_app LF LG εF εG (MorphismProperty.pi W) τ, ?_⟩
    intro m hm
    apply Functor.leftDerived_ext LG εG (MorphismProperty.pi W) LF
    ext x
    exact (hm x).trans
      (Functor.leftDerivedNatTrans_app LF LG εF εG (MorphismProperty.pi W) τ x).symm
  · intro τ σ
    exact (Functor.leftDerivedNatTrans_comp LF LG LK εF εG εK
      (MorphismProperty.pi W) τ σ).symm
  · intro τ hτ
    exact (Functor.leftDerivedNatIso LF LG εF εG (MorphismProperty.pi W) (asIso τ)).isIso_hom
  · intro V γ₁ γ₂ hγ
    exact Functor.leftDerived_ext LF εF (MorphismProperty.pi W) V γ₁ γ₂ hγ

end CategoryTheory
