/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.AlgebraicGeometry.FrobeniusFactorization
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-! Structural witness interface for the model Frobenius comparison. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

private theorem modelEnd_isModel :
    IsModelFrobenius (modelEnd D₀ X₀) X₀.hom
      (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))) := by
  have hF : (X₀.left.iterateFrobenius D₀.prime
      (D₀.model_characteristic X₀.hom) D₀.a).IsFrobenius (Nat.card D₀.k₀) := by
    intro R t φ hφ
    have hR := D₀.model_characteristic (t ≫ X₀.hom)
    have hn : t ≫ X₀.left.iterateFrobenius D₀.prime
        (D₀.model_characteristic X₀.hom) D₀.a =
        (Spec R).iterateFrobenius D₀.prime hR D₀.a ≫ t := by
      refine Scheme.Hom.ext (f := t ≫ _) (g := _ ≫ t) rfl ?_
      intro U
      simp only [eqToHom_refl, Scheme.Hom.comp_app]
      ext s
      change t.app U (s ^ D₀.p ^ D₀.a) = (t.app U s) ^ D₀.p ^ D₀.a
      exact map_pow (t.app U).hom s (D₀.p ^ D₀.a)
    have ha : (Spec R).iterateFrobenius D₀.prime hR D₀.a = Spec.map φ := by
      apply AlgebraicGeometry.ext_to_Spec
      change (Scheme.ΓSpecIso R).inv ≫
          ((Spec R).iterateFrobenius D₀.prime hR D₀.a).appTop =
        (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop
      rw [← Scheme.ΓSpecIso_inv_naturality]
      ext x
      change ((Scheme.ΓSpecIso R).inv x) ^ D₀.p ^ D₀.a =
        (Scheme.ΓSpecIso R).inv (φ x)
      rw [hφ, map_pow, D₀.card_base, D₀.cardinality_eq]
    rw [hn, ha]
  refine ⟨IsPullback.of_hasPullback _ _, _, hF, ?_⟩
  simpa only [modelEnd, Over.homMk_left, WeilConjectures.FiniteFieldDatum.schemeFrobenius]
    using (D₀.relativeFrobenius_projections X₀).1

private theorem inv_powers_cancel {T : Scheme.{u}} (e : Aut T) (m : ℕ) :
    ((End.of e.inv) ^ m) ≫ ((End.of e.hom) ^ m) = 𝟙 T := by
  induction m with
  | zero => simp [End.one_def]
  | succ m ih =>
    rw [pow_succ, pow_succ' (End.of e.hom), End.mul_def, End.mul_def]
    change (e.inv ≫ _) ≫ (_ ≫ e.hom) = _
    rw [Category.assoc, ← Category.assoc (((End.of e.inv) ^ m) : T ⟶ T), ih]
    simp

/-- Proof witnesses for the fixed model Frobenius and base-changed compactification.
Source: latest blueprint, lem-fd-realness-pushforward.proof.md, Step 1;
original operator comparison proof steps 1 and 5.
(blueprint: lem-fd-condensed-model-frobenius-operators-structural).

Proof: the geometric fibre is locally Noetherian over the algebraic closure. The
certified algebraic-closure constructibility comparison turns the strict carrier's
constant-model predicate into boundedConstructible. On affine tests, naturality of
absolute Frobenius is map_pow, so the relative factor is IsModelFrobenius; its proved
API gives finiteness and universal homeomorphism for every iterate. Compose the
absolute Frobenius factorization with powers of geometric Frobenius and cancel the
arithmetic inverse powers. At exponent zero both maps are identity. Finally compare
both projections of the open compactification square; Galois maps preserve the model
projection and have the same field action on the point projection. The proper square
is the second projection formula. The endomorphism power lemma iterates both squares.
Every existential witness here is a proposition about the existing constructions. -/
theorem condensed_model_frobenius_operators_structural
    [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D₀.p)]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (c₀ : Compactification X₀.hom) :
    ∃ _w : Factorization D₀ X₀,
      ∃ _hB : boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ell) (D₀.geometricFiber X₀).left)
        K.carrier.obj,
      ∃ _hf : ∀ m : ℕ, IsFinite (frobeniusIterate (modelEnd D₀ X₀) m).left,
      ∃ _hu : ∀ m : ℕ, IsUniversalHomeomorphism
        (frobeniusIterate (modelEnd D₀ X₀) m).left,
      ∃ _wj : ∀ m : ℕ,
        ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) ≫
          (geometricCompactification D₀ X₀ c₀).i =
        (geometricCompactification D₀ X₀ c₀).i ≫
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m),
      ∃ _wp : ∀ m : ℕ,
        ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m) ≫
          (geometricCompactification D₀ X₀ c₀).g =
        (geometricCompactification D₀ X₀ c₀).g ≫
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m), True := by
  classical
  let := Fintype.ofFinite D₀.k₀
  have : IsLocallyNoetherian (D₀.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D₀.geometricFiber X₀).hom
  have hB : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D₀.geometricFiber X₀).left)
      K.carrier.obj := by
    erw [(adicConstructibilityPredicateComparison ell (D₀.geometricFiber X₀).left
      (Profinite.padicAlgClRingObj ell) .algebraicClosure).2]
    exact K.carrier.property.1
  have hmod := modelEnd_isModel D₀ X₀
  refine ⟨?_, hB, hmod.isFinite, hmod.isUniversalHomeomorphism, ?_, ?_, trivial⟩
  · intro m
    rw [frobeniusIterate_left]
    cases m with
    | zero =>
      simp only [Nat.mul_zero, pow_zero, End.one_def, Scheme.iterateFrobenius_zero,
        Category.id_comp]
      rfl
    | succ n =>
      have hf := (D₀.absoluteFrobenius_factorization X₀ (n + 1) (Nat.succ_pos n)).1
      have hc :
          ((End.of (D₀.arithmeticGaloisFrobenius X₀)) ^ (n + 1)) ≫
            ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ (n + 1)) =
          𝟙 (D₀.geometricFiber X₀).left :=
        inv_powers_cancel (D₀.geometricFrobenius X₀) (n + 1)
      simp only [modelEnd, Over.homMk_left]
      change ((End.of (D₀.schemeFrobenius X₀)) ^ (n + 1)) = _
      have heq := congrArg
        (fun f ↦ f ≫ ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ (n + 1))) hf.symm
      rw [Category.assoc, hc, Category.comp_id] at heq
      exact heq
  · intro m
    apply End.asHom_pow_comp_eq_comp_asHom_pow _ m
    let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D₀.k₀ D₀.k
    change D₀.galoisMap X₀.hom σ ≫
      (c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).i =
      (c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).i ≫
        D₀.galoisMap c₀.g σ
    apply pullback.hom_ext
    · simp only [Compactification.baseChange_i_fst, Category.assoc]
      erw [← Category.assoc, (D₀.galoisMap_projections X₀.hom σ).1,
        (D₀.galoisMap_projections c₀.g σ).1, Compactification.baseChange_i_fst]
    · simp only [Compactification.baseChange_i_snd, Category.assoc]
      erw [(D₀.galoisMap_projections X₀.hom σ).2,
        (D₀.galoisMap_projections c₀.g σ).2, ← Category.assoc,
        Compactification.baseChange_i_snd]
  · intro m
    apply End.asHom_pow_comp_eq_comp_asHom_pow _ m
    exact (D₀.galoisMap_projections c₀.g
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D₀.k₀ D₀.k)).2

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
