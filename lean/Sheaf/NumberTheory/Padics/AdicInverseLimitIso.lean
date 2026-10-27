module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Compatible isomorphisms of adic quotients

Source: literature/stacks-project/algebra.tex, Tag 00M9 (section-completion),
compatible finite-level maps and the inverse-limit description of completion
(blueprint: lem-trf-adic-inverse-limit-iso).
-/

@[expose] public section

universe u v


private theorem adicQuotientZero_subsingleton (R : Type*) [CommRing R] (K : Ideal R) :
    Subsingleton (R ⧸ K ^ 0) := by
  rw [pow_zero, Ideal.one_eq_top]
  infer_instance

private theorem factorPow_eval (R : Type*) [CommRing R] (K : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion K R) :
    Ideal.Quotient.factorPow K hmn (AdicCompletion.evalₐ K n x) =
      AdicCompletion.evalₐ K m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective K R x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk K hmn s

/-- Compatible isomorphisms of positive adic quotients induce a unique isomorphism of
adic completions.  This is the inverse-limit construction from Stacks Project,
Tag 00M9 (section-completion):

1. Using [def-weil-pbc-adic-completion], regard both completions as compatible
   tuples.  Define the map coordinatewise by `e n`; compatibility with the
   quotient transitions makes the result a tuple, and componentwise operations
   make it a ring homomorphism with the displayed projection identities.
2. The inverse quotient isomorphisms satisfy the reversed transition identities,
   so they define the inverse compatible-tuple map.  Coordinatewise cancellation
   gives both composites as identities, hence a ring isomorphism.
3. Any map with the same projection identities has equal coordinates to the
   constructed map, so equality of tuples gives uniqueness even among maps of
   sets.

(blueprint: lem-trf-adic-inverse-limit-iso)
-/
theorem adicCompletionRingEquivOfCompatible
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B)
    (e : ∀ n : ℕ, 0 < n → (A ⧸ I ^ n) ≃+* (B ⧸ J ^ n))
    (he : ∀ {m n : ℕ} (hmn : m ≤ n) (hm : 0 < m) (hn : 0 < n),
      (Ideal.Quotient.factorPow J hmn).comp (e n hn).toRingHom =
        (e m hm).toRingHom.comp (Ideal.Quotient.factorPow I hmn)) :
    ∃ E : AdicCompletion I A ≃+* AdicCompletion J B,
      (∀ (n : ℕ) (hn : 0 < n) (x : AdicCompletion I A),
        AdicCompletion.evalₐ J n (E x) =
          e n hn (AdicCompletion.evalₐ I n x)) ∧
      (∀ F : AdicCompletion I A → AdicCompletion J B,
        (∀ (n : ℕ) (hn : 0 < n) (x : AdicCompletion I A),
          AdicCompletion.evalₐ J n (F x) =
            e n hn (AdicCompletion.evalₐ I n x)) →
        F = E.toFun) := by
  let e₀ : (A ⧸ I ^ 0) ≃+* (B ⧸ J ^ 0) := by
    letI := adicQuotientZero_subsingleton A I
    letI := adicQuotientZero_subsingleton B J
    letI : Unique (A ⧸ I ^ 0) := { default := 0, uniq := fun _ ↦ Subsingleton.elim _ _ }
    letI : Unique (B ⧸ J ^ 0) := { default := 0, uniq := fun _ ↦ Subsingleton.elim _ _ }
    exact RingEquiv.ofUnique
  let q (n : ℕ) : (A ⧸ I ^ n) ≃+* (B ⧸ J ^ n) :=
    match n with
    | 0 => e₀
    | n + 1 => e (n + 1) (Nat.succ_pos n)
  have htrans {m n : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n) :
      Ideal.Quotient.factorPow J hmn (q n x) =
        q m (Ideal.Quotient.factorPow I hmn x) := by
    cases m with
    | zero => exact (adicQuotientZero_subsingleton B J).elim _ _
    | succ m =>
      cases n with
      | zero => exact False.elim (Nat.not_succ_le_zero m hmn)
      | succ n => exact DFunLike.congr_fun (he hmn (Nat.succ_pos m) (Nat.succ_pos n)) x
  let f (n : ℕ) := (q n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom
  have hf {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow J hmn).comp (f n) = f m := by
    ext x
    exact (htrans hmn _).trans (congrArg (q m) (factorPow_eval A I hmn x))
  let g (n : ℕ) := (q n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom
  have hg {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow I hmn).comp (g n) = g m := by
    ext x
    change Ideal.Quotient.factorPow I hmn
      ((q n).symm (AdicCompletion.evalₐ J n x)) =
        (q m).symm (AdicCompletion.evalₐ J m x)
    apply (q m).injective
    rw [← htrans hmn, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact factorPow_eval B J hmn x
  let F := AdicCompletion.liftRingHom J f hf
  let G := AdicCompletion.liftRingHom I g hg
  have hF (n : ℕ) (x : AdicCompletion I A) :
      AdicCompletion.evalₐ J n (F x) = q n (AdicCompletion.evalₐ I n x) :=
    AdicCompletion.evalₐ_liftRingHom J f hf n x
  have hG (n : ℕ) (x : AdicCompletion J B) :
      AdicCompletion.evalₐ I n (G x) = (q n).symm (AdicCompletion.evalₐ J n x) :=
    AdicCompletion.evalₐ_liftRingHom I g hg n x
  let E : AdicCompletion I A ≃+* AdicCompletion J B :=
    { F with
      invFun := G
      left_inv := fun x ↦ AdicCompletion.ext_evalₐ (fun n ↦ by
        change AdicCompletion.evalₐ I n (G (F x)) = AdicCompletion.evalₐ I n x
        rw [hG, hF, RingEquiv.symm_apply_apply])
      right_inv := fun x ↦ AdicCompletion.ext_evalₐ (fun n ↦ by
        change AdicCompletion.evalₐ J n (F (G x)) = AdicCompletion.evalₐ J n x
        rw [hF, hG, RingEquiv.apply_symm_apply]) }
  have hE (n : ℕ) (hn : 0 < n) (x : AdicCompletion I A) :
      AdicCompletion.evalₐ J n (E x) = e n hn (AdicCompletion.evalₐ I n x) := by
    cases n with
    | zero => exact False.elim (Nat.lt_irrefl 0 hn)
    | succ n => exact hF (n + 1) x
  refine ⟨E, hE, ?_⟩
  intro H hH
  funext x
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero => exact (adicQuotientZero_subsingleton B J).elim _ _
  | succ n => exact (hH (n + 1) (Nat.succ_pos n) x).trans (hE _ (Nat.succ_pos n) x).symm

end
