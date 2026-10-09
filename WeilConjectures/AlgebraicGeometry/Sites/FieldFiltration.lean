/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.PGroup
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.FieldTrace
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# Split sheaves on the small étale site of a field

Let `F` be a field and `N/F` a finite Galois extension. An étale sheaf `X` on `Spec F` is
*split by `N`* (`AlgebraicGeometry.Scheme.IsSplitBy`) if restriction `X(N) → X(E)` is bijective
for every field `E` étale over `F` and every `F`-embedding `N → E`.

If `N/F` has `ℓ`-power degree and `X` is split by `N` with `X(N)` a finite group killed by a
power of `ℓ`, then `X` is an iterated extension of copies of the constant sheaf `ℤ/ℓ`
(`AlgebraicGeometry.Scheme.IsSplitBy.induction`): the `ℓ`-group `Gal(N/F)` has a nonzero fixed
vector in `X(N)`, which descends to a global section of `X` of order `ℓ`, that is, to a
monomorphism `ℤ/ℓ ⟶ X`, and the cokernel is again split by `N`, with smaller group of sections
over `N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {F : Type u} [Field F]

/-- The terminal object `𝟙 : Spec F ⟶ Spec F` of the small étale site of `Spec F`. -/
local notation "𝟙ₑ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of F)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of F)))

variable (N : Type u) [Field N] [Algebra F N] [Algebra.Etale F N]

/-- An étale sheaf `X` on `Spec F` is *split by* the étale field extension `N` if restriction
`X(N) → X(E)` is bijective for every embedding `N → E` into a field `E` étale over `F`. -/
def IsSplitBy (X : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra F E] [Algebra.Etale F E] (β : N →ₐ[F] E),
    Function.Bijective (X.obj.map (etaleSpecMap β).op)

/-- Every field `E` étale over `F` admits a field extension `E'`, étale over `F`, into which
`N` embeds as well. -/
lemma exists_field_etaleSpec_comp (E : Type u) [Field E] [Algebra F E] [Algebra.Etale F E] :
    ∃ (E' : Type u) (_ : Field E') (_ : Algebra F E') (_ : Algebra.Etale F E')
      (_ : etaleSpec F E' ⟶ etaleSpec F E), Nonempty (N →ₐ[F] E') := by
  obtain ⟨x⟩ : Nonempty (etaleBaseChange N (etaleSpec F E)).left := by
    obtain ⟨y⟩ : Nonempty (etaleSpec F E).left := inferInstanceAs (Nonempty (Spec (.of E)))
    obtain ⟨x, -⟩ := surjective_etaleBaseChangeFst (A := N) (etaleSpec F E) y
    exact ⟨x⟩
  obtain ⟨E', _, _, _, ψ, -⟩ := exists_etaleSpec_field_mem _ x
  obtain ⟨β, -⟩ := exists_etaleSpecMap_eq (ψ ≫ etaleBaseChangeSnd N (etaleSpec F E))
  exact ⟨E', _, _, _, ψ ≫ etaleBaseChangeFst N _, ⟨β⟩⟩

variable {N}

/-- A sheaf split by `N` with no sections over `N` is zero. -/
lemma IsSplitBy.isZero {X : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hX : IsSplitBy N X) (h0 : Subsingleton (X.obj.obj (op (etaleSpec F N)))) : IsZero X := by
  have hs (V : (Spec (.of F)).Etale) (s : X.obj.obj (op V)) : s = 0 := by
    refine ext_of_forall_etaleSpec_field X fun E _ _ _ ψ ↦ ?_
    rw [map_zero]
    obtain ⟨E', _, _, _, θ, ⟨β⟩⟩ := exists_field_etaleSpec_comp (F := F) N E
    refine injective_map_of_surjective X θ (surjective_left_of_field θ) ?_
    rw [map_zero]
    obtain ⟨t, ht⟩ := (hX E' β).2 (X.obj.map θ.op (X.obj.map ψ.op s))
    rw [← ht, Subsingleton.elim t 0, map_zero]
  refine (IsZero.iff_id_eq_zero X).2 ?_
  ext V s
  exact (hs _ _).trans (hs _ _).symm

lemma etaleSpecMap_id' : etaleSpecMap (AlgHom.id F N) = 𝟙 (etaleSpec F N) := by
  apply MorphismProperty.Over.Hom.ext
  exact Spec.map_id _

variable (N) in
/-- The action of `Gal(N/F)` on the sections of a sheaf over `Spec N`. -/
noncomputable abbrev galoisAction (X : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    MulAction (N ≃ₐ[F] N) (X.obj.obj (op (etaleSpec F N))) where
  smul σ x := X.obj.map (etaleSpecMap σ.toAlgHom).op x
  one_smul x := by
    change X.obj.map (etaleSpecMap (AlgHom.id F N)).op x = x
    rw [etaleSpecMap_id', op_id, X.obj.map_id, AddCommGrpCat.id_apply]
  mul_smul σ τ x := by
    change X.obj.map (etaleSpecMap (σ.toAlgHom.comp τ.toAlgHom)).op x =
      X.obj.map (etaleSpecMap σ.toAlgHom).op (X.obj.map (etaleSpecMap τ.toAlgHom).op x)
    rw [← etaleSpecMap_comp, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **Fixed vectors.** If `Gal(N/F)` is an `ℓ`-group and the sections of `X` over `N` form a
nontrivial finite group killed by `ℓ ^ a`, there is a Galois-invariant section over `N` of order
`ℓ`. -/
lemma exists_ne_zero_fixed {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hP : IsPGroup ℓ (N ≃ₐ[F] N))
    [Finite (N ≃ₐ[F] N)]
    (X : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})
    [Finite (X.obj.obj (op (etaleSpec F N)))] [Nontrivial (X.obj.obj (op (etaleSpec F N)))]
    {a : ℕ} (ha : ∀ x : X.obj.obj (op (etaleSpec F N)), ℓ ^ a • x = 0) :
    ∃ x : X.obj.obj (op (etaleSpec F N)), x ≠ 0 ∧ ℓ • x = 0 ∧
      ∀ σ : N ≃ₐ[F] N, X.obj.map (etaleSpecMap σ.toAlgHom).op x = x := by
  let := galoisAction N X
  -- `ℓ` divides the order of `X(N)`
  have hdvd : ℓ ∣ Nat.card (X.obj.obj (op (etaleSpec F N))) := by
    obtain ⟨z, hz⟩ := exists_ne (0 : X.obj.obj (op (etaleSpec F N)))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ.out).1 (addOrderOf_dvd_of_nsmul_eq_zero (ha z))
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hz (AddMonoid.addOrderOf_eq_one_iff.1 (by simpa using hj))
    exact (dvd_pow_self ℓ hj0).trans (hj ▸ addOrderOf_dvd_natCard z)
  have hfix := hP.card_modEq_card_fixedPoints (X.obj.obj (op (etaleSpec F N)))
  have hfdvd : ℓ ∣ Nat.card (MulAction.fixedPoints (N ≃ₐ[F] N) (X.obj.obj (op (etaleSpec F N)))) :=
    (Nat.modEq_zero_iff_dvd.1 (hfix.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd)))
  -- a nonzero fixed vector
  have h0 : (0 : X.obj.obj (op (etaleSpec F N))) ∈
      MulAction.fixedPoints (N ≃ₐ[F] N) (X.obj.obj (op (etaleSpec F N))) := fun σ ↦ by
    change X.obj.map (etaleSpecMap σ.toAlgHom).op 0 = 0
    exact map_zero _
  have : Nontrivial (MulAction.fixedPoints (N ≃ₐ[F] N) (X.obj.obj (op (etaleSpec F N)))) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have : Nonempty (MulAction.fixedPoints (N ≃ₐ[F] N) (X.obj.obj (op (etaleSpec F N)))) :=
      ⟨⟨0, h0⟩⟩
    have hpos : 0 < Nat.card (MulAction.fixedPoints (N ≃ₐ[F] N)
        (X.obj.obj (op (etaleSpec F N)))) := Nat.card_pos
    exact lt_of_lt_of_le hℓ.out.one_lt (Nat.le_of_dvd hpos hfdvd)
  obtain ⟨⟨y, hy⟩, hy0⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints (N ≃ₐ[F] N)
    (X.obj.obj (op (etaleSpec F N))))
  have hy0' : y ≠ 0 := fun h ↦ hy0 (Subtype.ext h)
  -- a multiple of order `ℓ`
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ.out).1 (addOrderOf_dvd_of_nsmul_eq_zero (ha y))
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hy0' (AddMonoid.addOrderOf_eq_one_iff.1 (by simpa using hj))
  refine ⟨ℓ ^ (j - 1) • y, ?_, ?_, fun σ ↦ ?_⟩
  · intro h
    have := addOrderOf_le_of_nsmul_eq_zero (pow_pos hℓ.out.pos (j - 1)) h
    rw [hj] at this
    exact absurd this (not_le.2 (Nat.pow_lt_pow_right hℓ.out.one_lt (by omega)))
  · rw [smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hj,
      addOrderOf_nsmul_eq_zero]
  · rw [map_nsmul]
    exact congrArg _ (hy σ)

variable (N) in
/-- The morphism `Spec N ⟶ Spec F` to the terminal object. -/
noncomputable abbrev toTerminal : etaleSpec F N ⟶ 𝟙ₑ :=
  (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of F))).from _

/-- **Galois descent of an invariant section over `Spec N`.** -/
lemma exists_map_toTerminal_eq [IsGalois F N]
    (X : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : X.obj.obj (op (etaleSpec F N)))
    (hx : ∀ σ : N ≃ₐ[F] N, X.obj.map (etaleSpecMap σ.toAlgHom).op x = x) :
    ∃ s : X.obj.obj (op 𝟙ₑ), X.obj.map (toTerminal N).op s = x := by
  let q := etaleBaseChangeSnd N 𝟙ₑ
  have hq : Function.Injective (X.obj.map q.op) := by
    refine injective_map_of_surjective X q ?_
    have : IsIso q.left := inferInstanceAs (IsIso (pullback.snd (𝟙 _) _))
    have h : Surjective q.left := inferInstance
    exact h.surj
  obtain ⟨s, hs⟩ := exists_map_etaleBaseChangeFst_eq X 𝟙ₑ (X.obj.map q.op x) fun σ ↦ by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, etaleBaseChangeMap_snd,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hx]
  refine ⟨s, hq ?_⟩
  rw [← hs, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 3
  exact congrArg Quiver.Hom.op ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of F))).hom_ext _ _)

section Constant

variable (ℓ : ℕ) (X : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The restriction of a global section to an étale `F`-scheme. -/
noncomputable abbrev globalRes (W : (Spec (.of F)).Etale) (s : X.obj.obj (op 𝟙ₑ)) :
    X.obj.obj (op W) :=
  X.obj.map ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
    (Spec (.of F))).from W).op s

lemma map_globalRes {W W' : (Spec (.of F)).Etale} (g : W' ⟶ W) (s : X.obj.obj (op 𝟙ₑ)) :
    X.obj.map g.op (globalRes X W s) = globalRes X W' s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 3
  exact congrArg Quiver.Hom.op ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
    (Spec (.of F))).hom_ext _ _)

/-- The map `a ↦ a • s` from the constant presheaf `ℤ/ℓ` to `X`, for a global section `s` of
`X` killed by `ℓ`. -/
noncomputable def constZModPresheafHom (s : X.obj.obj (op 𝟙ₑ)) (hs : ℓ • s = 0) :
    (Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) ⟶ X.obj where
  app W := AddCommGrpCat.ofHom ((ZMod.lift ℓ ⟨zmultiplesHom _ (globalRes X W.unop s), by
      rw [zmultiplesHom_apply, natCast_zsmul, ← map_nsmul, hs, map_zero]⟩).comp
    AddEquiv.ulift.toAddMonoidHom)
  naturality W W' g := by
    ext a
    obtain ⟨a⟩ := a
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    simp only [Functor.const_obj_obj, Functor.const_obj_map, AddCommGrpCat.hom_comp,
      AddCommGrpCat.hom_id, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom]
    change ZMod.lift ℓ _ (n : ZMod ℓ) = X.obj.map g (ZMod.lift ℓ _ (n : ZMod ℓ))
    rw [ZMod.lift_coe, ZMod.lift_coe, zmultiplesHom_apply, zmultiplesHom_apply, map_zsmul,
      ← map_globalRes X g.unop]
    rfl

/-- The constant presheaf `ℤ/ℓ` on the small étale site of `Spec F`. -/
noncomputable abbrev constZModPresheaf :
    (Spec (.of F)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))

/-- The morphism `ℤ/ℓ ⟶ X` sending `1` to a global section `s` killed by `ℓ`. -/
noncomputable def constZModHom (s : X.obj.obj (op 𝟙ₑ)) (hs : ℓ • s = 0) :
    (Spec (.of F)).constantZMod ℓ ⟶ X :=
  ⟨sheafifyLift _ (constZModPresheafHom ℓ X s hs) X.property⟩

lemma toSheafify_constZModHom (s : X.obj.obj (op 𝟙ₑ)) (hs : ℓ • s = 0) :
    toSheafify _ (constZModPresheaf ℓ) ≫ (constZModHom ℓ X s hs).hom =
      constZModPresheafHom ℓ X s hs :=
  toSheafify_sheafifyLift _ _ _

/-- A section of the constant sheaf `ℤ/ℓ` over the spectrum of a field is constant. -/
lemma exists_toSheafify_eq (E : Type u) [Field E] [Algebra F E] [Algebra.Etale F E]
    (w : ((Spec (.of F)).constantZMod ℓ).obj.obj (op (etaleSpec F E))) :
    ∃ a, (toSheafify _ (constZModPresheaf ℓ)).app (op (etaleSpec F E)) a = w := by
  have hmem := Presheaf.imageSieve_mem (Spec (.of F)).smallEtaleTopology
    (toSheafify _ (constZModPresheaf ℓ)) w
  obtain ⟨E', _, _, _, θ, ⟨a, ha⟩, -⟩ :=
    exists_etaleSpec_field_mem_of_mem hmem
      (show (etaleSpec F E).left from ⟨⊥, Ideal.isPrime_bot⟩)
  refine ⟨a, injective_map_of_surjective _ θ (surjective_left_of_field θ) ?_⟩
  rw [← ha]
  exact (NatTrans.naturality_apply (toSheafify _ (constZModPresheaf ℓ)) θ.op a).symm

variable {ℓ X} in
lemma constZModHom_app_toSheafify {s : X.obj.obj (op 𝟙ₑ)} (hs : ℓ • s = 0)
    (W : (Spec (.of F)).Etale) (n : ℤ) :
    (constZModHom ℓ X s hs).hom.app (op W)
      ((toSheafify _ (constZModPresheaf ℓ)).app (op W) (⟨(n : ZMod ℓ)⟩ : ULift (ZMod ℓ))) =
        n • globalRes X W s := by
  change ((toSheafify _ (constZModPresheaf ℓ) ≫ (constZModHom ℓ X s hs).hom).app (op W))
    (⟨(n : ZMod ℓ)⟩ : ULift (ZMod ℓ)) = _
  rw [toSheafify_constZModHom]
  change (ZMod.lift ℓ ⟨zmultiplesHom _ (globalRes X W s), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← map_nsmul, hs, map_zero]⟩) (n : ZMod ℓ) = _
  rw [ZMod.lift_coe, zmultiplesHom_apply]

lemma injective_globalRes (E : Type u) [Field E] [Algebra F E] [Algebra.Etale F E] :
    Function.Injective (globalRes X (etaleSpec F E)) :=
  injective_map_of_surjective X _ fun y ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext
    ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime (y : PrimeSpectrum F).asIdeal).symm)⟩

variable {ℓ X} in
lemma constZModHom_app_eq_zero [hℓ : Fact ℓ.Prime] {s : X.obj.obj (op 𝟙ₑ)} (hs : ℓ • s = 0)
    (hs0 : s ≠ 0) {V : (Spec (.of F)).Etale} (w : ((Spec (.of F)).constantZMod ℓ).obj.obj (op V))
    (hw : (constZModHom ℓ X s hs).hom.app (op V) w = 0) : w = 0 := by
  refine ext_of_forall_etaleSpec_field _ fun E _ _ _ χ ↦ ?_
  rw [map_zero]
  obtain ⟨⟨a⟩, ha⟩ := exists_toSheafify_eq ℓ E (((Spec (.of F)).constantZMod ℓ).obj.map χ.op w)
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
  have h1 : n • globalRes X (etaleSpec F E) s = 0 := by
    rw [← constZModHom_app_toSheafify hs, ha, NatTrans.naturality_apply, hw, map_zero]
  have hne : globalRes X (etaleSpec F E) s ≠ 0 := fun h ↦
    hs0 (injective_globalRes X E (h.trans (map_zero _).symm))
  have hord : addOrderOf (globalRes X (etaleSpec F E) s) = ℓ :=
    addOrderOf_eq_prime (by rw [← map_nsmul, hs, map_zero]) hne
  have hn : (n : ZMod ℓ) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.2 h1
  rw [← ha, hn]
  exact map_zero ((toSheafify _ (constZModPresheaf ℓ)).app (op (etaleSpec F E))).hom

variable {ℓ X} in
/-- The morphism `ℤ/ℓ ⟶ X` defined by a nonzero global section of order `ℓ` is a
monomorphism. -/
lemma mono_constZModHom [Fact ℓ.Prime] {s : X.obj.obj (op 𝟙ₑ)} (hs : ℓ • s = 0)
    (hs0 : s ≠ 0) : Mono (constZModHom ℓ X s hs) := by
  have : Mono (constZModHom ℓ X s hs).hom := by
    have (V : (Spec (.of F)).Etaleᵒᵖ) : Mono ((constZModHom ℓ X s hs).hom.app V) := by
      refine (AddCommGrpCat.mono_iff_injective _).2 ?_
      rw [injective_iff_map_eq_zero]
      exact fun w hw ↦ constZModHom_app_eq_zero hs hs0 w hw
    exact NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

end Constant

end AlgebraicGeometry.Scheme
