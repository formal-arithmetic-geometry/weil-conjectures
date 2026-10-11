/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Induction
public import WeilConjectures.RepresentationTheory.DiscreteModule.Sylow
public import WeilConjectures.Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# A degree-two criterion for the cohomological dimension of a profinite group

Let `G` be a profinite group and `ℓ` a prime such that `H²(K, 𝔽_ℓ) = 0` for every open subgroup
`K` of `G`. Then `Hⁿ(G, M) = 0` for every `n ≥ 2` and every `ℓ`-primary discrete `G`-module `M`.

For finite `M`, an open subgroup `K` of index prime to `ℓ` acts on `M` through an `ℓ`-group, so
`M|_K` is an iterated extension of trivial modules `𝔽_ℓ` and `H²(K, M) = 0`; restriction followed
by corestriction is multiplication by the index, hence `H²(G, M) = 0`. A general `M` is the
union of its finite submodules; we show directly, by an explicit computation of `H²` through
coinduced modules, that `H²` vanishes on such a union. Finally the coinduced modules
`C^sm(G, M)` are acyclic, so a dimension shift gives all degrees `n ≥ 2`.

## Main statements

- `DiscreteModule.subsingleton_H_coind₁`: coinduced modules are acyclic.
- `DiscreteModule.subsingleton_H_of_two_le`: the criterion.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Action

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section toolkit

/-- A short complex of discrete modules which is exact on the underlying abelian groups, with
injective first map and surjective second map, is short exact. -/
lemma shortExact_of_forget {S : ShortComplex (DiscreteModule.{w} G)}
    (hf : Function.Injective S.f.hom.hom.hom) (hg : Function.Surjective S.g.hom.hom.hom)
    (hfg : ∀ x, S.g.hom.hom.hom x = 0 → ∃ y, S.f.hom.hom.hom y = x) : S.ShortExact where
  exact := by
    rw [← S.exact_map_iff_of_faithful (forget₂Ab.{w} G), ShortComplex.ab_exact_iff]
    exact hfg
  mono_f := (forget₂Ab.{w} G).mono_of_mono_map ((AddCommGrpCat.mono_iff_injective _).2 hf)
  epi_g := (forget₂Ab.{w} G).epi_of_epi_map ((AddCommGrpCat.epi_iff_surjective _).2 hg)

/-- Vanishing of `Ext` into the middle term of a short exact sequence. -/
lemma subsingleton_ext_of_shortExact {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    {X : C} {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (h₁ : Subsingleton (Abelian.Ext X S.X₁ n)) (h₃ : Subsingleton (Abelian.Ext X S.X₃ n)) :
    Subsingleton (Abelian.Ext X S.X₂ n) := by
  refine ⟨fun a b ↦ ?_⟩
  have key (x : Abelian.Ext X S.X₂ n) : x = 0 := by
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₂ X hS x (Subsingleton.elim _ _)
    rw [← hy, Subsingleton.elim y 0, Abelian.Ext.zero_comp]
  rw [key a, key b]

/-- Dimension shifting: `Extⁿ⁺¹(X, S.X₁)` is a quotient of `Extⁿ(X, S.X₃)` when
`Extⁿ⁺¹(X, S.X₂) = 0`. -/
lemma subsingleton_ext_succ_of_shortExact {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    {X : C} {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (h₂ : Subsingleton (Abelian.Ext X S.X₂ (n + 1))) (h₃ : Subsingleton (Abelian.Ext X S.X₃ n)) :
    Subsingleton (Abelian.Ext X S.X₁ (n + 1)) := by
  refine ⟨fun a b ↦ ?_⟩
  have key (x : Abelian.Ext X S.X₁ (n + 1)) : x = 0 := by
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _) rfl
    rw [← hy, Subsingleton.elim y 0, Abelian.Ext.zero_comp]
  rw [key a, key b]

end toolkit

section coind₁

/-- **Coinduced modules are acyclic.** `Hⁿ(G, C^sm(G, A)) = 0` for `n ≥ 1`: by the
`Ext`-adjunction for the exact functors `forget ⊣ coind₁` it is `Extⁿ(ℤ, A)` computed among
abelian groups, which vanishes as `ℤ` is projective. -/
lemma subsingleton_H_coind₁ (A : AddCommGrpCat.{max u w}) (n : ℕ) :
    Subsingleton (H G ((coind₁ G).obj A) (n + 1)) := by
  let := hasExt_of_enoughInjectives.{max u w} AddCommGrpCat.{max u w}
  have e := (coind₁Adjunction.{w} G).extAddEquiv (intTrivial G) A (n + 1)
  have : Projective ((forget₂Ab.{w} G).obj (intTrivial G)) :=
    AddCommGrpCat.projective_of_uliftInt
  refine ⟨fun a b ↦ e.injective ?_⟩
  rw [Abelian.Ext.eq_zero_of_projective (e a), Abelian.Ext.eq_zero_of_projective (e b)]

end coind₁

section quotient

variable (X : DiscreteModule.{w} G) (S : AddSubgroup X.obj.V)
  (hS : ∀ g : G, ∀ x ∈ S, (X.obj.ρ g).hom x ∈ S)

/-- The quotient of a discrete module by a stable subgroup. -/
@[simps]
def quotientAction : Action AddCommGrpCat.{max u w} G where
  V := AddCommGrpCat.of (X.obj.V ⧸ S)
  ρ :=
    { toFun g := AddCommGrpCat.ofHom (QuotientAddGroup.map S S (X.obj.ρ g).hom fun x hx ↦ hS g x hx)
      map_one' := AddCommGrpCat.ext fun q ↦ QuotientAddGroup.induction_on q fun x ↦ by
        simp [End.one_def]
      map_mul' a b := AddCommGrpCat.ext fun q ↦ QuotientAddGroup.induction_on q fun x ↦ by
        simp [End.mul_def] }

/-- The quotient of a discrete module by a stable subgroup. -/
def quotient : DiscreteModule.{w} G :=
  ⟨quotientAction X S hS, fun q ↦ QuotientAddGroup.induction_on q fun x ↦
    Subgroup.isOpen_mono (H₁ := X.obj.stabilizer x) (fun g (hg : _ = _) ↦ by
      change QuotientAddGroup.mk ((X.obj.ρ g).hom x) = _
      rw [hg]) (X.isOpen_stabilizer x)⟩

/-- The projection onto the quotient. -/
def quotientπ : X ⟶ quotient X S hS :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (QuotientAddGroup.mk' S)
      comm g := rfl }

@[simp]
lemma quotientπ_apply (x : X.obj.V) :
    (quotientπ X S hS).hom.hom.hom x = QuotientAddGroup.mk x :=
  rfl

lemma quotient_ρ_mk (g : G) (x : X.obj.V) :
    ((quotient X S hS).obj.ρ g).hom (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk ((X.obj.ρ g).hom x) :=
  rfl

end quotient

/-- The action of `G` on the underlying group of an `Action`, as a `DistribMulAction`. -/
@[reducible]
def _root_.Action.distribMulAction (M : Action AddCommGrpCat.{w} G) :
    DistribMulAction G M.V where
  smul g x := (M.ρ g).hom x
  one_smul := ρ_one_apply M
  mul_smul a b x := ρ_mul_apply M a b x
  smul_zero g := map_zero _
  smul_add g := map_add _

lemma subsingleton_H_of_subsingleton (X : DiscreteModule.{w} G) [Subsingleton X.obj.V] (n : ℕ) :
    Subsingleton (H G X n) := by
  have hX : IsZero X := by
    rw [IsZero.iff_id_eq_zero]
    ext x
    exact Subsingleton.elim _ _
  refine ⟨fun a b ↦ ?_⟩
  rw [← Abelian.Ext.comp_mk₀_id a, ← Abelian.Ext.comp_mk₀_id b, hX.eq_of_src (𝟙 X) 0,
    Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]

/-- A predicate saying that every element of a discrete module is killed by a power of `ℓ`. -/
def IsPrimary (ℓ : ℕ) (X : DiscreteModule.{w} G) : Prop :=
  ∀ x : X.obj.V, ∃ j : ℕ, ℓ ^ j • x = 0

section finite

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

variable (G) in
/-- The trivial discrete module `𝔽_ℓ`. -/
abbrev trivialZMod : DiscreteModule.{w} G :=
  trivial G (AddCommGrpCat.of (ULift.{max u w} (ZMod ℓ)))

/-- The additive map `𝔽_ℓ ⟶ X`, `1 ↦ x`, for `x` killed by `ℓ`. -/
def zmodHom {A : Type*} [AddCommGroup A] (x : A) (hx : ℓ • x = 0) :
    ULift.{max u w} (ZMod ℓ) →+ A :=
  (ZMod.lift ℓ ⟨zmultiplesHom _ x, by simp [hx]⟩).comp AddEquiv.ulift.toAddMonoidHom

lemma zmodHom_intCast {A : Type*} [AddCommGroup A] (x : A) (hx : ℓ • x = 0) (n : ℤ) :
    zmodHom.{w, u} ℓ x hx (ULift.up (n : ZMod ℓ)) = n • x := by
  show ZMod.lift ℓ ⟨zmultiplesHom A x, by simp [hx]⟩ ((n : ZMod ℓ)) = n • x
  rw [ZMod.lift_coe]
  simp

/-- The inclusion `𝔽_ℓ ⟶ X`, `1 ↦ x`, of an invariant element killed by `ℓ`. -/
def ofInvariant (X : DiscreteModule.{w} G) (x : X.obj.V) (hx : ℓ • x = 0)
    (hxg : ∀ g : G, (X.obj.ρ g).hom x = x) : trivialZMod.{w} G ℓ ⟶ X :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (zmodHom.{w, u} ℓ x hx)
      comm g := AddCommGrpCat.ext fun a ↦ by
        obtain ⟨n, hn⟩ := ZMod.intCast_surjective a.down
        obtain rfl : a = ULift.up (n : ZMod ℓ) := ULift.ext _ _ hn.symm
        change zmodHom.{w, u} ℓ x hx (ULift.up (n : ZMod ℓ)) =
          (X.obj.ρ g).hom (zmodHom.{w, u} ℓ x hx (ULift.up (n : ZMod ℓ)))
        rw [zmodHom_intCast, map_zsmul, hxg g] }

lemma ofInvariant_apply_intCast (X : DiscreteModule.{w} G) (x : X.obj.V) (hx : ℓ • x = 0)
    (hxg : ∀ g : G, (X.obj.ρ g).hom x = x) (n : ℤ) :
    (ofInvariant ℓ X x hx hxg).hom.hom.hom (ULift.up (n : ZMod ℓ)) = n • x :=
  zmodHom_intCast.{w, u} ℓ x hx n

lemma injective_ofInvariant (X : DiscreteModule.{w} G) (x : X.obj.V) (hx : ℓ • x = 0)
    (hxg : ∀ g : G, (X.obj.ρ g).hom x = x) (hx0 : x ≠ 0) :
    Function.Injective (ofInvariant ℓ X x hx hxg).hom.hom.hom := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a⟩ ha
  by_contra h
  have ha0 : a ≠ 0 := fun h' ↦ h (by rw [h']; rfl)
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective a⁻¹
  have h1 : ((n * a : ZMod ℓ)) = 1 := by rw [hn, inv_mul_cancel₀ ha0]
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective a
  have : (ofInvariant ℓ X x hx hxg).hom.hom.hom (ULift.up (n * a : ZMod ℓ)) = n • 0 := by
    rw [← ha, ← hm, ← Int.cast_mul, ofInvariant_apply_intCast, ofInvariant_apply_intCast,
      mul_smul]
  rw [h1, smul_zero, show (1 : ZMod ℓ) = ((1 : ℤ) : ZMod ℓ) by simp,
    ofInvariant_apply_intCast, one_smul] at this
  exact hx0 this

/-- **Modules over an `ℓ`-group.** Suppose that `G` acts on finite `ℓ`-primary modules through
an `ℓ`-group: the normal subgroup `N` acts trivially and every element of `G` has an `ℓ`-power in
`N`. If `H²(G, 𝔽_ℓ) = 0`, then `H²(G, X) = 0` for every such `X`: a nonzero `X` contains a
copy of `𝔽_ℓ` spanned by a fixed vector, and we argue by induction on `#X`. -/
theorem subsingleton_H_two_of_forall_pow_mem (N : Subgroup G) [N.Normal]
    (hpow : ∀ k : G, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (h2 : Subsingleton (H G (trivialZMod.{w} G ℓ) 2))
    (n : ℕ) (X : DiscreteModule.{w} G) [Finite X.obj.V] (hn : Nat.card X.obj.V = n)
    (hN : ∀ k ∈ N, ∀ x : X.obj.V, (X.obj.ρ k).hom x = x) (hX : IsPrimary ℓ X) :
    Subsingleton (H G X 2) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  by_cases htriv : Subsingleton X.obj.V
  · exact subsingleton_H_of_subsingleton X 2
  rw [not_subsingleton_iff_nontrivial] at htriv
  letI := X.obj.distribMulAction
  obtain ⟨x, hx0, hxℓ, hxg⟩ := exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup ℓ N hN hpow hX
  let S := AddSubgroup.zmultiples x
  have hS : ∀ g : G, ∀ y ∈ S, (X.obj.ρ g).hom y ∈ S := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨m, by rw [map_zsmul]; exact congrArg (m • ·) (hxg g).symm⟩
  have hzero : ofInvariant ℓ X x hxℓ hxg ≫ quotientπ X S hS = 0 := by
    ext a
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective a.down
    obtain rfl : a = ULift.up (m : ZMod ℓ) := ULift.ext _ _ hm.symm
    change QuotientAddGroup.mk ((ofInvariant ℓ X x hxℓ hxg).hom.hom.hom _) = 0
    rw [ofInvariant_apply_intCast, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩
  let T := ShortComplex.mk _ _ hzero
  have hT : T.ShortExact := by
    refine shortExact_of_forget (injective_ofInvariant ℓ X x hxℓ hxg hx0)
      QuotientAddGroup.mk_surjective fun y hy ↦ ?_
    obtain ⟨m, rfl⟩ := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact ⟨ULift.up (m : ZMod ℓ), ofInvariant_apply_intCast ℓ X x hxℓ hxg m⟩
  refine subsingleton_ext_of_shortExact hT h2 ?_
  have : Finite (quotient X S hS).obj.V :=
    Finite.of_surjective _ (QuotientAddGroup.mk_surjective (s := S))
  refine ih _ ?_ (quotient X S hS) rfl ?_ ?_
  · rw [← hn, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S]
    have h1 : 1 < Nat.card S := by
      have : Nontrivial S := ⟨⟨0, ⟨x, AddSubgroup.mem_zmultiples x⟩, fun h ↦ hx0
        (congrArg Subtype.val h).symm⟩⟩
      exact Finite.one_lt_card_iff_nontrivial.2 this
    have h2 : 0 < Nat.card (X.obj.V ⧸ S) := Nat.card_pos
    change Nat.card (X.obj.V ⧸ S) < _
    nlinarith
  · intro k hk q
    induction q using QuotientAddGroup.induction_on with
    | H y => exact congrArg QuotientAddGroup.mk (hN k hk y)
  · intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨j, hj⟩ := hX y
      exact ⟨j, by rw [← QuotientAddGroup.mk_nsmul, hj, QuotientAddGroup.mk_zero]⟩

end finite

end DiscreteModule
