/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
import Sheaf.DeligneLaumon.GeometricMultiplicityOne
import WeilConjectures.WeilSheaf.GeometricConstituent
import WeilConjectures.WeilSheaf.LisseFiltration
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # A cyclic geometric decomposition with a power return

Source: the geometric-socle and multiplicity-eigenline argument in
`sk-i-dl-general-real`, first step.
(blueprint: lem-zl-geometric-power-orbit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

section Helpers

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

-- A multiplicity-free decomposition turns the return matrix into a monomial matrix.
private theorem monomial_return (V : WeilSheaf k₀ l X) {n : ℕ}
    (U : Fin n → AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hU : ∀ a, IsIrreducibleAdicLocalSystem (U a))
    (hne : ∀ a b, Nonempty (U a ≅ U b) → a = b) (s : V.obj.carrier ≅ ⨁ U) :
    ∃ (σ : Equiv.Perm (Fin n))
      (e : ∀ a, (frobeniusPullback k₀ l X).obj (U a) ≅ U (σ a)),
      ∀ a, (e a).hom ≫ biproduct.ι U (σ a) ≫ s.inv =
        (frobeniusPullback k₀ l X).map (biproduct.ι U a ≫ s.inv) ≫ V.obj.str.hom := by
  classical
  let F := frobeniusPullback k₀ l X
  let f (a : Fin n) : F.obj (U a) ⟶ ⨁ U :=
    F.map (biproduct.ι U a ≫ s.inv) ≫ V.obj.str.hom ≫ s.hom
  have hF (a : Fin n) := isIrreducibleAdicLocalSystem_frobeniusPullback_obj (hU a)
  have hf (a : Fin n) : ∃ b, f a ≫ biproduct.π U b ≠ 0 := by
    by_contra! h
    have hz : f a = 0 := biproduct.hom_ext _ _ (fun b ↦ by simpa using h b)
    have : Mono (f a) := by dsimp [f]; infer_instance
    exact (hF a).2.1 (IsZero.of_mono_eq_zero (f a) hz)
  choose t ht using hf
  have hi (a : Fin n) : IsIso (f a ≫ biproduct.π U (t a)) :=
    (hF a).isIso_of_ne_zero (hU (t a)) _ (ht a)
  let e (a : Fin n) : F.obj (U a) ≅ U (t a) := asIso (f a ≫ biproduct.π U (t a))
  have hzero (a b : Fin n) (hb : b ≠ t a) : f a ≫ biproduct.π U b = 0 := by
    by_contra hz
    have : IsIso (f a ≫ biproduct.π U b) := (hF a).isIso_of_ne_zero (hU b) _ hz
    exact hb (hne b (t a) ⟨(asIso (f a ≫ biproduct.π U b)).symm ≪≫ e a⟩)
  have hfac (a : Fin n) : f a = (e a).hom ≫ biproduct.ι U (t a) := by
    apply biproduct.hom_ext
    intro b
    by_cases hb : t a = b
    · subst b; simp [e]
    · simp [hb, hzero a b (Ne.symm hb)]
  have htinj : Function.Injective t := by
    intro a b hab
    exact hne a b ⟨F.preimageIso (e a ≪≫ eqToIso (congrArg U hab) ≪≫ (e b).symm)⟩
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective t
    ⟨htinj, (Finite.injective_iff_surjective).1 htinj⟩
  refine ⟨σ, e, fun a ↦ ?_⟩
  change (e a).hom ≫ biproduct.ι U (t a) ≫ s.inv = _
  calc
    (e a).hom ≫ biproduct.ι U (t a) ≫ s.inv = f a ≫ s.inv := by
      rw [hfac a, Category.assoc]
    _ = _ := by simp [f, F]

-- An orbit projector is a Weil idempotent. Its image is lisse; simplicity
-- forces every nonzero orbit projector to be the identity.
private theorem transitive_return
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    {n : ℕ} (U : Fin n → AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hU : ∀ a, IsIrreducibleAdicLocalSystem (U a)) (s : V.obj.carrier ≅ ⨁ U)
    (σ : Equiv.Perm (Fin n))
    (e : ∀ a, (frobeniusPullback k₀ l X).obj (U a) ≅ U (σ a))
    (he : ∀ a, (e a).hom ≫ biproduct.ι U (σ a) ≫ s.inv =
      (frobeniusPullback k₀ l X).map (biproduct.ι U a ≫ s.inv) ≫ V.obj.str.hom) :
    ∀ a b, σ.SameCycle a b := by
  classical
  let F := frobeniusPullback k₀ l X
  let i (b : Fin n) := biproduct.ι U b ≫ s.inv
  have ext {Z : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
      {f g : V.obj.carrier ⟶ Z} (h : ∀ b, i b ≫ f = i b ≫ g) : f = g := by
    apply (cancel_epi s.inv).1
    exact biproduct.hom_ext' _ _ h
  intro a b
  let p : V.obj.carrier ⟶ V.obj.carrier :=
    s.hom ≫ biproduct.desc (fun c ↦ if σ.SameCycle a c then i c else 0)
  have hip (c : Fin n) : i c ≫ p = if σ.SameCycle a c then i c else 0 := by
    simp [i, p]
  have hpp : p ≫ p = p := by
    apply ext
    intro c
    rw [← Category.assoc, hip]
    split_ifs with hc <;> simp [hip, hc]
  have hp : F.map p ≫ V.obj.str.hom = V.obj.str.hom ≫ p := by
    apply (cancel_epi (F.map s.inv)).1
    apply (cancel_epi (F.mapBiproduct U).inv).1
    rw [Functor.mapBiproduct_inv]
    apply biproduct.hom_ext'
    intro c
    simp only [biproduct.ι_desc_assoc, ← F.map_comp_assoc]
    change F.map (i c ≫ p) ≫ V.obj.str.hom =
      F.map (i c) ≫ V.obj.str.hom ≫ p
    have hec : (e c).hom ≫ i (σ c) = F.map (i c) ≫ V.obj.str.hom := he c
    rw [hip, ← reassoc_of% hec, hip]
    have hcycle := Equiv.Perm.sameCycle_apply_right (f := σ) (x := a) (y := c)
    by_cases hc : σ.SameCycle a c
    · rw [if_pos hc, if_pos (hcycle.2 hc)]
      exact (he c).symm
    · rw [if_neg hc, if_neg (fun h ↦ hc (hcycle.1 h)), F.map_zero, zero_comp, comp_zero]
  let q : V ⟶ V := ObjectProperty.homMk (ObjectProperty.homMk ⟨p, hp⟩)
  let D := carrierFunctor k₀ l X
  have hDi : D.obj (image q) ≅ image p := (PreservesImage.iso D q).symm
  have him : (image q).IsLisse := (hV.1.image hV.1 p).of_iso hDi.symm
  have hq0 : ¬ IsZero (image q) := by
    intro hz
    have hz' : IsZero (image p) := (D.map_isZero hz).of_iso hDi.symm
    have hp0 : p = 0 := by
      rw [← image.fac p]
      rw [hz'.eq_of_tgt (factorThruImage p) 0, zero_comp]
    have hi0 : i a = 0 := by
      have := hip a
      rw [hp0, comp_zero, if_pos (Equiv.Perm.SameCycle.refl σ a)] at this
      exact this.symm
    have : Mono (i a) := by dsimp [i]; infer_instance
    exact (hU a).2.1 (IsZero.of_mono_eq_zero (i a) hi0)
  have hiiso : IsIso (image.ι q) :=
    (hV.2.2 _ (image.ι q) inferInstance him).resolve_left hq0
  have hqepi : Epi q := by
    rw [← image.fac q]
    infer_instance
  have hqidem : q ≫ q = q := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact Algebra.Hom.ext hpp
  have hqid : q = 𝟙 V := by
    apply (cancel_epi q).1
    simpa using hqidem
  have hpid : p = 𝟙 V.obj.carrier := congrArg (fun f : V ⟶ V ↦ f.hom.hom.f) hqid
  by_contra hab
  have hib0 : i b = 0 := by simpa [hpid, hab] using hip b
  have : Mono (i b) := by dsimp [i]; infer_instance
  exact (hU b).2.1 (IsZero.of_mono_eq_zero (i b) hib0)

-- The geometric power functors include the scheme-pushforward coherence isomorphisms.
-- Iterate the embedded one-step transports with exactly those isomorphisms.
omit [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] in
private theorem iterated_return (V : WeilSheaf k₀ l X) {n : ℕ}
    (U : Fin n → AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (i : ∀ a, U a ⟶ V.obj.carrier) (σ : Equiv.Perm (Fin n))
    (e : ∀ a, (frobeniusPullback k₀ l X).obj (U a) ≅ U (σ a))
    (he : ∀ a, (e a).hom ≫ i (σ a) =
      (frobeniusPullback k₀ l X).map (i a) ≫ V.obj.str.hom) (j : ℕ) :
    ∀ a, ∃ g : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj (U a) ≅
      U ((σ ^ j) a), g.hom ≫ i ((σ ^ j) a) =
        (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).map (i a) ≫
          (V.obj.frobeniusPowIso j).hom := by
  induction j with
  | zero =>
    intro a
    refine ⟨(adicLowerStarCongr l (by rw [pow_zero]; rfl)).app (U a) ≪≫
      (adicLowerStarId l _).app (U a), ?_⟩
    simp only [ProEtaleWeilSheaf.frobeniusPowIso,
      Iso.trans_hom, Iso.app_hom, Category.assoc]
    rw [NatTrans.naturality_assoc, NatTrans.naturality]
    rfl
  | succ j ih =>
    intro a
    obtain ⟨g, hg⟩ := ih a
    let τ : ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X (j + 1) ≅
        ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j ⋙ frobeniusPullback k₀ l X :=
      adicLowerStarCongr l (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]) ≪≫
        (adicLowerStarComp l _ _).symm
    have hp : (σ ^ (j + 1)) a = σ ((σ ^ j) a) := by
      rw [pow_succ']; rfl
    rw [hp]
    refine ⟨τ.app (U a) ≪≫ (frobeniusPullback k₀ l X).mapIso g ≪≫
      e ((σ ^ j) a), ?_⟩
    have hφ : (V.obj.frobeniusPowIso (j + 1)).hom =
        (τ.app V.obj.carrier).hom ≫
          (frobeniusPullback k₀ l X).map (V.obj.frobeniusPowIso j).hom ≫
            V.obj.str.hom := rfl
    rw [hφ]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [he, ← Functor.map_comp_assoc, hg, Functor.map_comp]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ f ≫
        (frobeniusPullback k₀ l X).map (V.obj.frobeniusPowIso j).hom ≫ V.obj.str.hom)
        (τ.hom.naturality (i a)).symm

end Helpers

/-- A simple Weil object with semisimple carrier splits into geometric simple
objects with a common power return; the original return acts transitively on
these embedded summands.

Source: blueprint `sec-deligne-laumon-general/sk-i-dl-general-real/_section.md`,
first step, and `sk-lem-wgen-geometric-constituents/lem-zl-geometric-constituents-any-base`,
proof paragraphs 1--2.
(blueprint: lem-zl-geometric-power-orbit).

Proof: Form the isotypic components of the supplied finite semisimple carrier.
Frobenius permutes them: a simple object's image under the Frobenius equivalence
is simple, and each nonzero component of its inclusion lands in an isomorphic
simple factor. An orbit sum is lisse and inherits the Weil map, so arithmetic
simplicity implies transitivity. Take a positive power fixing the finitely many
classes. On a chosen block, identify the return with an intertwiner of its simple
factor tensored with an invertible operator on the multiplicity space; Schur's
lemma gives this description. Choose an eigenline of the multiplicity operator
and propagate it around the orbit. Their sum is a nonzero Weil subobject, hence
is the original object by simplicity. Thus each isotypic block has multiplicity
one. Restrict the iterated original Weil map to each embedded block: these
restrictions are invertible and define the power algebras W. Their inclusions
are equivariant, so the geometric sum isomorphism lifts to the power-algebra
category. Iterating the original Weil map identifies any two blocks and gives
exactly the stated equation with their inclusions. This assertion constructs
neither a constant-field model nor a local Frobenius comparison. -/
theorem exists_geometric_power_orbit
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    (N : ℕ) (T : Fin N → AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hT : ∀ i, IsIrreducibleAdicLocalSystem (T i)) (vT : V.obj.carrier ≅ ⨁ T) :
    ∃ (r : ℕ) (_ : 0 < r) (n : ℕ)
      (W : Fin n → IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
      (v : (ProEtaleWeilSheaf.powFunctor k₀ l X r).obj V.obj ≅ ⨁ W),
      (∀ a, IsIrreducibleAdicLocalSystem (W a).carrier) ∧
      ∀ a b, ∃ (j : ℕ)
        (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj (W a).carrier ≅
          (W b).carrier),
        e.hom ≫ (biproduct.ι W b ≫ v.inv).hom.f =
          (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).map
            (biproduct.ι W a ≫ v.inv).hom.f ≫ (V.obj.frobeniusPowIso j).hom := by
  classical
  let n := N
  let U := T
  have hU := hT
  let s := vT
  have hne := geometric_factors_pairwise_nonisomorphic V hV N T hT vT
  obtain ⟨σ, e, he⟩ := monomial_return V U hU hne s
  have hcycle := transitive_return V hV U hU s σ e he
  let i (a : Fin n) := biproduct.ι U a ≫ s.inv
  have he' (a : Fin n) : (e a).hom ≫ i (σ a) =
      (frobeniusPullback k₀ l X).map (i a) ≫ V.obj.str.hom := he a
  let r := orderOf σ
  have hr : 0 < r := orderOf_pos σ
  have hreturn (a : Fin n) :
      ∃ g : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r).obj (U a) ≅ U a,
        g.hom ≫ i a =
          (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r).map (i a) ≫
            (V.obj.frobeniusPowIso r).hom := by
    have h := iterated_return V U i σ e he' r a
    have ha : (σ ^ r) a = a := by rw [pow_orderOf_eq_one]; rfl
    rw [ha] at h
    exact h
  choose ψ hψ using hreturn
  let W (a : Fin n) : IsoAlgebra
      (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r) := IsoAlgebra.mk (U a) (ψ a)
  let P := (ProEtaleWeilSheaf.powFunctor k₀ l X r).obj V.obj
  let g (a : Fin n) : W a ⟶ P := ObjectProperty.homMk ⟨i a, (hψ a).symm⟩
  let m : ⨁ W ⟶ P := biproduct.desc g
  let D := IsoAlgebra.forget (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r)
  have hm : (D.mapBiproduct W).inv ≫ D.map m = s.inv := by
    rw [Functor.mapBiproduct_inv]
    apply biproduct.hom_ext'
    intro a
    simp only [biproduct.ι_desc_assoc, ← D.map_comp, m, biproduct.ι_desc]
    rfl
  have hmi : IsIso ((D.mapBiproduct W).inv ≫ D.map m) := by
    rw [hm]
    infer_instance
  have : IsIso (D.map m) := IsIso.of_isIso_comp_left (D.mapBiproduct W).inv (D.map m)
  have : IsIso m := isIso_of_reflects_iso m D
  let v : P ≅ ⨁ W := (asIso m).symm
  have hι (a : Fin n) : (biproduct.ι W a ≫ v.inv).hom.f = i a := by
    change (biproduct.ι W a ≫ biproduct.desc g).hom.f = i a
    rw [biproduct.ι_desc]
    rfl
  refine ⟨r, hr, n, W, v, hU, fun a b ↦ ?_⟩
  obtain ⟨j, hj⟩ := (hcycle a b).exists_nat_pow_eq
  have h := iterated_return V U i σ e he' j a
  rw [hj] at h
  obtain ⟨g', hg'⟩ := h
  exact ⟨j, g', by simpa only [hι] using hg'⟩

end AlgebraicGeometry.WeilSheaf
