/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Sheaf.LinearAlgebra.BoundedCoordinateSplitProjections
import Sheaf.LinearAlgebra.MatrixUnitCornerEmbedding
import Sheaf.LinearAlgebra.OrthogonalSplitIdempotentsSmallModule
import Sheaf.SetTheory.UncountableAlmostDisjointFamily
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Denumerable

/-! # Reconstruction from a rank-one corner

Source: main-20261015 blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary
(blueprint: lem-sfb-countable-endomorphism-module-reconstruction).

The basis is algebraic. The index type is countable and pointed, equivalently a nonempty
finite set or a copy of the natural numbers, with the distinguished index labelled zero.
The corner is the range of the rank-one operator's action on the algebraic module.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t
open scoped TensorProduct

namespace Padic

private theorem reindex_norm_bound
    {E : Type u} [NormedField E] {V : Type v}
    [NormedAddCommGroup V] [NormedSpace E V]
    {J : Type t} (b : Module.Basis J E V) (e : J ≃ ℕ) (c C : ℝ)
    (hb : ∀ a : J →₀ E,
      c * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ) ≤ ‖b.repr.symm a‖ ∧
      ‖b.repr.symm a‖ ≤ C * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ)) :
    ∀ a : ℕ →₀ E,
      c * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ) ≤ ‖(b.reindex e).repr.symm a‖ ∧
      ‖(b.reindex e).repr.symm a‖ ≤
        C * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ) := by
  classical
  intro a
  let a' := a.mapDomain e.symm
  have ha : (b.reindex e).repr.symm a = b.repr.symm a' := by
    apply (b.reindex e).repr.injective
    simp [a', Module.Basis.repr_reindex]
  have hs : a'.support.sup (fun j ↦ ‖a' j‖₊) = a.support.sup (fun j ↦ ‖a j‖₊) := by
    simp only [a', Finsupp.mapDomain_support_of_injective e.symm.injective]
    rw [Finset.sup_image]
    congr 1
    funext j
    rw [Function.comp_apply, Finsupp.mapDomain_apply e.symm.injective]
  simpa only [ha, hs] using hb a'

/-- Countably spanned algebraic representations of the continuous endomorphism algebra
are reconstructed by the specified rank-one corner map.

Source: main-20261015 blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary
(blueprint: lem-sfb-countable-endomorphism-module-reconstruction).

Proof:
1. The lower norm bound bounds every coordinate by the norm divided by c. Thus the
   coordinates and all matrix units E_ij are continuous; the latter have bound C/c.
   The same estimate makes theta_v(w) = lambda(w) v continuous.
2. The image eH is an E-subspace, and e acts identically there. The displayed formula
   is bilinear and T theta_v = theta_(Tv), so the tensor map intertwines the D-actions.
3. Expand a tensor as a finite sum of b_j tensor h_j. Applying E_0k to a relation
   between its images isolates h_k. This proves injectivity.
4. Its image N is a D-submodule. The quotient Q = H/N is countably spanned, and eQ = 0
   because eh = theta_(b_0)(eh). All finite coordinate projections therefore kill Q.
   For a finite basis their sum is the identity, so Q = 0.
5. For a countably infinite basis use lem-sfb-uncountable-almost-disjoint-family to
   obtain uncountably many infinite subsets A_i with finite pairwise intersections.
   Each A_i has an increasing bijective enumeration by the natural numbers.
6. Reindexing coordinates gives operators u_i and r_i, bounded by C/c, with
   r_i u_i = 1 and u_i r_i = p_i, the coordinate projection onto A_i.
7. For i distinct from j, p_i p_j is a finite coordinate projection and kills Q.
8. If q is nonzero in Q, the vectors u_i q are nonzero and linearly independent:
   applying p_i to a finite relation isolates its ith coefficient.
9. By lem-sfb-independent-family-spanning-cardinality (linearIndependent_le_span''),
   that independent index set injects into a countable spanning set of Q, impossible.
10. Hence Q = 0, so the tensor map is bijective; its inverse also intertwines D.
    This argument includes the zero module and a one-element basis.

The pure-tensor intertwining equation expresses D-linearity with D acting only on the
first tensor factor. The E-action on H is the scalar restriction of its unital D-action,
encoded by IsScalarTower; no topology on H is requested. -/
theorem countableEndomorphismModule_reconstruction
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hE : ∀ a : E, ‖a‖ = coefficientExtensionAbsoluteValue l E a)
    (V : Type v) [NormedAddCommGroup V] [NormedSpace E V]
    (J : Type t) [Countable J] (j₀ : J) (b : Module.Basis J E V)
    (c C : ℝ) (_hc : 0 < c) (_hcC : c ≤ C)
    (_hb : ∀ a : J →₀ E,
      c * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ) ≤ ‖b.repr.symm a‖ ∧
      ‖b.repr.symm a‖ ≤ C * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ)) :
    ∃ lam : V →L[E] E, lam.toLinearMap = b.coord j₀ ∧
      ∀ (H : Type w) [AddCommGroup H] [Module (V →L[E] V) H] [Module E H]
        [IsScalarTower E (V →L[E] V) H],
        (∃ S : Set H, S.Countable ∧ Submodule.span E S = ⊤) →
        ∃ Φ : (V ⊗[E] LinearMap.range
            (Module.toModuleEnd E H (lam.smulRight (b j₀)))) ≃ₗ[E] H,
          (∀ (v₀ : V) (h : LinearMap.range
              (Module.toModuleEnd E H (lam.smulRight (b j₀)))),
            Φ (v₀ ⊗ₜ[E] h) = (lam.smulRight v₀) • (h : H)) ∧
          (∀ (T : V →L[E] V) (v₀ : V) (h : LinearMap.range
              (Module.toModuleEnd E H (lam.smulRight (b j₀)))),
            Φ (T v₀ ⊗ₜ[E] h) = T • Φ (v₀ ⊗ₜ[E] h)) := by
  classical
  obtain ⟨lam, em, theta, p, hlam, _, hem, _, _, hp, hpp, hfinite⟩ :=
    b.bounded_coordinate_split_projections E V J j₀ c C _hc _hcC _hb
  refine ⟨lam j₀, hlam j₀, ?_⟩
  intro H _ _ _ _ hH
  let forget : (V →L[E] V) →ₐ[E] Module.End E V :=
    { ContinuousLinearMap.toLinearMapRingHom with
      commutes' := fun a ↦ by ext v; rfl }
  let D := forget.range
  let lift : D →ₐ[E] (V →L[E] V) :=
    { toFun := fun T ↦
        ⟨T.val, by
          obtain ⟨T', hT'⟩ := T.property
          rw [← hT']
          exact T'.continuous⟩
      map_zero' := by ext v; rfl
      map_one' := by ext v; rfl
      map_add' := fun _ _ ↦ by ext v; rfl
      map_mul' := fun _ _ ↦ by ext v; rfl
      commutes' := fun _ ↦ by ext v; rfl }
  let toD (T : V →L[E] V) : D := ⟨T.toLinearMap, T, rfl⟩
  let : Module D H := Module.compHom H lift.toRingHom
  have : IsScalarTower E D H := IsScalarTower.of_algebraMap_smul (fun a h ↦ by
    change lift (algebraMap E D a) • h = a • h
    rw [lift.commutes, IsScalarTower.algebraMap_smul])
  have act (T : D) (h : H) : T • h = lift T • h := rfl
  have lift_toD (T : V →L[E] V) : lift (toD T) = T := by ext v; rfl
  have hE : ∀ i j : J, (b.coord j).smulRight (b i) ∈ D := by
    intro i j
    refine ⟨em i j, ?_⟩
    ext v
    exact (hem i j v).1.trans (by rw [← hlam j]; rfl)
  have lift_rank (i j : J) :
      lift ⟨(b.coord j).smulRight (b i), hE i j⟩ = (lam j).smulRight (b i) := by
    ext v
    change b.coord j v • b i = lam j v • b i
    rw [← hlam j]
    rfl
  obtain ⟨corner, hcorner, htheta, phi, hphi, hinj, hinter, N, hN, he, hdiag⟩ :=
    b.matrixUnit_corner_embedding j₀ D hE H
  have corner_eq : corner = LinearMap.range
      (Module.toModuleEnd E H ((lam j₀).smulRight (b j₀))) := by
    ext h
    rw [← SetLike.mem_coe, hcorner]
    change (∃ x, (⟨(b.coord j₀).smulRight (b j₀), hE j₀ j₀⟩ : D) • x = h) ↔
      ∃ x, ((lam j₀).smulRight (b j₀)) • x = h
    simp only [act, lift_rank]
  have hspan : ∃ W : Set (H ⧸ N), Countable W ∧ Submodule.span E W = ⊤ := by
    obtain ⟨S, hS, hSspan⟩ := hH
    let q : H →ₗ[E] H ⧸ N := N.mkQ.restrictScalars E
    refine ⟨q '' S, (hS.image q).to_subtype, ?_⟩
    rw [← Submodule.map_span, hSspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr N.mkQ_surjective
  have hzero : Subsingleton (H ⧸ N) := by
    cases finite_or_infinite J with
    | inl hJ =>
      let := Fintype.ofFinite J
      have hid : (∑ j : J, (⟨(b.coord j).smulRight (b j), hE j j⟩ : D)) = 1 := by
        apply Subtype.ext
        change D.val (∑ j : J, (⟨(b.coord j).smulRight (b j), hE j j⟩ : D)) = 1
        rw [map_sum]
        apply b.ext
        intro j
        simp only [LinearMap.sum_apply]
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          simp [Finsupp.single_eq_of_ne hij]
        · simp
      refine ⟨fun q q' ↦ ?_⟩
      have hz (q : H ⧸ N) : q = 0 := by
        calc
          q = (1 : D) • q := (one_smul D q).symm
          _ = (∑ j : J, (⟨(b.coord j).smulRight (b j), hE j j⟩ : D)) • q :=
            by rw [hid]
          _ = 0 := by rw [Finset.sum_smul]; simp only [hdiag, Finset.sum_const_zero]
      exact (hz q).trans (hz q').symm
    | inr hJ =>
      let e : J ≃ ℕ := Classical.choice (nonempty_equiv_of_countable : Nonempty (J ≃ ℕ))
      let bn := b.reindex e
      have hbn := reindex_norm_bound b e c C _hb
      obtain ⟨ln, en, tn, pp, hln, _, hen, _, _, hppn, _, hfn⟩ :=
        bn.bounded_coordinate_split_projections E V ℕ (e j₀) c C _hc _hcC hbn
      have hen_eq (n m : ℕ) : (en n m).toLinearMap =
          (b.coord (e.symm m)).smulRight (b (e.symm n)) := by
        ext x
        change en n m x = b.coord (e.symm m) x • b (e.symm n)
        rw [(hen n m x).1]
        change (ln m).toLinearMap x • bn n = _
        rw [hln m]
        simp [bn, Module.Basis.coord_apply, Module.Basis.reindex_apply]
      obtain ⟨I, A, hI, hA, hAA⟩ := Set.exists_uncountable_almostDisjoint_family.{0}
      have hsplit := fun i ↦ bn.bounded_coordinate_split_reindexing E V c C _hc _hcC
        hbn (A i) (hA i)
      choose a u r pn hau har har0 hpn hru hur hpu hnorm using hsplit
      have horth : ∀ i j : I, i ≠ j → ∀ q : H ⧸ N,
          ((toD (u i) * toD (r i)) * (toD (u j) * toD (r j))) • q = 0 := by
        intro i j hij q
        have hp_eq (i : I) : pn i = pp (A i) := by
          ext x
          exact (hpn i x).trans (hppn (A i) x).1.symm
        have hprod : (toD (u i) * toD (r i)) * (toD (u j) * toD (r j)) =
            ∑ k ∈ (hAA i j hij).toFinset,
              (⟨(b.coord (e.symm k)).smulRight (b (e.symm k)),
                hE (e.symm k) (e.symm k)⟩ : D) := by
          apply Subtype.ext
          change ((u i * r i) * (u j * r j)).toLinearMap = _
          rw [hur i, hur j, hp_eq i, hp_eq j, (hfn (A i) (A j) (hAA i j hij)).1]
          change ContinuousLinearMap.toLinearMapRingHom
            (∑ k ∈ (hAA i j hij).toFinset, en k k) =
              D.val (∑ k ∈ (hAA i j hij).toFinset,
                (⟨(b.coord (e.symm k)).smulRight (b (e.symm k)),
                  hE (e.symm k) (e.symm k)⟩ : D))
          rw [map_sum, map_sum]
          apply Finset.sum_congr rfl
          intro k _
          exact hen_eq k k
        rw [hprod, Finset.sum_smul]
        simp only [hdiag, Finset.sum_const_zero]
      exact (Module.orthogonal_split_idempotents_small_module E D (H ⧸ N) I
        (fun i ↦ toD (u i)) (fun i ↦ toD (r i))
        (by intro i; apply Subtype.ext; exact congrArg ContinuousLinearMap.toLinearMap (hru i))
        horth).2.2 hI hspan
  have hsurj : Function.Surjective phi := by
    intro h
    have hz : N.mkQ h = 0 := Subsingleton.elim _ _
    have hm : h ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hz
    rw [← SetLike.mem_coe, hN] at hm
    exact hm
  subst corner
  refine ⟨LinearEquiv.ofBijective phi ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro v h
    change phi (v ⊗ₜ[E] h) = _
    rw [hphi, act]
    congr 1
    ext w
    change b.coord j₀ w • v = lam j₀ w • v
    rw [← hlam j₀]
    rfl
  · intro T v h
    change phi (T v ⊗ₜ[E] h) = T • phi (v ⊗ₜ[E] h)
    exact hinter (toD T) (v ⊗ₜ[E] h)

end Padic
