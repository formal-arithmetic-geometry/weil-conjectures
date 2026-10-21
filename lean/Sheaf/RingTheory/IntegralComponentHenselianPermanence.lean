/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Group.Idempotent
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Connected integral algebras over henselian local rings

Source: Hübner--Schmidt, The tame site of a scheme, printed p. 12, permanence paragraph
citing Artin Proposition 3.3; Stacks Project, More on Algebra, Tags 092X and 09XK
(blueprint: lem-trf-integral-component-henselian-permanence).
-/

@[expose] public section

universe u v

namespace HenselianLocalRing

/-- The zero-one idempotent condition forces the finite-product decomposition to have
exactly one factor. Transport its henselian local structure back to the algebra. -/
private theorem finite_connected_henselian
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    [HenselianLocalRing R] [Algebra R B] [Nontrivial B] [Module.Finite R B]
    (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) :
    HenselianLocalRing B := by
  classical
  obtain ⟨n, A, rings, algebras, henselian, localMaps, ⟨e⟩, _, _⟩ :=
    finite_over_henselian_exists_algEquiv_pi R B
  let := rings
  let := algebras
  let := henselian
  have hn : Nonempty (Fin n) := by
    by_contra h
    have : IsEmpty (Fin n) := ⟨fun i => h ⟨i⟩⟩
    exact zero_ne_one (e.injective (Subsingleton.elim _ _))
  have hs : Subsingleton (Fin n) := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    let a : ∀ k, A k := fun k => if k = i then 1 else 0
    have ha : IsIdempotentElem (e.symm a) := by
      apply e.injective
      simp only [map_mul, AlgEquiv.apply_symm_apply]
      funext k
      change a k * a k = a k
      dsimp [a]
      split <;> simp
    rcases hc _ ha with h | h
    · have h' := congrFun (congrArg e h) i
      simp [a] at h'
    · have h' := congrFun (congrArg e h) j
      simp [a, Ne.symm hij] at h'
  let : Unique (Fin n) := ⟨⟨Classical.choice hn⟩, fun i => hs.elim i _⟩
  exact HenselianLocalRing.of_ringEquiv
    (e.toRingEquiv.trans (RingEquiv.piUnique A)).symm

/-- An integral homomorphism between local rings contracts the maximal ideal to the
maximal ideal and therefore reflects units. -/
private theorem integral_local_map
    (A : Type*) (B : Type*) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [Algebra.IsIntegral A B] :
    IsLocalHom (algebraMap A B) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 4 0).mp
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal B))

/-- A nonzero connected integral algebra over a henselian local ring is henselian local;
its structure map is local and its canonical residue-field extension is algebraic.
Strict henselianity of the base implies strict henselianity of the algebra.
Source: Hübner--Schmidt, printed p. 12, permanence paragraph citing Artin Proposition 3.3;
Stacks Project, Tags 092X and 09XK, with the connected specialization of Tag 04GH.
(blueprint: lem-trf-integral-component-henselian-permanence).

Proof:
1. A finite R-subalgebra A of S is nonzero and has only zero-one idempotents. Apply
   lem-weil-pbc-finite-over-henselian-local-product. A coordinate idempotent contradicts
   connectedness if there are two factors; nonzeroness excludes the empty product.
   The resulting singleton-product equivalence transports henselianity to A.
2. For s in S, R[s] is finite by lem-weil-pbc-finite-of-integral-generators. Its locality
   makes either s or 1-s a unit there, hence in S. This proves S is local.
3. Any integral map between local rings contracts the target maximal ideal to the source
   maximal ideal by lem-weil-pbc-integral-maximal-contracts-maximal and uniqueness. Thus
   both R to S and every finite subalgebra inclusion A to S are local.
4. For a monic polynomial f over S and a proposed simple root a0 modulo the maximal
   ideal, adjoin its finitely many coefficients and a0 to R. This is a finite henselian
   local subalgebra A. Locality of A to S descends the root and derivative conditions.
   Hensel lifting in A supplies the required root in S. This proves henselianity directly,
   without constructing a categorical filtered colimit.
5. Lift a residue element to S and reduce its monic integral equation coefficientwise
   along R to its residue field. Compatibility of the canonical residue maps gives a
   monic nonzero annihilating polynomial, proving algebraicity of the residue extension.
6. If R is strictly henselian, its residue field is separably closed. Mathlib's general
   Algebra.IsAlgebraic.isSepClosed (which also realizes the finite-extension dependency
   lem-kun-sep-closed-finite-extension-sep-closed) implies that the residue field of S is
   separably closed. Combine this with Step 4. No finiteness, reducedness or domain
   assumption on S is used. -/
theorem integral_component_henselian_permanence
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [HenselianLocalRing R] [Algebra R S] [Nontrivial S] [Algebra.IsIntegral R S]
    (hconnected : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∃ (_ : HenselianLocalRing S), ∃ (_ : IsLocalHom (algebraMap R S)),
      @Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        _ _ (IsLocalRing.ResidueField.map (algebraMap R S)).toAlgebra ∧
      (IsStrictlyHenselianLocalRing R → IsStrictlyHenselianLocalRing S) := by
  classical
  have hstage (A : Subalgebra R S) [Module.Finite R A] : HenselianLocalRing A := by
    apply finite_connected_henselian R A
    intro e he
    rcases hconnected e (congrArg Subtype.val he) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hlocal : IsLocalRing S := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    let A := Algebra.adjoin R ({a} : Set S)
    have : Module.Finite R A :=
      Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
    have : HenselianLocalRing A := hstage A
    let a' : A := ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self a').imp
      (fun h => h.map A.val) (fun h => by simpa using h.map A.val)
  have hH : HenselianLocalRing S := by
    refine ⟨?_⟩
    intro f hf a₀ hmem hunit
    let t : Finset S := insert a₀ f.coeffs
    let A := Algebra.adjoin R (t : Set S)
    have : Module.Finite R A := Algebra.finite_adjoin_of_finite_of_isIntegral
      t.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral x)
    have : HenselianLocalRing A := hstage A
    have : Algebra.IsIntegral A S :=
      ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
    have : IsLocalHom (algebraMap A S) := integral_local_map A S
    have hc (n : ℕ) : f.coeff n ∈ A := by
      by_cases h : f.coeff n = 0
      · simp [h]
      · exact Algebra.subset_adjoin (Finset.mem_insert_of_mem
          (Polynomial.mem_coeffs_iff.mpr ⟨n, Polynomial.mem_support_iff.mpr h, rfl⟩))
    obtain ⟨g, hg⟩ := (Polynomial.mem_lifts (f := A.val.toRingHom) f).mp
      ((Polynomial.lifts_iff_coeff_lifts (f := A.val.toRingHom) f).mpr (fun n => ⟨⟨_, hc n⟩, rfl⟩))
    let a' : A := ⟨a₀, Algebra.subset_adjoin (Finset.mem_insert_self _ _)⟩
    have hinj : Function.Injective A.val.toRingHom := Subtype.val_injective
    have hgmonic : g.Monic := hinj.monic_map_iff.mpr (hg.symm ▸ hf)
    have heval : A.val (g.eval a') = f.eval a₀ := by
      rw [← hg]
      exact (Polynomial.eval_map_apply (p := g) A.val.toRingHom a').symm
    have hderiv : A.val (g.derivative.eval a') = f.derivative.eval a₀ := by
      rw [← hg, Polynomial.derivative_map]
      exact (Polynomial.eval_map_apply (p := g.derivative) A.val.toRingHom a').symm
    have hm : g.eval a' ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal] at hmem ⊢
      intro hu
      exact hmem (heval ▸ hu.map A.val)
    have hu : IsUnit (g.derivative.eval a') := by
      apply (isUnit_map_iff (algebraMap A S) _).mp
      change IsUnit (A.val (g.derivative.eval a'))
      rwa [hderiv]
    obtain ⟨a, ha, hdiff⟩ := HenselianLocalRing.is_henselian g hgmonic a' hm hu
    refine ⟨a, ?_, ?_⟩
    · rw [Polynomial.IsRoot.def, ← hg]
      exact (Polynomial.eval_map_apply (p := g) A.val.toRingHom a).trans
        (by rw [ha, map_zero])
    · rw [IsLocalRing.mem_maximalIdeal] at hdiff ⊢
      intro hu
      apply hdiff
      apply (isUnit_map_iff (algebraMap A S) _).mp
      exact hu
  have hmap : IsLocalHom (algebraMap R S) := integral_local_map R S
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    (IsLocalRing.ResidueField.map (algebraMap R S)).toAlgebra
  have halg : Algebra.IsAlgebraic
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := S) x
    obtain ⟨p, hp, hps⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    refine ⟨p.map (IsLocalRing.residue R), (hp.map _).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have he : (IsLocalRing.ResidueField.map (algebraMap R S)).comp
        (IsLocalRing.residue R) = (IsLocalRing.residue S).comp (algebraMap R S) := by
      ext r
      rfl
    change p.eval₂ ((IsLocalRing.ResidueField.map (algebraMap R S)).comp
      (IsLocalRing.residue R)) (IsLocalRing.residue S s) = 0
    rw [he, ← Polynomial.hom_eval₂, hps, map_zero]
  refine ⟨hH, hmap, halg, ?_⟩
  intro hstrict
  have : IsStrictlyHenselianLocalRing R := hstrict
  exact ⟨Algebra.IsAlgebraic.isSepClosed
    (F := IsLocalRing.ResidueField R) (E := IsLocalRing.ResidueField S)⟩

end HenselianLocalRing
