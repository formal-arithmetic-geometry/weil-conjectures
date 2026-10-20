/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.RingTheory.FlatFiberPrimeHeight
import WeilConjectures.RingTheory.MinimalComponentDimensionMaximum

/-!
# Dimension formula over a universally catenary domain

Source: Stacks Project, Algebra, Tag 02IJ, equality clause
(blueprint: lem-exc-dimension-formula-universally-catenary-finite-type-domain).

Residue fields use Mathlib's `IsFractionRing (A ⧸ p) p.ResidueField` instance.
Transcendence degrees are mapped to extended natural numbers by `Cardinal.toENat`;
they are finite here, so this retains their ordinary numerical values.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsUniversallyCatenary

private theorem saturated_of_full_height {α : Type*} [PartialOrder α]
    (c : LTSeries α) (hlen : (c.length : ℕ∞) = Order.height c.last) :
    IsMin c.head ∧ ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ := by
  have hind := Order.height_eq_index_of_length_eq_height_last hlen
  refine ⟨Order.height_eq_zero.mp (hind 0), ?_⟩
  intro i
  refine ⟨c.step i, ?_⟩
  intro x hprev hnext
  have h1 := Order.height_add_one_le hprev
  have h2 := Order.height_add_one_le hnext
  rw [hind i.castSucc] at h1
  rw [hind i.succ] at h2
  have h1' : ((i.val + 1 : ℕ) : ℕ∞) ≤ Order.height x := by simpa using h1
  have h2' : Order.height x + 1 ≤ ((i.val + 1 : ℕ) : ℕ∞) := by simpa using h2
  have h3 : ((i.val + 2 : ℕ) : ℕ∞) ≤ ((i.val + 1 : ℕ) : ℕ∞) := calc
    _ = ((i.val + 1 : ℕ) : ℕ∞) + 1 := by push_cast; rfl
    _ ≤ Order.height x + 1 := add_le_add h1' le_rfl
    _ ≤ _ := h2'
  have h4 : i.val + 2 ≤ i.val + 1 := by exact_mod_cast h3
  omega

private theorem smash_saturated {α : Type*} [PartialOrder α]
    (a b : LTSeries α) (h : a.last = b.head)
    (ha : ∀ i : Fin a.length, a i.castSucc ⋖ a i.succ)
    (hb : ∀ i : Fin b.length, b i.castSucc ⋖ b i.succ) :
    ∀ i : Fin (a.smash b h).length,
      (a.smash b h) i.castSucc ⋖ (a.smash b h) i.succ := by
  intro i
  change Fin (a.length + b.length) at i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd] using ha j
  · intro j
    simpa only [RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd] using hb j

private theorem saturated_primeChain {A : Type*} [CommRing A]
    (c : LTSeries (PrimeSpectrum A))
    (hc : ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ) :
    IsSaturatedPrimeChain A c.head.asIdeal c.last.asIdeal c.length
      (fun i ↦ (c i).asIdeal) := by
  refine ⟨⟨fun i ↦ (c i).isPrime, rfl, rfl, fun i ↦ c.step i⟩, ?_⟩
  rintro i ⟨r, hr, hprev, hnext⟩
  exact (hc i).2 (c := ⟨r, hr⟩) hprev hnext

private theorem catenary_surjective_height
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : Function.Surjective f) (hcat : IsCatenaryRing A)
    (q : Ideal B) [q.IsPrime] :
    (q.comap f).height = (RingHom.ker f).height + q.height := by
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨a, halast, halen⟩ := Ideal.exists_ltSeries_length_eq_height (RingHom.ker f)
  obtain ⟨b, hblast, hblen⟩ := Ideal.exists_ltSeries_length_eq_height q
  obtain ⟨d, hdlast, hdlen⟩ := Ideal.exists_ltSeries_length_eq_height (q.comap f)
  have full (c : LTSeries (PrimeSpectrum A)) (p : Ideal A) [p.IsPrime]
      (hlast : c.last = ⟨p, inferInstance⟩) (hlen : (c.length : ℕ∞) = p.height) :
      IsMin c.head ∧ ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ := by
    apply saturated_of_full_height
    rw [hlast, ← PrimeSpectrum.height_eq_orderHeight]
    exact hlen
  obtain ⟨hamin, hacov⟩ := full a _ halast halen
  obtain ⟨hdmin, hdcov⟩ := full d _ hdlast hdlen
  have hbfull : (b.length : ℕ∞) = Order.height b.last := by
    rw [hblast, ← PrimeSpectrum.height_eq_orderHeight]
    exact hblen
  obtain ⟨hbmin, hbcov⟩ := saturated_of_full_height b hbfull
  let e := PrimeSpectrum.comap f
  have hstrict : StrictMono e := by
    intro x y hxy
    exact (Ideal.orderEmbeddingOfSurjective f hf).strictMono hxy
  let b' := b.map e hstrict
  have hb'cov : ∀ i : Fin b'.length, b' i.castSucc ⋖ b' i.succ := by
    intro i
    refine ⟨hstrict (b.step i), ?_⟩
    intro x hx hy
    change (b i.castSucc).asIdeal.comap f < x.asIdeal at hx
    change x.asIdeal < (b i.succ).asIdeal.comap f at hy
    have hk : RingHom.ker f ≤ x.asIdeal :=
      (Ideal.comap_mono (show (⊥ : Ideal B) ≤ (b i.castSucc).asIdeal from bot_le)).trans
        hx.le
    have : (x.asIdeal.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hk
    have heq : (x.asIdeal.map f).comap f = x.asIdeal := by
      rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hk]
    apply (hbcov i).2 (c := ⟨x.asIdeal.map f, inferInstance⟩)
    · apply (Ideal.orderEmbeddingOfSurjective f hf).lt_iff_lt.mp
      simpa only [Ideal.orderEmbeddingOfSurjective_apply, heq] using hx
    · apply (Ideal.orderEmbeddingOfSurjective f hf).lt_iff_lt.mp
      simpa only [Ideal.orderEmbeddingOfSurjective_apply, heq] using hy
  have hconnect : a.last = b'.head := by
    have hbzero : b.head = ⊥ := isMin_iff_eq_bot.mp hbmin
    apply PrimeSpectrum.ext
    rw [halast]
    change RingHom.ker f = b.head.asIdeal.comap f
    rw [hbzero]
    rfl
  let c := a.smash b' hconnect
  have hchead : c.head.asIdeal = (⊥ : Ideal A) := by
    have ha0 := isMin_iff_eq_bot.mp hamin
    dsimp only [c]
    rw [RelSeries.head_smash, ha0]
    rfl
  have hclast : c.last.asIdeal = q.comap f := by
    dsimp only [c]
    rw [RelSeries.last_smash]
    change b.last.asIdeal.comap f = q.comap f
    rw [hblast]
  have hdhead : d.head.asIdeal = (⊥ : Ideal A) := by
    rw [isMin_iff_eq_bot.mp hdmin]
    rfl
  have hdc := saturated_primeChain d hdcov
  have hcc := saturated_primeChain c (smash_saturated a b' hconnect hacov hb'cov)
  rw [hdhead, hdlast] at hdc
  rw [hchead, hclast] at hcc
  have hl := (hcat ⊥ (q.comap f) bot_le).2 _ _ _ _ hdc hcc
  have hl' : d.length = a.length + b.length := hl
  rw [← hdlen, ← halen, ← hblen, ← Nat.cast_add, hl']

private theorem polynomial_field_formula
    {k : Type*} [Field k] (n : ℕ) (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    q.height + Cardinal.toENat (Algebra.trdeg k q.ResidueField) = n := by
  let P := MvPolynomial (Fin n) k
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (Ideal.height_ne_top_of_isPrime (I := q))
  have hdim : ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, ← hd]
    rfl
  have : Algebra.EssFiniteType k q.ResidueField := .comp k P _
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 k q.ResidueField)
  obtain ⟨_, z, hz, _, hmin, hdz⟩ :=
    AlgebraicGeometry.minimal_component_dimension_maximum (k := k) q d r hdim hr
  have hz0 : z = ⊥ := (hmin ⊥ inferInstance bot_le).symm
  rw [hz0, (RingEquiv.quotientBot P).ringKrullDim] at hdz
  have hP : ringKrullDim P = (n : WithBot ℕ∞) := by
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  rw [hP] at hdz
  have hsum : n = d + r := by exact_mod_cast hdz
  rw [← hd, hr, Cardinal.toENat_nat, ← Nat.cast_add, hsum]

private theorem polynomial_formula
    {R : Type*} [CommRing R] [IsNoetherianRing R] (n : ℕ)
    (p : Ideal R) (q : Ideal (MvPolynomial (Fin n) R)) [p.IsPrime] [q.IsPrime]
    (hpq : p = q.comap (algebraMap R (MvPolynomial (Fin n) R))) :
    q.height + Cardinal.toENat
        (@Algebra.trdeg p.ResidueField q.ResidueField _ _
          (Ideal.ResidueField.map p q (algebraMap R _) hpq).toAlgebra) = p.height + n := by
  let P := MvPolynomial (Fin n) R
  let κ := p.ResidueField
  let : Algebra κ q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R P) hpq).toAlgebra
  let eF := PrimeSpectrum.preimageEquivFiber R P (⟨p, inferInstance⟩ : PrimeSpectrum R)
  let x : PrimeSpectrum.comap (algebraMap R P) ⁻¹' {⟨p, inferInstance⟩} :=
    ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hpq.symm⟩
  let Q := (eF x).asIdeal
  have : Q.IsPrime := (eF x).isPrime
  let : Algebra κ Q.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q)
  let i : P →+* p.Fiber P := Algebra.TensorProduct.includeRight.toRingHom
  have hQ : q = Q.comap i := by
    have h := congrArg (fun y ↦ y.val.asIdeal) (eF.symm_apply_apply x)
    exact h.symm
  have hheight : q.height = p.height + Q.height := by
    rw [hQ]
    exact RingHom.height_eq_add_of_flat_fiber
      (RingHom.flat_algebraMap_iff.mpr inferInstance) p Q
  let g := Ideal.ResidueField.map q Q i hQ
  have hg : g.comp (algebraMap κ q.ResidueField) = algebraMap κ Q.ResidueField := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp only [RingHom.comp_apply]
    change Ideal.ResidueField.map q Q i hQ
      (Ideal.ResidueField.map p q (algebraMap R P) hpq (algebraMap R κ r)) = _
    rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
    change algebraMap (p.Fiber P) Q.ResidueField (i (algebraMap R P r)) =
      algebraMap κ Q.ResidueField (algebraMap R κ r)
    rw [← IsScalarTower.algebraMap_apply R κ Q.ResidueField]
    rw [show i (algebraMap R P r) = algebraMap R (p.Fiber P) r from
      Algebra.TensorProduct.includeRight.commutes r]
    exact (IsScalarTower.algebraMap_apply R (p.Fiber P) Q.ResidueField r).symm
  let eqκ : q.ResidueField ≃ₐ[κ] Q.ResidueField :=
    AlgEquiv.ofBijective ⟨g, fun r ↦ congr($hg r)⟩
      ((p.surjectiveOnStalks_residueField.baseChange').residueFieldMap_bijective q Q hQ)
  let e : p.Fiber P ≃ₐ[κ] MvPolynomial (Fin n) κ :=
    MvPolynomial.algebraTensorAlgEquiv R κ
  let Q' := Q.map e.toRingHom
  have : Q'.IsPrime := Ideal.map_isPrime_of_equiv e.toRingEquiv
  have heQ : Q = Q'.comap e.toRingHom := by
    dsimp [Q']
    exact (Ideal.comap_map_of_bijective e.toRingHom e.bijective).symm
  let eκ : Q.ResidueField ≃ₐ[κ] Q'.ResidueField :=
    Ideal.residueFieldAlgEquiv Q Q' e heQ
  have htr : Cardinal.toENat (Algebra.trdeg κ q.ResidueField) =
      Cardinal.toENat (Algebra.trdeg κ Q'.ResidueField) := by
    have h := (eqκ.trans eκ).lift_trdeg_eq
    have ht := congrArg Cardinal.toENat h
    simpa only [Cardinal.toENat_lift] using ht
  have hfield := polynomial_field_formula n Q'
  have hh : Q.height = Q'.height := (e.toRingEquiv.height_map Q).symm
  change q.height + Cardinal.toENat (Algebra.trdeg κ q.ResidueField) = p.height + n
  rw [hheight, hh, htr, add_assoc, hfield]

private theorem generic_residue_trdeg
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (h0 : (⊥ : Ideal R) = (⊥ : Ideal S).comap (algebraMap R S)) :
    Cardinal.toENat
        (@Algebra.trdeg (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField _ _
          (Ideal.ResidueField.map ⊥ ⊥ (algebraMap R S) h0).toAlgebra) =
      Cardinal.toENat (Algebra.trdeg R S) := by
  let K := (⊥ : Ideal R).ResidueField
  let L := (⊥ : Ideal S).ResidueField
  let : Algebra K L := (Ideal.ResidueField.map ⊥ ⊥ (algebraMap R S) h0).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun r ↦ by
    change algebraMap R L r =
      Ideal.ResidueField.map ⊥ ⊥ (algebraMap R S) h0 (algebraMap R K r)
    rw [Ideal.ResidueField.map_algebraMap]
    exact IsScalarTower.algebraMap_apply R S L r
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
  have hRK := trdeg_eq_zero_iff.mpr (inferInstance : Algebra.IsAlgebraic R K)
  have hSL := trdeg_eq_zero_iff.mpr (inferInstance : Algebra.IsAlgebraic S L)
  have h1 := congrArg Cardinal.toENat (lift_trdeg_add_eq R S L)
  have : FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective R K).mpr (IsFractionRing.injective R K)
  have : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).mpr (RingHom.injective _)
  have ht2 := @lift_trdeg_add_eq R K L _ _ _ _ _ _
    (inferInstance : IsScalarTower R K L) _ _
    (inferInstance : FaithfulSMul R K) (inferInstance : FaithfulSMul K L)
  have h2 := congrArg Cardinal.toENat ht2
  simp only [map_add, Cardinal.toENat_lift, hRK, hSL, map_zero, add_zero, zero_add]
    at h1 h2
  exact h2.trans h1.symm

private theorem surjective_residue_trdeg
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (p : Ideal R) (q : Ideal B) [p.IsPrime] [q.IsPrime]
    (hpq : p = q.comap (algebraMap R B))
    (hpr : p = (q.comap f.toRingHom).comap (algebraMap R A)) :
    Cardinal.toENat
        (@Algebra.trdeg p.ResidueField (q.comap f.toRingHom).ResidueField _ _
          (Ideal.ResidueField.map p (q.comap f.toRingHom) (algebraMap R A) hpr).toAlgebra) =
      Cardinal.toENat
        (@Algebra.trdeg p.ResidueField q.ResidueField _ _
          (Ideal.ResidueField.map p q (algebraMap R B) hpq).toAlgebra) := by
  let r := q.comap f.toRingHom
  let : Algebra p.ResidueField r.ResidueField :=
    (Ideal.ResidueField.map p r (algebraMap R A) hpr).toAlgebra
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R B) hpq).toAlgebra
  let g := Ideal.ResidueField.map r q f.toRingHom rfl
  have hg : g.comp (algebraMap p.ResidueField r.ResidueField) =
      algebraMap p.ResidueField q.ResidueField := by
    apply Ideal.ResidueField.ringHom_ext
    ext x
    change Ideal.ResidueField.map r q f.toRingHom rfl
      (Ideal.ResidueField.map p r (algebraMap R A) hpr (algebraMap R _ x)) =
        Ideal.ResidueField.map p q (algebraMap R B) hpq (algebraMap R _ x)
    simp only [Ideal.ResidueField.map_algebraMap]
    exact congrArg (algebraMap B q.ResidueField) (f.commutes x)
  let e : r.ResidueField ≃ₐ[p.ResidueField] q.ResidueField :=
    AlgEquiv.ofBijective ⟨g, fun x ↦ congr($hg x)⟩
      ((RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective r q rfl)
  have h := congrArg Cardinal.toENat e.lift_trdeg_eq
  simpa only [Cardinal.toENat_lift] using h

/-- The dimension formula for a finite type inclusion of Noetherian universally catenary
commutative domains, at a prime and its contraction. Source: Stacks Project, Algebra,
Tag 02IJ, equality clause
(blueprint: lem-exc-dimension-formula-universally-catenary-finite-type-domain).

Proof, using a finite polynomial presentation instead of induction on generators:
1. For a polynomial ring in n variables over a field, the minimal-component dimension
   formula and its unique minimal prime (0) give height plus residue transcendence degree n.
2. For P = R[X₁, ..., Xₙ], the flat fibre height formula gives height(q') = height(p) +
   height(Q). The fibre is kappa(p)[X₁, ..., Xₙ], and its residue field at Q agrees with
   kappa(q') over kappa(p). Step 1 gives the polynomial formula.
3. Choose a surjection P → S with prime kernel k. A full-height chain ending at k and
   the inverse image of a full-height chain ending at q concatenate to a saturated chain
   from (0) to q'. Catenarity of P compares it with a full-height chain ending at q',
   giving height(q') = height(k) + height(q).
4. The surjection identifies residue fields at corresponding primes. Apply step 2 at
   q' and at k, which contracts to zero. The generic residue fields are fraction fields;
   the domain tower formula identifies their relative degree with trdeg_R S, since
   fractions are algebraic over their domains. Thus height(k) + trdeg_R S = n.
5. Substitute steps 3 and 4 into the formula at q' and cancel the finite height of k.
   No subtraction or cancellation of an infinite value occurs.
-/
theorem height_add_trdeg_residueField_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S]
    (hR : IsUniversallyCatenary R) (hinj : Function.Injective (algebraMap R S))
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    q.height + Cardinal.toENat
        (@Algebra.trdeg p.ResidueField q.ResidueField _ _
          (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra) =
      p.height + Cardinal.toENat (Algebra.trdeg R S) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let P := MvPolynomial (Fin n) R
  let r := q.comap f.toRingHom
  let k := RingHom.ker f.toRingHom
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : k.IsPrime := RingHom.ker_isPrime f.toRingHom
  have hpr : p = r.comap (algebraMap R P) := by
    rw [hpq]
    dsimp [r]
    rw [Ideal.comap_comap]
    congr 1
    exact (f.comp_algebraMap).symm
  have h0 : (⊥ : Ideal R) = (⊥ : Ideal S).comap (algebraMap R S) :=
    ((RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp hinj).symm
  have h0k : (⊥ : Ideal R) = k.comap (algebraMap R P) := by
    rw [h0]
    change (⊥ : Ideal S).comap (algebraMap R S) =
      ((⊥ : Ideal S).comap f.toRingHom).comap (algebraMap R P)
    rw [Ideal.comap_comap]
    congr 1
    exact f.comp_algebraMap.symm
  have hpoly := polynomial_formula n p r hpr
  have hgeneric := polynomial_formula n (⊥ : Ideal R) k h0k
  have hres := surjective_residue_trdeg f hf p q hpq hpr
  have hgen := surjective_residue_trdeg f hf (⊥ : Ideal R) (⊥ : Ideal S) h0 h0k
  have htr := generic_residue_trdeg hinj h0
  have hgeneric' : k.height + Cardinal.toENat (Algebra.trdeg R S) = n := by
    calc
      _ = k.height + Cardinal.toENat
          (@Algebra.trdeg (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField _ _
            (Ideal.ResidueField.map ⊥ ⊥ (algebraMap R S) h0).toAlgebra) := by rw [htr]
      _ = k.height + Cardinal.toENat
          (@Algebra.trdeg (⊥ : Ideal R).ResidueField k.ResidueField _ _
            (Ideal.ResidueField.map ⊥ k (algebraMap R P) h0k).toAlgebra) := by
        congr 1
        exact hgen.symm
      _ = n := by simpa only [Ideal.height_bot, zero_add] using hgeneric
  have hheight := catenary_surjective_height f.toRingHom hf (hR.2 P) q
  rw [hheight, hres] at hpoly
  apply ENat.add_right_injective_of_ne_top
    (Ideal.height_ne_top_of_isPrime (I := k))
  calc
    k.height + (q.height + _) = (k.height + q.height) + _ := (add_assoc _ _ _).symm
    _ = p.height + n := hpoly
    _ = k.height + (p.height + Cardinal.toENat (Algebra.trdeg R S)) := by
      rw [← hgeneric']
      ac_rfl

end IsUniversallyCatenary
