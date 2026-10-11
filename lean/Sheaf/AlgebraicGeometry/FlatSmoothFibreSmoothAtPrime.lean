module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.RingTheory.SingularIdeal

/-!
# Flat with smooth fibre implies smooth at a prime

Source: Stacks Project, Algebra, Lemma 00TF (lemma-flat-fibre-smooth)
(blueprint: lem-weil-pbc-flat-smooth-fibre-smooth-at-prime).
-/

@[expose] public section

universe u v

/-- Let `R → S` be a ring map, `q` a prime of `S` and `p = q ∩ R`. If `S_g` is a finitely
presented `R`-algebra for some `g ∉ q`, the local map `R_p → S_q` is flat, and the fibre
`κ(p) ⊗[R] S` (`p.Fiber S`) is smooth over `κ(p)` at the prime `Q` corresponding to `q`
(`PrimeSpectrum.preimageEquivFiber`, the kernel of `κ(p) ⊗[R] S → κ(q)`), then `R → S` is
smooth at `q`. Smoothness at a prime is `Algebra.IsSmoothAtPrime` (`∃ g ∉ q, S_g` smooth).
Source: Stacks Project, Algebra, Lemma 00TF (lemma-flat-fibre-smooth).
(blueprint: lem-weil-pbc-flat-smooth-fibre-smooth-at-prime)

Proof, following the node:
1. By (3) some `F_h`, `h ∉ Q`, is smooth over `κ(p)`, hence a local complete intersection;
shrinking, some `F_{h'}`, `h' ∉ Q`, is a global complete intersection over `κ(p)`.
2. With (1), (2) and step 1, the syntomic-at-a-prime lemma gives `g ∉ q` and an
`R`-isomorphism of `S_g` with a relative global complete intersection
`T = R[x_1,…,x_n]/(f_1,…,f_c)`, and the prime `q_T` corresponding to `q`.
3. The fibre `F_T = T ⊗_R κ(p)` is `κ(p)[x]/(f̄)` and is `F_{ḡ}`, matching `Q_T` with `Q`.
4. `κ(p) → F_T` is a relative global complete intersection smooth at `Q_T`.
5. The Jacobian criterion gives a maximal minor `g_I` with `ḡ_I ⊗ 1 ∉ Q_T`.
6. Hence `ḡ_I ∉ q_T` and the Jacobian criterion for `R → T` gives `t ∉ q_T` with `T_t` smooth.
7. Writing `θ⁻¹(t) = s/g^m`, `S_{gs} ≅ T_t` is smooth with `gs ∉ q`. -/
theorem flat_smooth_fibre_smooth_at_prime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ Algebra.FinitePresentation R (Localization.Away g))
    (hflat : (Localization.localRingHom (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
      q.asIdeal (algebraMap R S) rfl).Flat)
    (hsmooth : Algebra.IsSmoothAtPrime (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
      (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q) ⟨q, rfl⟩)) :
    Algebra.IsSmoothAtPrime R q := by
  sorry
