module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Basic

/-!
# Prime factors in a localized polynomial fibre

Source: Stacks Project, Algebra, Tag 00UF, proof of
`lemma-standard-etale-finite-flat-Zariski`, residue-field paragraph
(blueprint: lem-trf-localized-fibre-prime-factor).

`AdjoinRoot f` is exactly `R[X]/(f)`. The fibre below is localized at the image
of the class of `g` under the canonical quotient map; this is the class of
`g.map φ`. The two helper definitions only compose Mathlib's canonical maps
and ideal extensions.
-/

@[expose] public section

universe u v

namespace AdjoinRoot

/-- The canonical map `(R[X]/(f))[1/g] → (S[X]/(f.map φ))[1/(g.map φ)]`.
The target is written using the image of the class of `g` under `AdjoinRoot.map`.
Source: Stacks Project, Algebra, Tag 00UF, residue-field paragraph
(blueprint: lem-trf-localized-fibre-prime-factor). -/
noncomputable def localizedMap {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (f g : Polynomial R) :
    Localization.Away (AdjoinRoot.mk f g) →+*
      Localization.Away
        (AdjoinRoot.map φ f (f.map φ) (dvd_refl (f.map φ)) (AdjoinRoot.mk f g)) :=
  Localization.awayMap (AdjoinRoot.map φ f (f.map φ) (dvd_refl (f.map φ)))
    (AdjoinRoot.mk f g)

/-- The ideal `((h)/(f.map φ))F`: first map `(h)` to `S[X]/(f.map φ)`, then
extend it to the localization at the image of `g`.
Source: Stacks Project, Algebra, Tag 00UF, residue-field paragraph
(blueprint: lem-trf-localized-fibre-prime-factor). -/
noncomputable def localizedFactorIdeal {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (f g : Polynomial R) (h : Polynomial S) :
    Ideal (Localization.Away
      (AdjoinRoot.map φ f (f.map φ) (dvd_refl (f.map φ)) (AdjoinRoot.mk f g))) :=
  Ideal.map (algebraMap (AdjoinRoot (f.map φ))
    (Localization.Away
      (AdjoinRoot.map φ f (f.map φ) (dvd_refl (f.map φ)) (AdjoinRoot.mk f g))))
    (Ideal.map (AdjoinRoot.mk (f.map φ)) (Ideal.span {h}))

/-- A prime of a localized monic polynomial quotient is the contraction of the
ideal of exactly one monic irreducible factor over its base residue field, and
membership of every fraction is divisibility of its reduced numerator.
Source: Stacks Project, Algebra, Tag 00UF, residue-field paragraph
(blueprint: lem-trf-localized-fibre-prime-factor).

Proof plan (the eight steps of the node):
1. Map `B` to `L = κ(q)`. Its kernel is `q`, by the fraction equality rule and
   primality (def-weil-pbc-localization-at-prime). The composite from `R` has
   kernel `p`, and all denominators outside `p` have nonzero image.
2. Embed `κ(p)` in `L` using `r/s ↦ τ(r)/τ(s)` and evaluate polynomials at the
   image of `X`. This gives a prime kernel `Q` containing `f_k` but avoiding `g_k`.
   Monicity makes `f_k` nonzero (def-weil-polynomial-ring,
   def-weil-ring-localization-away, def-weil-pbc-localization-at-prime).
3. The field polynomial ring is a PID (lem-pur-polynomial-field-pid), so
   `Q = (d)` for a nonzero nonunit polynomial `d`.
4. Divide `d` by its leading coefficient to obtain monic `h`. Primality of `(h)`
   and cancellation show irreducibility; membership gives `h ∣ f_k`, `h ∤ g_k`
   (def-weil-polynomial-ring).
5. Evaluate `[P]/g^m` in `L`. Its nonzero denominator shows that it belongs to
   `q` exactly when `h` divides `P.map (algebraMap R κ(p))`, including `m = 0`
   (def-weil-ring-localization-away).
6. Evaluation on the fibre has kernel the extension of the image of `(h)`:
   a fraction evaluates to zero exactly when its numerator is divisible by `h`.
   Its composite with the canonical map is `τ`, giving the ideal contraction
   (def-weil-ring-localization-away).
7. Any other candidate `h'` is coprime to `g_k` (def-weil-coprime-polynomials).
   Cancel powers of `g_k` using lem-weil-coprime-divides-product and the
   localization fraction equality rule. Its contraction therefore gives the same
   divisibility test on every reduced polynomial from `R[X]`.
8. Clear the finitely many coefficient denominators of an arbitrary polynomial
   over `κ(p)` (def-weil-pbc-localization-at-prime, def-weil-polynomial-ring).
   The common denominator is a nonzero scalar, so the divisibility tests agree
   on all polynomials. The candidates divide each other; monicity gives equality.
-/
theorem exists_unique_localized_fibre_prime_factor {R : Type u} [CommRing R]
    (f g : Polynomial R) (hf : f.Monic)
    (q : Ideal (Localization.Away (AdjoinRoot.mk f g))) [q.IsPrime]
    (p : Ideal R) [p.IsPrime]
    (hp : p = Ideal.comap
      ((algebraMap (AdjoinRoot f) (Localization.Away (AdjoinRoot.mk f g))).comp
        (AdjoinRoot.of f)) q) :
    ∃ h : Polynomial p.ResidueField,
      h.Monic ∧ Irreducible h ∧
      h ∣ f.map (algebraMap R p.ResidueField) ∧
      ¬ h ∣ g.map (algebraMap R p.ResidueField) ∧
      q = Ideal.comap (localizedMap (algebraMap R p.ResidueField) f g)
        (localizedFactorIdeal (algebraMap R p.ResidueField) f g h) ∧
      (∀ (P : Polynomial R) (m : ℕ),
        Localization.mk (AdjoinRoot.mk f P)
          (⟨AdjoinRoot.mk f g ^ m, m, rfl⟩ : Submonoid.powers (AdjoinRoot.mk f g)) ∈ q ↔
            h ∣ P.map (algebraMap R p.ResidueField)) ∧
      (∀ h' : Polynomial p.ResidueField,
        h'.Monic → Irreducible h' →
        h' ∣ f.map (algebraMap R p.ResidueField) →
        ¬ h' ∣ g.map (algebraMap R p.ResidueField) →
        q = Ideal.comap (localizedMap (algebraMap R p.ResidueField) f g)
          (localizedFactorIdeal (algebraMap R p.ResidueField) f g h') →
        h' = h) := by
  sorry

end AdjoinRoot
