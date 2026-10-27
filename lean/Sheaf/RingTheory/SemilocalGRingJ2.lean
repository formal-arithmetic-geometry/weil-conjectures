module

public import Mathlib.RingTheory.LocalProperties.Semilocal
public import WeilConjectures.RingTheory.GRing
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Semilocal G-rings are quasi-excellent

Source: Kurano–Shimomoto, *Ideal-adic completion of quasi-excellent rings (after Gabber)*,
Section 2, printed p. 2 (blueprint: lem-per-semilocal-g-ring-j2).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A commutative Noetherian semilocal G-ring is quasi-excellent. The proof follows
Kurano–Shimomoto, Section 2, printed p. 2, using completions at the finitely many maximal
ideals, excellence of complete local rings, and faithfully flat descent of openness of the
regular locus (blueprint: lem-per-semilocal-g-ring-j2).

The proof is postponed. It handles the zero ring as well: `MaximalSpectrum A` may be empty,
and the J-2 quantification in `IsQuasiExcellent` is then vacuous where appropriate.

Proof (the nine steps of the node):
1. If `A = 0`, every `A`-algebra is zero and the open set is empty. Otherwise list the
   maximal ideals `mᵢ`, `i = 1, …, r`. Put `Rᵢ = A_{mᵢ}` and let `Cᵢ` be its
   `mᵢ`-adic completion. It is Noetherian, local, complete, hence excellent
   (`lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-local-completion-local-ring`,
   `lem-weil-pbc-adic-completion-mod-ideal`, `lem-per-complete-local-excellence`).
2. `A → Rᵢ` is regular (`lem-weil-pbc-localization-regular`), `Rᵢ → Cᵢ` is regular by
   the G-ring hypothesis, and the fibres of `A → Cᵢ` are Noetherian
   (`lem-weil-pbc-fibre-ring-noetherian`); so `A → Cᵢ` is regular, in particular flat
   (`lem-weil-pbc-regular-composition`).
3. `B = ∏ Cᵢ` is flat over `A` (`lem-weil-pbc-finite-product-flat-modules`), and
   `mᵢ B ≠ B` since `B → κ(mᵢ)` kills it; so `A → B` is faithfully flat
   (`lem-weil-pbc-flat-faithfully-flat-maximal-ideals`).
4. For a finite type `A`-algebra `D` put `Eᵢ = D ⊗_A Cᵢ`. It is of finite type over
   `Cᵢ`, Noetherian, and its regular locus is open by the J-2 clause of the excellence
   of `Cᵢ`. The map `D → Eᵢ` is regular (`lem-weil-pbc-regular-base-change`).
5. For `q ∈ Spec Eᵢ` over `p ∈ Spec D`, `D_p → (Eᵢ)_q` is a flat local homomorphism
   (`lem-weil-pbc-flat-local-ring-maps`); if `(Eᵢ)_q` is regular then so is `D_p`
   (`lem-weil-pbc-flat-under-regular`).
6. Conversely, if `D_p` is regular, the local map `D_p → (Eᵢ)_q` is regular
   (`lem-weil-pbc-regular-local-maximal`), its closed fibre is regular, so `(Eᵢ)_q` is
   regular (`lem-weil-pbc-flat-over-regular-with-regular-fibre`). Thus the inverse image
   of `Reg(D)` in `Spec Eᵢ` is `Reg(Eᵢ)`.
7. `E = D ⊗_A B ≅ ∏ Eᵢ`, so `Spec E` is the disjoint union of the open-and-closed
   `Spec Eᵢ` with the same local rings; hence the inverse image of `Reg(D)` under
   `g : Spec E → Spec D` is open.
8. `D → E` is faithfully flat (`lem-weil-pbc-faithfully-flat-base-change`), so `g` is
   flat, surjective and quasi-compact (`lem-weil-pbc-flat-ring-map-iff-flat-affine`,
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`, `lem-weil-pbc-affine-scheme-qcqs`),
   hence a quotient map (`lem-weil-pbc-flat-qc-surjective-quotient-map`); by step 7,
   `Reg(D)` is open.
9. `D` was arbitrary, so `A` is J-2; with Noetherianity and the G-ring property this is
   quasi-excellence (`def-exc-excellent-ring`), also in the zero-ring case of step 1. -/
theorem isQuasiExcellent_of_finite_maximalSpectrum
    (A : Type u) [CommRing A] [Finite (MaximalSpectrum A)]
    (hNoetherian : IsNoetherianRing A) (hG : IsGRing A) : IsQuasiExcellent A := by
  sorry
