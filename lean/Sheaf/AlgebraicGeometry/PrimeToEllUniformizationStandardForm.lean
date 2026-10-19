/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.AlterationCoverStandardRefinement
import Sheaf.AlgebraicGeometry.GabberPrimeToEllRegularCover

/-!
# Prime-to-ell uniformization in standard form

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, IX Theorem 1.1,
II Theorem 3.2.3, and XIII 3.2.1, printed p. 199
(blueprint: lem-per-prime-to-ell-uniformization-standard-form).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Prime-to-ell uniformization produces a proper modification, a finite completely decomposed
family of étale maps, positive prime-to-ell finite locally free covers, and maps to a finite
disjoint union of regular pairs. Source: ILO IX Theorem 1.1, II Theorem 3.2.3,
and XIII 3.2.1 (blueprint: lem-per-prime-to-ell-uniformization-standard-form).

Proof:
1. Put `Z = X ∖ U`. It is closed and nowhere dense. Integrality implies reducedness;
   the remaining hypotheses are exactly those of the regular-cover theorem.
2. Apply `lem-per-gabber-prime-to-ell-regular-cover` to `(X, Z, ell)`. It gives a finite
   prime-to-ell alteration cover `q_b : Y_b → X` by regular Noetherian schemes and strict
   normal crossings boundaries whose supports are `q_b⁻¹(Z)`. Their complements are the
   inverse images of `U`.
3. Apply `lem-per-alteration-cover-standard-refinement` to that cover. It gives the integral
   modification `p`, the finite completely decomposed separated étale family `e_i`, and the
   finite locally free surjections `a_i` of positive constant ranks coprime to `ell`, together
   with maps `W_i → Y_b(i)` over `X`. It also supplies all the finite type assertions and
   the isomorphism of `p` over a dense open.
4. Form the scheme coproduct of the `Y_b`, with structure map `Sigma.desc q`. Compose each
   map from Step 3 with its summand inclusion. The resulting maps commute with the maps to
   `X`, and the boundaries on the retained `Y_b` are unchanged. -/
theorem primeToEll_uniformization_standard_form
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : ∀ V : X.affineOpens, IsQuasiExcellent Γ(X, V.1))
    (ell : ℕ) (hell : ell.Prime)
    (hinv : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ X)
      (n m : ℕ) (E W : Fin n → Scheme.{u}) (Y : Fin m → Scheme.{u})
      (e : ∀ i, E i ⟶ X') (a : ∀ i, W i ⟶ E i) (r : Fin n → ℕ)
      (q : ∀ b, Y b ⟶ X) (h : ∀ i, W i ⟶ ∐ Y),
      IsIntegral X' ∧ IsProper p ∧
      (∃ V : X.Opens, Dense (V : Set X) ∧ IsIso (p ∣_ V)) ∧
      (LocallyOfFiniteType p ∧ QuasiCompact p) ∧
      (∀ i, IsSeparated (e i) ∧ Etale (e i) ∧
        LocallyOfFiniteType (e i) ∧ QuasiCompact (e i)) ∧
      (∀ i, (a i).IsFiniteLocallyFreeOfDegree (r i) ∧
        Surjective (a i) ∧ 0 < r i ∧ Nat.Coprime (r i) ell) ∧
      (∀ i, LocallyOfFiniteType (e i ≫ p) ∧ QuasiCompact (e i ≫ p)) ∧
      (∀ i, LocallyOfFiniteType (a i ≫ e i ≫ p) ∧ QuasiCompact (a i ≫ e i ≫ p)) ∧
      (∀ b, IsRegularScheme (Y b) ∧ IsNoetherian (Y b) ∧
        LocallyOfFiniteType (q b) ∧ QuasiCompact (q b)) ∧
      (∀ x' : X', ∃ (i : Fin n) (z : E i),
        e i z = x' ∧ IsIso ((e i).residueFieldMap z)) ∧
      (∀ i, h i ≫ Sigma.desc q = a i ≫ e i ≫ p) ∧
      (∀ b, ∃ H : (Y b).IdealSheafData,
        IsStrictNormalCrossingsBoundary H ∧
        (q b) ⁻¹' (U : Set X) = (H.support : Set (Y b))ᶜ) := by
  sorry

end AlgebraicGeometry
