/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.PolynomialOriginRegularLocal
import Sheaf.RingTheory.FlatOverRegular
import Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian

/-!
# Selecting polynomial parameters in a regular closed fibre

Source: Stacks Project, Smoothing Ring Maps, Tag 07FH, lemma-solution-modulo,
parameter selection for property (1); Algebra, Tags 00NQ, 00OP, 07DY and 00MP.
-/

@[expose] public section

set_option autoImplicit false
universe u v
namespace Algebra

/-- For an initially flat polynomial coordinate map with regular local closed fibre,
a subset of given maximal-ideal generators gives a flat appended map. The selected
parameters generate the maximal ideal modulo the first-coordinate ideal.
Source: Stacks Project, Tag 07FH, lemma-solution-modulo, selection of parameters
for property (1); Algebra, Tags 00NQ, 00OP, 07DY and 00MP.
(blueprint: lem-weil-pbc-flat-regular-fibre-parameter-selection).

Proof: Write L = Λ_q, A₀ = k[X_j] at the contracted prime, and I₀ for the
extended prime in L. The quotient S = L/I₀ is regular local by hfibre. The images
of ys generate its maximal ideal. In its cotangent space choose a basis from
these finitely many generators and let s index that subset. Nakayama implies
that these selected images generate the maximal ideal of S. Their number equals
its embedding dimension, which equals its Krull dimension by regular locality.
They are a regular system of parameters, hence a regular sequence by 00NQ.
Lifting their generation from S gives m_L = I₀ + (ys (s i)/1).

Append the selected coordinates, obtaining A₁, the localization of k[X_j,Y_i]
at its contracted prime. The maps A₀ → A₁ → L are local and all three rings are
Noetherian. The closed fibre of A₀ → A₁ is κ(p₀)[Y_i] localized at its origin:
the added variables lie in the contracted prime, and their ideal is already
maximal over κ(p₀). By 00OP this fibre is regular local of dimension e, with the
Y_i as parameters. The map of closed fibres sends them to the selected regular
sequence in S, so 07DY gives fibre flatness. Apply 00MP with base A₀, middle A₁,
target L and finite nonzero L-module L, using hflat for its flatness over A₀.
It gives flatness over A₁. The induced map is the canonical localRingHom by
uniqueness of localization. If S is a field, take e = 0; if r = 0, the given
maximal ideal is zero and this case applies. Repeated generators cause no
problem because a basis is extracted from the spanning family. -/
theorem exists_flat_regular_fibre_parameter_selection
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (q : Ideal Λ) [q.IsPrime]
    (t r : ℕ) (xs : Fin t → Λ) (ys : Fin r → Λ)
    (hyq : ∀ i, ys i ∈ q)
    (hys : Ideal.span (Set.range (fun i ↦ algebraMap Λ (Localization.AtPrime q) (ys i))) =
      q.map (algebraMap Λ (Localization.AtPrime q)))
    (hflat : (Localization.localRingHom
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom) q
      (MvPolynomial.aeval (R := k) xs).toRingHom rfl).Flat)
    (hfibre : IsRegularLocalRing (Localization.AtPrime q ⧸
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp
          (MvPolynomial.aeval (R := k) xs).toRingHom))) :
    ∃ (e : ℕ) (s : Fin e → Fin r),
      let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
        MvPolynomial.aeval (Fin.addCases xs (fun i ↦ ys (s i)))
      (Localization.localRingHom (q.comap φ.toRingHom) q φ.toRingHom rfl).Flat ∧
        q.map (algebraMap Λ (Localization.AtPrime q)) =
          (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
              ((algebraMap Λ (Localization.AtPrime q)).comp
                (MvPolynomial.aeval (R := k) xs).toRingHom) ⊔
            Ideal.span (Set.range (fun i ↦
              algebraMap Λ (Localization.AtPrime q) (ys (s i)))) := by sorry

end Algebra
