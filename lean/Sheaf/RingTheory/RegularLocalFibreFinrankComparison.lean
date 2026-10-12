module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Sheaf.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

import Sheaf.FieldTheory.SeparablyGeneratedDifferentialsDimension
import Sheaf.Paper.SeparableResidueCotangentInjective
import Mathlib.RingTheory.Etale.Kaehler

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra


/-- Conormal decomposition with an explicit finite function-space summand.
(blueprint: lem-weil-pbc-regular-local-fibre-finrank-add-fin-fun)

Proof: use the conormal exact sequence, separable residue injectivity, localization,
and the separating transcendence basis differential basis. -/
theorem fibre_finrank_eq_cotangent_finrank_add_fin_fun
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField)
    (r : ℕ) (hr : Algebra.trdeg k q.ResidueField = (r : Cardinal.{v})) :
    Module.finrank q.ResidueField (q.ResidueField ⊗[S] KaehlerDifferential k S) =
      Module.finrank q.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime q)) +
        Module.finrank q.ResidueField (Fin r → q.ResidueField) := by
  sorry

/-- The residue-field fibre of the differentials has dimension equal to the embedding
dimension plus the residue-field transcendence degree.
Source: Stacks Project, Algebra, proof of Lemma Tag 00TV, using Tag 00TU.
(blueprint: lem-weil-pbc-regular-local-fibre-finrank-comparison).

Proof:
Put R = S_q and K = kappa(q). Finite type over k makes R Noetherian and K finitely
generated as a field. Its maximal ideal m is finitely generated, so m/m^2 is finite
dimensional over K. The quotient conormal sequence
m/m^2 -> K tensor_R Omega[R/k] -> Omega[K/k] -> 0 is right exact.
Separability of K/k makes the first map injective by Tag 00TU. A separating
transcendence basis of K/k has r elements by hr; its differentials form a basis
 of Omega[K/k], since the remaining algebraic extension is finite separable.
Thus the outer terms are finite dimensional, and short-exact-sequence dimension
additivity gives dimension of the middle term equal to dim_K(m/m^2) + r.
Localization of differentials gives Omega[R/k] = R tensor_S Omega[S/k]. Tensor
associativity identifies K tensor_R Omega[R/k] with K tensor_S Omega[S/k].
The canonical residue-field identification identifies m/m^2 with the cotangent
space of R, including its K scalar action. Transporting finranks proves the formula.
-/
theorem fibre_finrank_eq_cotangent_finrank_add
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField)
    (r : ℕ) (hr : Algebra.trdeg k q.ResidueField = (r : Cardinal.{v})) :
    Module.finrank q.ResidueField (q.ResidueField ⊗[S] KaehlerDifferential k S) =
      Module.finrank q.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime q)) + r := by
  rw [fibre_finrank_eq_cotangent_finrank_add_fin_fun k S q hsep r hr]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

end Algebra
