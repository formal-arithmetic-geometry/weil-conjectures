module

public import Sheaf.GroupTheory.BrauerElementary
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Character
import Sheaf.RepresentationTheory.FiniteGroupInductionCalculus
import Sheaf.RepresentationTheory.InducedCharacterConjugacyFormula

/-! # The elementary induction identity for the complex unit character

Source: accepted auxiliary character-ring proof under latest blueprint
lem-per-artin-gabber-affine-curve, Step 3. ILO, Exposé X, Proposition 1.2, printed p.138,
is representation-theoretic motivation only. Serre, Linear Representations of Finite Groups,
Part II, Chapter 10, §§10.2–10.3 is wanted.
(blueprint: lem-per-brauer-elementary-unit-character)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Representation

/-- The constant unit character is an integral sum of characters induced from elementary
subgroups. Bundled complex modules supply the vector spaces, and `Module.Finite`
states their finite-dimensionality without choosing bases or dimensions.

The quotient is Mathlib's `IndV`. Write `[g,w]` for `IndV.mk E.subtype ρ g⁻¹ w`.
Its diagonal coinvariant relation is `[ge,w]=[g,ρ e w]`; `ind_mk` gives
`a [g,w]=[ag,w]`. Sending a generator at x to `[x⁻¹,w]` is the inverse quotient
identification, so this is precisely the induction convention of the node.

Source: accepted seven-step auxiliary proof, with ILO X 1.2, printed p.138 as motivation;
Serre II, Chapter 10, §§10.2–10.3 is wanted.
(blueprint: lem-per-brauer-elementary-unit-character)

Proof plan:
1. Set N=|G|. By lem-per-cyclotomic-integer-power-basis choose a primitive root ζ and
   the integral power basis of A=O_{ℚ(ζ)}. The coefficient-of-1 map t:A→ℤ is additive,
   ℤ-linear, and sends 1 to 1. By lem-per-character-prime-part-reduction characters lie in A.
2. Let B be the A-span of complex characters in A^G. Direct sums and tensor products
   make B a unital ring. The A-span J of elementary induced characters is an ideal by
   the tensor identity in lem-per-finite-group-induction-calculus. Complex algebraic
   closure is lem-weil-complex-algebraically-closed; ℂ has characteristic zero.
3. If J is proper, lem-per-finite-function-subring-residue-test gives evaluation at g
   followed by reduction modulo a maximal ideal q of A annihilating J. Its residue
   field has prime characteristic p. By lem-per-character-prime-part-reduction write
   g=su with commuting prime-to-p and p-power parts. Every f∈J has f(s)=0 modulo q.
4. In D=C_G(s), C=⟨s⟩ is central of prime-to-p order m. Choose a Sylow p-subgroup P
   by lem-weil-pbc-sylow-subgroup-prime-index. Then C∩P=1 and E=CP≅C×P is elementary.
   The integer c₀=[D:E] is prime to p, since [D:P]=m c₀ is prime to p.
5. Put S=C∩s^G and ξ=ζ^(N/m). For 0≤j<m define λ_j(s^a v)=ξ^(ja) on E=C×P,
   and a_j=∑_{s^a∈S} ξ^(ja). Finite geometric sums give ∑_j ξ^(-j)a_j=m, since
   s∈S. Hence some a_j is nonzero modulo q. This includes m=1.
6. Every element of E conjugate to s has trivial P-component, so E∩s^G=S.
   By lem-per-induced-character-conjugacy-formula the character induced from λ_j at s
   is c₀a_j, nonzero modulo q, contradicting step 3. Thus J=B and 1=∑_i b_i χ_{U_i}
   for U_i=Ind_{E_i}^G W_i and b_i∈A.
7. By lem-per-finite-group-character-decomposition decompose the U_i into a finite
   common list of irreducibles, including the trivial line T₀. Pair with χ_T(g⁻¹)
   and use lem-per-finite-group-character-orthogonality to obtain ∑_i b_i m_{iT}=δ_{T,T₀}.
   Apply t to these multiplicity equalities, then multiply by χ_T and sum. This gives
   1=∑_i t(b_i)χ_{U_i}. The map t is never applied to products of arbitrary character
   values. All sums are finite and the coefficients t(b_i) are integers.
-/
theorem brauer_elementary_unit_character (G : Type u) [Group G] [Finite G] :
    ∃ (n : ℕ) (E : Fin n → Subgroup G) (W : Fin n → ModuleCat.{v} ℂ)
      (ρ : (i : Fin n) → Representation ℂ (E i) (W i)) (a : Fin n → ℤ),
      (∀ i, Group.IsBrauerElementary (E i)) ∧ (∀ i, Module.Finite ℂ (W i)) ∧
        ∀ g : G, (1 : ℂ) = ∑ i, (a i : ℂ) *
          LinearMap.trace ℂ (IndV (E i).subtype (ρ i)) (ind (E i).subtype (ρ i) g) := by
  sorry

end Representation
