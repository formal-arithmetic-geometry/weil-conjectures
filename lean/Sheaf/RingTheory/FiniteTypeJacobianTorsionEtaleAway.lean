module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent
import WeilConjectures.RingTheory.EtaleRingMapConormalCriterion
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Ordinary Jacobian torsion away from an ideal

Source: Stacks Project, restricted.tex, Tag 0ALQ (lemma-rig-etale), converse paragraph
(blueprint: lem-per-finite-type-jacobian-torsion-etale-away).
-/

set_option autoImplicit false

@[expose] public section

universe u

open AlgebraicGeometry

namespace Algebra.Generators

/-- The kernel and cokernel of the polynomial conormal differential are killed by
one common power of the base ideal when the algebra is etale off its zero locus.

`P` is the chosen finite polynomial surjection, bundled with a section. Its conormal
module is `P.toExtension.Cotangent = K/K²`. The identity-index specialization of
`cotangentRestrict` is the full differential to `Fin r →₀ S`, not a projection onto
fewer coordinates: `cotangentRestrict_mk` gives its coordinates as the images of
formal partial derivatives. Thus its target is precisely the direct sum in the node.

Source: Stacks Project, restricted.tex, Tag 0ALQ (lemma-rig-etale), converse paragraph
(blueprint: lem-per-finite-type-jacobian-torsion-etale-away).

Proof:
1. By lem-weil-pbc-finite-type-algebra-noetherian, the polynomial ring and S are
Noetherian. Its kernel K is finitely generated (def-weil-pbc-noetherian-ring), so
K/K² and the finite free target are finite S-modules. Their kernel and cokernel
are finite by lem-pc-noetherian-finite-kernels-cokernels. Choose finite generating
lists using def-weil-finitely-generated-module.
2. For a in I, lem-weil-pbc-principal-localization-open-immersion identifies Spec S_a
with the inverse image of D(a). The hypothesis, lem-a1-etale-open-restriction, and
lem-weil-pbc-etale-composition-cancellation make S_a etale over A. Apply
lem-weil-pbc-etale-ring-map-conormal-criterion to the presentation obtained by adding
az-1. The polynomial differential basis (lem-weil-pbc-polynomial-ring-kahler-basis)
and lem-weil-pbc-principal-localization-naive-cotangent identify its conormal complex
with the localized original complex plus the acyclic unit-multiplication summand.
Thus the localized original differential is bijective. Localizing its two short
exact sequences by lem-sc-p1-localization-short-exact kills both homology modules.
3. Write I = (a_1,...,a_m). The zero-fraction criterion in
 def-weil-pbc-module-localization-away gives a power of each a_j killing every
member of each finite generating list. Choose e_j >= 1 uniformly over both lists.
Then a_j^e_j kills both modules. For m = 0 take c = 1. Otherwise take
c = 1 + sum_j (e_j - 1). Every degree-c monomial in the a_j contains some a_j^e_j,
so every element of I^c kills both modules. All actions are through A → S. -/
theorem finite_type_jacobian_torsion_etale_away
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing A] (I : Ideal A)
    (hfinite : (algebraMap A S).FiniteType)
    (hetale : AlgebraicGeometry.Etale
      ((Spec.map (CommRingCat.ofHom (algebraMap A S))) ∣_
        ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
          (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩))
    (r : ℕ) (P : Generators A S (Fin r)) :
    ∃ c : ℕ, ∀ a ∈ I ^ c,
      (∀ x : LinearMap.ker (P.cotangentRestrict (u := _root_.id) Function.injective_id),
        algebraMap A S a • x = 0) ∧
      (∀ x : (Fin r →₀ S) ⧸
          LinearMap.range (P.cotangentRestrict (u := _root_.id) Function.injective_id),
        algebraMap A S a • x = 0) := by
  sorry

end Algebra.Generators
