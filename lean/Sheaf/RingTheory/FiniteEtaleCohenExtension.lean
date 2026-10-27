module

public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Category.CommAlgCat.Basic

import Mathlib.RingTheory.Henselian
import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.HenselianFiniteEtaleFieldLift
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import Sheaf.RingTheory.HenselianFiniteEtaleMapBijective

/-! # Finite étale extensions of Cohen rings

Source: Stacks Project, Algebra, Tag 04GK, specialized using Definition Tag 0327;
ILO IV 4.3.5, printed p.60 (blueprint: lem-per-finite-etale-cohen-extension).
-/

@[expose] public section

universe u v w

namespace IsCohenRing

/-- A finite separable extension of the residue field of a Cohen ring lifts to a finite
étale Cohen extension, and reduction identifies their automorphism groups.
The identification `eF` presents the named residue field as `D / pD`. The algebra map
is the requested local injection. The final equation specifies reduction, transported
by `e`, on every element, so the group equivalence is the canonical reduction map.

Source: Stacks Project, Algebra, Tag 04GK; ILO IV 4.3.5, printed p.60
(blueprint: lem-per-finite-etale-cohen-extension).

Proof:
1. The Cohen ring D is a DVR with maximal ideal pD, complete for that ideal.
   By lem-weil-pbc-complete-pair-henselian it is henselian. Apply
   lem-weil-pbc-henselian-finite-etale-field-lift to obtain a finite étale D-algebra B
   with the specified residue field. Identify (D/pD) tensor_D B with B/pB by
   a tensor b mapping to i(a)b modulo pB, with inverse b mapping to 1 tensor b.
2. By lem-weil-pbc-etale-algebra-flat, B is flat over D. The theorem
   lem-weil-pbc-finite-flat-local-free gives a basis. Its indices are finite because
   the supports of a finite generating set cover them, and nonempty because B/pB is L.
3. Apply lem-sfb-finite-free-field-fibre-dvr: i is injective, B is a DVR, and its
   maximal ideal is pB. The prescribed injective residue map shows i is local.
4. By lem-weil-pbc-pid-noetherian-normal, D is Noetherian. The domain clause of
   lem-weil-pbc-finite-over-complete-local-product makes B complete at its maximal
   ideal pB. Thus B is a Cohen ring with the same prime p.
5. Apply lem-weil-pbc-henselian-finite-etale-map-bijective to B twice. Lift a residue
   automorphism and its inverse uniquely; their composites reduce to the identity,
   hence equal the identity by injectivity of reduction on Hom. Thus reduction is
   bijective on automorphisms. It respects composition, as does conjugation by e. -/
theorem exists_finiteEtale_extension
    (p : ℕ) (D : Type u) [CommRing D] (hD : IsCohenRing p D)
    (F : Type v) [Field F] (eF : (D ⧸ Ideal.span {(p : D)}) ≃+* F)
    (L : Type (max u v w)) [Field L] [Algebra F L]
    [Module.Finite F L] [Algebra.IsSeparable F L] :
    ∃ B : CommAlgCat.{max u v w} D,
      IsCohenRing p B ∧ Function.Injective (algebraMap D B) ∧
        IsLocalHom (algebraMap D B) ∧ Module.Finite D B ∧ Algebra.Etale D B ∧
        ∃ e : (B ⧸ Ideal.span {(p : B)}) ≃+* L,
          (∀ d : D, e (Ideal.Quotient.mk _ (algebraMap D B d)) =
            algebraMap F L (eF (Ideal.Quotient.mk _ d))) ∧
          ∃ ρ : (B ≃ₐ[D] B) ≃* (L ≃ₐ[F] L),
            ∀ (α : B ≃ₐ[D] B) (b : B),
              ρ α (e (Ideal.Quotient.mk _ b)) = e (Ideal.Quotient.mk _ (α b)) := by
  sorry

end IsCohenRing
