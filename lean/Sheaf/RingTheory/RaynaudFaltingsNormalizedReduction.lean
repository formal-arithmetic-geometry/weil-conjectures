module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.RingTheory.IntegralClosureFiniteNormalProduct
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import WeilConjectures.RingTheory.NagataUniversallyJapanese
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

/-!
# Raynaud--Faltings normalized affine reduction

Source: Prasad--Yu, On quasi-reductive group schemes, Appendix Theorem A.2 and
Remark A.3, printed pp.27--28; Stacks Project, Tag 09IL
(blueprint: lem-sfb-raynaud-faltings-normalized-reduction).

Write R = integralClosure D L and E_R = R tensor_D E. The generic ring is written
E_R tensor_R L, canonically isomorphic to (E tensor_D F) tensor_F L by tensor
associativity and cancellation of scalar extension. Special fibres are written
(R/n) tensor_R C, canonically C/nC. These choices retain the canonical maps.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- The actual scalar extension E_R, with R the actual integral closure of D in L.
Source: Prasad--Yu, Appendix Theorem A.2; Stacks Project, setup before Tag 09IL
(blueprint: lem-sfb-raynaud-faltings-normalized-reduction). -/
abbrev normalizedReductionBase (D : Type u) (E : Type v) (L : Type w)
    [CommRing D] [CommRing E] [CommRing L] [Algebra D E] [Algebra D L] :=
  (integralClosure D L) ⊗[D] E

/-- The generic scalar extension of E_R, identified with E_F tensor_F L.
Source: Prasad--Yu, Appendix Theorem A.2; Stacks Project, setup before Tag 09IL
(blueprint: lem-sfb-raynaud-faltings-normalized-reduction). -/
abbrev normalizedReductionGeneric (D : Type u) (E : Type v) (L : Type w)
    [CommRing D] [CommRing E] [CommRing L] [Algebra D E] [Algebra D L] :=
  (normalizedReductionBase D E L) ⊗[integralClosure D L] L

/-- The integral closure of E_R inside its generic scalar extension; membership is
integrality, not a choice of a normal model.
Source: Prasad--Yu, Appendix Theorem A.2; Stacks Project, setup before Tag 09IL
(blueprint: lem-sfb-raynaud-faltings-normalized-reduction). -/
abbrev normalizedReductionClosure (D : Type u) (E : Type v) (L : Type w)
    [CommRing D] [CommRing E] [CommRing L] [Algebra D E] [Algebra D L] :=
  integralClosure (normalizedReductionBase D E L) (normalizedReductionGeneric D E L)

/-- The canonical generic-fibre map c tensor l ↦ c*l, from the inclusion of the
integral closure and the right scalar inclusion into its ambient generic ring.
Source: Prasad--Yu, Appendix Theorem A.2; Stacks Project, setup before Tag 09IL
(blueprint: lem-sfb-raynaud-faltings-normalized-reduction). -/
noncomputable def normalizedReductionGenericMap (D : Type u) (E : Type v) (L : Type w)
    [CommRing D] [CommRing E] [CommRing L] [Algebra D E] [Algebra D L] :
    (normalizedReductionClosure D E L) ⊗[integralClosure D L] L →ₐ[integralClosure D L]
      normalizedReductionGeneric D E L :=
  Algebra.TensorProduct.productMap
    ((normalizedReductionClosure D E L).val.restrictScalars (integralClosure D L))
    Algebra.TensorProduct.includeRight

/-- A finite extension of the fraction field makes normalized affine base change
finite, flat, normal, generically unchanged, and geometrically reduced on every
special fibre. No separability, nonzero-algebra or nonempty-special-fibre
hypothesis is imposed.

Source: Prasad--Yu, Appendix Theorem A.2 and Remark A.3, printed pp.27--28;
Stacks Project, Tag 09IL (blueprint: lem-sfb-raynaud-faltings-normalized-reduction).

Proof (the nine steps of the node):
1. A uniformizer pi of D acts injectively on E by flatness; thus E embeds in E_F.
   Normality of E_F makes E reduced. For E = 0 take L = F and C = 0.
2. For any complete DVR V and flat finite-type A with normal generic ring A_K,
   A is reduced Noetherian. Its total fraction ring is the finite product of
   fraction fields of its minimal components (reduced-noetherian-total-ring-fractions).
   V is Nagata (complete-local-nagata), and Nagata rings are universally Japanese
   (nagata-universally-japanese). Each component therefore has finite normalization;
   multiplying the finitely many monic equations identifies their product with
   the integral closure, which is finite over A.
3. The total fraction ring is unchanged on inverting pi_V. Normality of A_K puts
   the normalization inside A_K (normal-ring-integrally-closed-total). It is exactly
   the closure there, and is normal by integral-closure-finite-normal-product and
   reduced-normal-iff-integrally-closed-total-fractions. Finite-algebra-noetherian
   gives Noetherianity. Torsion freeness inside A_K gives flatness over the PID V
   (pid-torsion-free-module-flat). Inverting pi_V recovers A_K. Call this ring N for E/D.
4. Decompose N into finitely many normal domains. The finitely many primes minimal
   over pi (finite-minimal-primes-over-ideal) have height one by the principal ideal
   height bound. Their local rings T_i are DVRs (normal-dim1-dvr). Apply
   epp-essentially-finite-type-traits to D -> T_i, obtaining finite extensions F_i/F.
5. Complete-dvr-finite-normalization gives complete DVRs R_i finite over D.
   Epp-common-finite-trait-extension gives a common finite complete DVR extension R;
   put L = Frac(R). Uniqueness identifies R with the integral closure of D in L.
   If the family is empty use R = D and L = F. Epp's conclusion persists over L.
6. Apply steps 2--3 to E_R/R: base change preserves flatness and finite type;
   geometric normality supplies normality of its generic ring. This gives exactly C,
   finite over E_R, finite type and flat over R, normal, with the stated generic map
   bijective. N tensor_D R is integral over E_R and embeds in the same generic ring;
   transitivity of integrality identifies its closure with C, finite also over N.
7. A height-one vertical prime q in a normal domain component C_b contracts to a
   height-one vertical prime p_i of a component N_j. Flat going down on generic
   scalar extension gives dominance on components; going-down-normal-integral gives
   height at most one, and the uniformizer in the contraction gives height at least one.
8. Integral-closure-commutes-localization identifies the localization at N_j minus
   p_i with the closure of T_i tensor_D R in Frac(T_i) tensor_F L. Integral-transitive
   identifies this with Epp's ring B_L. At q the Epp conclusion says rho generates
   the maximal ideal and the residue field is geometrically reduced over R/(rho).
9. Normal-domain-principal-quotient-associated-height puts all associated primes of
   C_b/rho C_b in height one; they are among finitely many minimal primes over rho.
   Module-injects-localizations-associated-primes embeds this quotient in the finite
   product of the fields from step 8. Tensor with any residue-field extension Omega:
   module-over-field-flat and flat-tensor-preserves-injection preserve the injection.
   Tensor commutes with finite products; each factor is reduced, so every nilpotent
   vanishes. The finite product over b proves the special-fibre assertion. A DVR has
   one maximal ideal, giving the assertion for every maximal n. Empty fibres are allowed.
-/
theorem exists_raynaudFaltings_normalized_reduction
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (F : Type v) [Field F] [Algebra D F] [IsFractionRing D F]
    (E : Type w) [CommRing E] [Algebra D E] [FiniteType D E] [Module.Flat D E]
    (hgeneric : ∀ (K : Type (max u v w)) [Field K] [Algebra F K],
      ∀ (p : Ideal (K ⊗[F] (F ⊗[D] E))) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∃ (L : Type (max u v w)) (_ : Field L) (_ : Algebra F L) (_ : Algebra D L)
      (_ : IsScalarTower D F L),
      FiniteDimensional F L ∧
      Module.Finite (normalizedReductionBase D E L) (normalizedReductionClosure D E L) ∧
      FiniteType (integralClosure D L) (normalizedReductionClosure D E L) ∧
      Module.Flat (integralClosure D L) (normalizedReductionClosure D E L) ∧
      (∀ (p : Ideal (normalizedReductionClosure D E L)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      Function.Bijective (normalizedReductionGenericMap D E L) ∧
      (∀ (n : Ideal (integralClosure D L)) [n.IsMaximal],
        ∀ (Ω : Type (max u v w)) [Field Ω] [Algebra ((integralClosure D L) ⧸ n) Ω],
          IsReduced (Ω ⊗[(integralClosure D L) ⧸ n]
            (((integralClosure D L) ⧸ n) ⊗[integralClosure D L]
              (normalizedReductionClosure D E L)))) := by
  sorry

end Algebra
