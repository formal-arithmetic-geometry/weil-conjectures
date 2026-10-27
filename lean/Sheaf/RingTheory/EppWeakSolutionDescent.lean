module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Descent and composition of weak Epp solutions

Source: Stacks Project, More on Algebra, Tags 09EM, 09EN and 09ES, together with
iteration of the normalized tower argument (blueprint: lem-sfb-epp-weak-solution-descent).

The reduced generic tensor, its upper normalization and the canonical map between
the normalizations of Tag 09EM are stated here as `eppWeakReducedTensor`,
`eppWeakUpperClosure` and `eppWeakNormalizationMap`. They are the same terms as
`eppReducedTensor`, `eppUpperClosure` and `eppNormalizationMap` of
`Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`. That module is not imported:
its theorem node lem-sfb-epp-essentially-finite-type-traits lies downstream of this
node through lem-sfb-epp-weak-perfect-residue and lem-sfb-epp-finite-coefficient-triple.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z t s

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The reduced generic tensor algebra `(H ⊗_F M)_red`, quotienting by every
nilpotent element. Source: Stacks Project, More on Algebra, Tag 09EM
(blueprint: lem-sfb-epp-weak-solution-descent). -/
abbrev eppWeakReducedTensor (F : Type v) (H : Type x) (M : Type y)
    [Field F] [Field H] [Field M] [Algebra F H] [Algebra F M] :=
  (H ⊗[F] M) ⧸ nilradical (H ⊗[F] M)

/-- The actual integral closure of `T` in the reduced generic tensor algebra.
Source: Stacks Project, More on Algebra, Tag 09EM
(blueprint: lem-sfb-epp-weak-solution-descent). -/
abbrev eppWeakUpperClosure (T : Type w) (F : Type v) (H : Type x) (M : Type y)
    [CommRing T] [Field F] [Field H] [Field M]
    [Algebra T H] [Algebra F H] [Algebra F M] :=
  integralClosure T (eppWeakReducedTensor F H M)

/-- The canonical map between the lower and upper normalizations: the restriction
of `m ↦ 1 ⊗ m` followed by reduction, since monic equations over `D` remain monic
equations over `T`. Source: Stacks Project, More on Algebra, Tag 09EM
(blueprint: lem-sfb-epp-weak-solution-descent). -/
noncomputable def eppWeakNormalizationMap
    (D : Type u) (T : Type w) (F : Type v) (H : Type x) (M : Type y)
    [CommRing D] [CommRing T] [Field F] [Field H] [Field M]
    [Algebra D T] [Algebra D F] [Algebra D H] [Algebra T H] [Algebra F H]
    [IsScalarTower D T H] [IsScalarTower D F H]
    [Algebra F M] [Algebra D M] [IsScalarTower D F M] :
    integralClosure D M →+* eppWeakUpperClosure T F H M :=
  (((Ideal.Quotient.mkₐ F (nilradical (H ⊗[F] M))).comp
    Algebra.TensorProduct.includeRight).restrictScalars D |>.comp
      (integralClosure D M).val).codRestrict
        ((integralClosure T (eppWeakReducedTensor F H M)).restrictScalars D)
        (fun a ↦ (a.property.map
          (((Ideal.Quotient.mkₐ F (nilradical (H ⊗[F] M))).comp
            Algebra.TensorProduct.includeRight).restrictScalars D)).tower_top) |>.toRingHom

/-- The exact branch condition in the definition of a weak solution: maximal
contraction, two local DVRs, and equality of extended maximal ideals.
Source: Stacks Project, Tags 09EM and 09EN
(blueprint: lem-sfb-epp-weak-solution-descent). -/
def eppWeakBranch {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (q : Ideal S) [q.IsPrime] : Prop :=
  (q.comap f).IsMaximal ∧
  (∀ [_hn : (q.comap f).IsPrime], ∃ hd : IsDomain (Localization.AtPrime (q.comap f)),
    @IsDiscreteValuationRing (Localization.AtPrime (q.comap f)) _ hd) ∧
  (∃ hd : IsDomain (Localization.AtPrime q),
    @IsDiscreteValuationRing (Localization.AtPrime q) _ hd) ∧
  Ideal.map ((algebraMap S (Localization.AtPrime q)).comp f) (q.comap f) =
    Ideal.map (algebraMap S (Localization.AtPrime q)) q

/-- A finite coefficient extension is a weak solution precisely when every
maximal normalized branch satisfies `eppWeakBranch`.
Source: Stacks Project, Tags 09EM and 09EN
(blueprint: lem-sfb-epp-weak-solution-descent). -/
def eppIsWeakSolution
    (R : Type u) (S : Type v) (E : Type w) (Q : Type x) (E' : Type y)
    [CommRing R] [CommRing S] [Field E] [Field Q] [Field E']
    [Algebra R S] [Algebra R E] [Algebra S Q] [Algebra R Q] [Algebra E Q]
    [IsScalarTower R S Q] [IsScalarTower R E Q]
    [Algebra E E'] [Algebra R E'] [IsScalarTower R E E'] : Prop :=
  Module.Finite E E' ∧
  ∀ (q : Ideal (eppWeakUpperClosure S E Q E')) [q.IsMaximal],
    eppWeakBranch (eppWeakNormalizationMap R S E Q E') q

/-- The canonical map on reduced tensors for a coefficient extension; nilpotents
map to nilpotents. Source: Stacks Project, Tag 09ES, normalized tower proof
(blueprint: lem-sfb-epp-weak-solution-descent). -/
noncomputable def eppReducedCoefficientMap
    (E : Type u) (Q : Type v) (E₁ : Type w) (E₂ : Type x)
    [Field E] [Field Q] [Field E₁] [Field E₂]
    [Algebra E Q] [Algebra E E₁] [Algebra E E₂] [Algebra E₁ E₂]
    [IsScalarTower E E₁ E₂] : eppWeakReducedTensor E Q E₁ →ₐ[Q] eppWeakReducedTensor E Q E₂ :=
  Ideal.quotientMapₐ (nilradical (Q ⊗[E] E₂))
    (Algebra.TensorProduct.map (AlgHom.id Q Q) (IsScalarTower.toAlgHom E E₁ E₂))
    (fun _ hx ↦ mem_nilradical.mpr ((mem_nilradical.mp hx).map _))

/-- The induced canonical homomorphism of upper normalizations, obtained by
mapping each integral element with the reduced tensor homomorphism.
Source: Stacks Project, Tag 09ES, normalized tower proof
(blueprint: lem-sfb-epp-weak-solution-descent). -/
noncomputable def eppUpperCoefficientMap
    (R : Type u) (E : Type v) (Q : Type w) (E₁ : Type x) (E₂ : Type y)
    [CommRing R] [Field E] [Field Q] [Field E₁] [Field E₂]
    [Algebra R Q] [Algebra E Q] [Algebra E E₁] [Algebra E E₂] [Algebra E₁ E₂]
    [IsScalarTower E E₁ E₂] :
    eppWeakUpperClosure R E Q E₁ →+* eppWeakUpperClosure R E Q E₂ :=
  (((eppReducedCoefficientMap E Q E₁ E₂).restrictScalars R).comp
    (integralClosure R (eppWeakReducedTensor E Q E₁)).val).codRestrict
      (integralClosure R (eppWeakReducedTensor E Q E₂))
      (fun a ↦ a.property.map ((eppReducedCoefficientMap E Q E₁ E₂).restrictScalars R))
      |>.toRingHom

/-- The canonical lower-normalization action on a localized upper branch.
Source: Stacks Project, Tags 09EM and 09ES
(blueprint: lem-sfb-epp-weak-solution-descent). -/
noncomputable abbrev eppNormalizationLocalizationAlgebra
    (R : Type u) (S : Type v) (E : Type w) (Q : Type x) (E₁ : Type y)
    [CommRing R] [CommRing S] [Field E] [Field Q] [Field E₁]
    [Algebra R S] [Algebra R E] [Algebra S Q] [Algebra R Q] [Algebra E Q]
    [IsScalarTower R S Q] [IsScalarTower R E Q]
    [Algebra E E₁] [Algebra R E₁] [IsScalarTower R E E₁]
    (q : Ideal (eppWeakUpperClosure S E Q E₁)) [q.IsMaximal] :
    Algebra (integralClosure R E₁) (Localization.AtPrime q) :=
  ((algebraMap (eppWeakUpperClosure S E Q E₁) (Localization.AtPrime q)).comp
    (eppWeakNormalizationMap R S E Q E₁)).toAlgebra

/-- Weak solvability on one first-stage branch, tested on every compatible
fraction-field presentation of that very localization. The algebra on the
localization is the canonical normalization map, not an arbitrary morphism.
Source: Stacks Project, Tag 09ES, iterated normalized tower argument
(blueprint: lem-sfb-epp-weak-solution-descent). -/
def eppBranchContinuation
    (R : Type u) (S : Type v) (E : Type w) (Q : Type x) (E₁ : Type y) (E₂ : Type z)
    [CommRing R] [CommRing S] [Field E] [Field Q] [Field E₁] [Field E₂]
    [Algebra R S] [Algebra R E] [Algebra S Q] [Algebra R Q] [Algebra E Q]
    [IsScalarTower R S Q] [IsScalarTower R E Q]
    [Algebra E E₁] [Algebra R E₁] [IsScalarTower R E E₁]
    [Algebra E₁ E₂]
    (q : Ideal (eppWeakUpperClosure S E Q E₁)) [q.IsMaximal] : Prop :=
  letI : Algebra (integralClosure R E₁) (Localization.AtPrime q) :=
    eppNormalizationLocalizationAlgebra R S E Q E₁ q
  letI : SMul (integralClosure R E₁) (Localization.AtPrime q) :=
    (eppNormalizationLocalizationAlgebra R S E Q E₁ q).toSMul
  ∀ (F : Type (max u v w x y z t)) [Field F]
    [Algebra (Localization.AtPrime q) F] [IsFractionRing (Localization.AtPrime q) F]
    [Algebra E₁ F]
    [IsScalarTower (integralClosure R E₁) E₁ F]
    [_hbranch : IsScalarTower (integralClosure R E₁) (Localization.AtPrime q) F],
    eppIsWeakSolution (integralClosure R E₁) (Localization.AtPrime q) E₁ F E₂

/-- A complete DVR, with its local-ring structure bound explicitly.
Source: Stacks Project, Tag 09EM (blueprint: lem-sfb-epp-weak-solution-descent). -/
def eppIsCompleteDVR (R : Type u) [CommRing R] : Prop :=
  ∃ (hl : IsLocalRing R), IsAdicComplete (@IsLocalRing.maximalIdeal R _ hl) R ∧
    ∃ hd : IsDomain R, @IsDiscreteValuationRing R _ hd

/-- A finite product of actual complete DVRs, allowing all ring universes.
Source: Stacks Project, Tag 09EM (blueprint: lem-sfb-epp-weak-solution-descent). -/
def eppIsProductCompleteDVR (R : Type u) [CommRing R] : Prop :=
  ∃ (n : ℕ) (D : Fin n → CommRingCat.{u}),
    (∀ i, eppIsCompleteDVR (D i)) ∧ Nonempty (R ≃+* ∀ i, D i)

/-- The coefficient algebra on the reduced generic tensor, induced by
`a ↦ 1 ⊗ a` followed by reduction. Source: Stacks Project, Tag 09EM
(blueprint: lem-sfb-epp-weak-solution-descent). -/
noncomputable abbrev eppReducedRightAlgebra
    (E : Type u) (Q : Type v) (E₁ : Type w)
    [Field E] [Field Q] [Field E₁] [Algebra E Q] [Algebra E E₁] :
    Algebra E₁ (eppWeakReducedTensor E Q E₁) :=
  ((Ideal.Quotient.mkₐ E (nilradical (Q ⊗[E] E₁))).comp
    Algebra.TensorProduct.includeRight).toRingHom.toAlgebra

/-- The iterated reduced tensor, using the canonical coefficient algebra.
Source: Stacks Project, Tag 09ES, iterated normalized tower argument
(blueprint: lem-sfb-epp-weak-solution-descent). -/
abbrev eppIteratedReducedTensor
    (E : Type u) (Q : Type v) (E₁ : Type w) (E₂ : Type x)
    [Field E] [Field Q] [Field E₁] [Field E₂]
    [Algebra E Q] [Algebra E E₁] [Algebra E₁ E₂] :=
  letI := eppReducedRightAlgebra E Q E₁
  (eppWeakReducedTensor E Q E₁ ⊗[E₁] E₂) ⧸
    nilradical (eppWeakReducedTensor E Q E₁ ⊗[E₁] E₂)

/-- The generating element `(x ⊗ a) ⊗ b` of the iterated reduction.
Source: Stacks Project, Tag 09ES, iterated normalized tower argument
(blueprint: lem-sfb-epp-weak-solution-descent). -/
noncomputable def eppIteratedTmul
    (E : Type u) (Q : Type v) (E₁ : Type w) (E₂ : Type x)
    [Field E] [Field Q] [Field E₁] [Field E₂]
    [Algebra E Q] [Algebra E E₁] [Algebra E₁ E₂]
    (x : Q) (a : E₁) (b : E₂) : eppIteratedReducedTensor E Q E₁ E₂ :=
  letI := eppReducedRightAlgebra E Q E₁
  Ideal.Quotient.mk _ ((Ideal.Quotient.mk _ (x ⊗ₜ[E] a)) ⊗ₜ[E₁] b)

/-- Reduction commutes with successive coefficient extensions, with the
canonical pure-tensor characterization.

Source: Stacks Project, Tag 09ES, normalized tower argument, iterated twice
(blueprint: lem-sfb-epp-weak-solution-descent).

Proof: Maps from either side to a reduced ring are exactly compatible maps
from Q and E₂ agreeing on E. Factor first through the E₁ tensor and then
through its nilradical; the two universal constructions are inverse. On pure
tensors the resulting map sends `(x ⊗ a) ⊗ b` to `x ⊗ (a b)`.
-/
theorem epp_reduced_tensor_assoc
    (E : Type u) (Q : Type v) (E₁ : Type w) (E₂ : Type x)
    [Field E] [Field Q] [Field E₁] [Field E₂]
    [Algebra E Q] [Algebra E E₁] [Algebra E E₂] [Algebra E₁ E₂]
    [IsScalarTower E E₁ E₂] [Module.Finite E E₁] [Module.Finite E₁ E₂] :
    ∃ e : eppIteratedReducedTensor E Q E₁ E₂ ≃+* eppWeakReducedTensor E Q E₂,
      ∀ (x : Q) (a : E₁) (b : E₂),
        e (eppIteratedTmul E Q E₁ E₂ x a b) =
          Ideal.Quotient.mk _ (x ⊗ₜ[E] (algebraMap E₁ E₂ a * b)) := by
  sorry

/-- Normalization on any field branch of the successive reduced base change
agrees with normalization over the original complete DVR. Both quotient maps
are required to be the canonical maps on pure tensors, so the branch carries
its original structure maps.

Source: Stacks Project, Tags 09EM and 09ES, iterated normalized tower argument
(blueprint: lem-sfb-epp-weak-solution-descent).

Proof: Finite-dimensional reduced tensor algebras are finite products of
fields (lem-sfb-dvr-algebraic-normalization-structure). Thus a surjective field
quotient selects one factor. Its normalization over the complete DVR R is
finite, by lem-weil-pbc-complete-local-nagata, and local and complete by
lem-weil-pbc-finite-over-complete-local-product. The dimension-one criterion
lem-sfb-finite-normalization-local-dvr makes it a DVR. In the final field H,
integrality over this normalization implies integrality over R by
lem-weil-pbc-integral-transitive. Conversely a monic equation over R is also
a monic equation over the normalization. This proves equality as subrings
of the same field, hence respects every structure map. The reduced tensor
associativity and coordinate idempotents identify H with precisely its
corresponding direct-base-change field branch. Apply the same argument with
any intermediate lower DVR in place of R.
-/
theorem epp_normalization_branchwise
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : Type v) (Q : Type w) (E₁ : Type x) (E₂ : Type y)
    [Field E] [Field Q] [Field E₁] [Field E₂]
    [Algebra R Q] [IsFractionRing R Q] [Algebra E Q]
    [Algebra E E₁] [Module.Finite E E₁]
    [Algebra E₁ E₂] [Module.Finite E₁ E₂]
    (F : Type z) [Field F] [Algebra Q F] [Algebra E F] [Algebra E₁ F]
    [IsScalarTower E Q F] [IsScalarTower E E₁ F]
    [Algebra R F] [IsScalarTower R Q F]
    (φ : eppWeakReducedTensor E Q E₁ →+* F) (hφ : Function.Surjective φ)
    (hφ_tmul : ∀ (x : Q) (a : E₁),
      φ (Ideal.Quotient.mk _ (x ⊗ₜ[E] a)) = algebraMap Q F x * algebraMap E₁ F a)
    (H : Type t) [Field H] [Algebra F H] [Algebra E₁ H] [Algebra E₂ H]
    [IsScalarTower E₁ F H] [IsScalarTower E₁ E₂ H]
    [Algebra R H] [IsScalarTower R F H]
    (ψ : eppWeakReducedTensor E₁ F E₂ →+* H) (hψ : Function.Surjective ψ)
    (hψ_tmul : ∀ (x : F) (b : E₂),
      ψ (Ideal.Quotient.mk _ (x ⊗ₜ[E₁] b)) = algebraMap F H x * algebraMap E₂ H b) :
    eppIsCompleteDVR (integralClosure R F) ∧
    (integralClosure (integralClosure R F) H).toSubring =
      (integralClosure R H).toSubring := by
  sorry

/-- Weak solutions descend, compose after solving every normalized branch,
and compose over a single specified parent branch without any claim on others.

Source: Stacks Project, Tags 09EM and 09ES, with iteration for successive
coefficient extensions (blueprint: lem-sfb-epp-weak-solution-descent).

Proof:
1. Use lem-sfb-dvr-algebraic-normalization-structure for the finite field
   decompositions. Integrality in a finite product is coordinatewise, multiplying
   finitely many monic equations for the reverse implication. A complete DVR is
   Noetherian and Nagata (lem-weil-pbc-pid-noetherian-normal and
   lem-weil-pbc-complete-local-nagata), hence its finite-field normalization is
   finite. By lem-weil-pbc-finite-over-complete-local-product a domain factor is
   local and complete. Its dimension is one by the uniformizer-power expression
   (lem-weil-pbc-dvr-unit-times-uniformizer-power), so
   lem-sfb-finite-normalization-local-dvr makes it a complete DVR.
2. The integral closure of B in M is a finite complete DVR C'. Normality gives
   C' ⊆ C; locality identifies their maximal ideals. If x ∈ C lies outside C',
   its inverse lies in the maximal ideal of C', hence in that of C, impossible.
   Thus C=C' is integral over B. Injectivity of L ⊗ K₁ → M ⊗ K₁ follows by
   tensoring a linear retraction. Reducedness and monic equations give B₁ ⊆ C₁;
   integral transitivity and lying over give surjectivity on maximal branches
   (lem-weil-pbc-integral-transitive, lem-weil-pbc-integral-injective-lying-over,
   lem-weil-pbc-integral-prime-over-maximal-maximal and
   lem-weil-pbc-integral-maximal-contracts-maximal).
3. On a local tower A₁ → D → T write uniformizers as a=u d^e and d=v t^f.
   Weak solvability gives (a)=(t); cancellation forces ef=1, hence e=1.
   Surjectivity on branches proves descent.
4. epp_reduced_tensor_assoc identifies successive generic reductions. Finite
   product idempotents split the second tensor into its first-stage branches;
   nilpotence is coordinatewise, so this accounts for every final field factor.
5. On a branch F of the first reduction put D=integralClosure C F. In a final
   field H an element is integral over D iff it is integral over C: one way is
   transitivity and the other uses the same monic equation. The same holds for
   A₁ and A₂ and for each lower B branch, with all structural maps respected.
6. Every maximal ideal of C₂ has a parent q in C₁, and its local normalization
   is exactly the one in step 5. The assumed weak solution on every q gives
   precisely its ideal equality. Imposing the assumption at only one q gives
   the same conclusion exactly on the branches over q. The A→B weak-solution
   premise is retained, although it is redundant in this composition step.
-/
theorem epp_weak_solution_descent
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    (hAB : Function.Injective (algebraMap A B))
    (hBC : Function.Injective (algebraMap B C))
    (K : Type x) (L : Type y) (M : Type z)
    [Field K] [Field L] [Field M]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra C M] [IsFractionRing C M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A C M] [IsScalarTower A K M]
    [IsScalarTower B C M] [IsScalarTower B L M] [IsScalarTower K L M]
    [Module.Finite L M]
    (K₁ : Type t) [Field K₁] [Algebra K K₁] [Module.Finite K K₁]
    [Algebra A K₁] [IsScalarTower A K K₁] :
    eppIsCompleteDVR (integralClosure A K₁) ∧
    eppIsProductCompleteDVR (eppWeakUpperClosure C K M K₁) ∧
    (eppIsWeakSolution A C K M K₁ → eppIsWeakSolution A B K L K₁) ∧
    (∀ (K₂ : Type s) [Field K₂] [Algebra K₁ K₂] [Module.Finite K₁ K₂]
      [Algebra K K₂] [IsScalarTower K K₁ K₂]
      [Algebra A K₂] [IsScalarTower A K K₂],
      (integralClosure (integralClosure A K₁) K₂).toSubring =
        (integralClosure A K₂).toSubring ∧
      (eppIsWeakSolution A B K L K₁ →
        (∀ (q : Ideal (eppWeakUpperClosure C K M K₁)) [q.IsMaximal],
          eppBranchContinuation.{u, w, x, z, t, s, 0} A C K M K₁ K₂ q) →
        eppIsWeakSolution A C K M K₂) ∧
      (eppIsWeakSolution A B K L K₁ →
        ∀ (q : Ideal (eppWeakUpperClosure C K M K₁)) [q.IsMaximal],
          eppBranchContinuation.{u, w, x, z, t, s, 0} A C K M K₁ K₂ q →
          ∀ (r : Ideal (eppWeakUpperClosure C K M K₂)) [r.IsMaximal],
            r.comap (eppUpperCoefficientMap C K M K₁ K₂) = q →
            eppWeakBranch (eppWeakNormalizationMap A C K M K₂) r)) := by
  sorry

end IsDiscreteValuationRing
