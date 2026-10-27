module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteProductPrincipalOpen

/-! # Tame finite-index group algebra base change

Source: ILO, Travaux de Gabber, VI 2.2, printed p.72; Stacks Tags 0325 and 02G8
(blueprint: lem-sfb-tame-kummer-group-algebra-completion).

The character and inclusion determine the two scalar structures on the tensor product.
The local product is indexed by maximal ideals, with the indexing specified by contraction
along the product projections. A quotient-indexed basis expresses the rank even for the zero ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.TameKummer

/-- The canonical character base change, using the group rings with basis `[g]` and
multiplication `[g][h] = [g+h]`. The left scalar map evaluates `[l]` at `ρ(l)` and
the right one sends `[l]` to `[i(l)]`.
Source: ILO VI 2.2, p.72 (blueprint: lem-sfb-tame-kummer-group-algebra-completion). -/
abbrev BaseChange {L : Type u} {M : Type v} {E : Type w}
    [AddCommGroup L] [AddCommGroup M] [CommRing E]
    (i : L →+ M) (ρ : Multiplicative L →* Eˣ) : Type (max v w) :=
  letI := (AddMonoidAlgebra.lift ℤ E L ((Units.coeHom E).comp ρ)).toRingHom.toAlgebra
  letI := (AddMonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  E ⊗[AddMonoidAlgebra ℤ L] AddMonoidAlgebra ℤ M

/-- The tensor-product commutative ring structure: `(a ⊗ x)(b ⊗ y) = ab ⊗ xy`.
Source: ILO VI 2.2, p.72; the algebra tensor pushout universal property
(blueprint: lem-sfb-tame-kummer-group-algebra-completion). -/
instance baseChangeCommRing {L : Type u} {M : Type v} {E : Type w}
    [AddCommGroup L] [AddCommGroup M] [CommRing E]
    (i : L →+ M) (ρ : Multiplicative L →* Eˣ) : CommRing (BaseChange i ρ) :=
  letI := (AddMonoidAlgebra.lift ℤ E L ((Units.coeHom E).comp ρ)).toRingHom.toAlgebra
  letI := (AddMonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  inferInstanceAs (CommRing (E ⊗[AddMonoidAlgebra ℤ L] AddMonoidAlgebra ℤ M))

/-- The canonical coefficient algebra structure, sending `a` to `a ⊗ 1`.
Source: ILO VI 2.2, p.72 (blueprint: lem-sfb-tame-kummer-group-algebra-completion). -/
instance baseChangeAlgebra {L : Type u} {M : Type v} {E : Type w}
    [AddCommGroup L] [AddCommGroup M] [CommRing E]
    (i : L →+ M) (ρ : Multiplicative L →* Eˣ) : Algebra E (BaseChange i ρ) :=
  letI := (AddMonoidAlgebra.lift ℤ E L ((Units.coeHom E).comp ρ)).toRingHom.toAlgebra
  letI := (AddMonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  inferInstanceAs (Algebra E (E ⊗[AddMonoidAlgebra ℤ L] AddMonoidAlgebra ℤ M))

/-- Tame finite-index base change is free of the quotient rank and etale. Over a
nonzero complete Noetherian local coefficient ring, its complete local factors are
indexed by its maximal ideals, and have finite separable residue extensions.

Source: ILO VI 2.2, printed p.72; Stacks Tags 0325 and 02G8
(blueprint: lem-sfb-tame-kummer-group-algebra-completion).

Proof:
1. Choose coset representatives in `M/i(L)`. Grouping group-ring coefficients by coset
   identifies the larger group ring with the direct sum of copies of the smaller one.
   Tensoring gives a basis `1 ⊗ [s(c)]` indexed by the quotient; its inverse sends
   `a ⊗ [i(l)+s(c)]` to the vector with coefficient `aρ(l)` in coordinate `c`.
   Balancing and the inverse identities follow on these generators (tensor and free
   module definitions).
2. Choose quotient generators and adjoin them successively. If `d` is the order of
   the next generator modulo the preceding subgroup, then `d` divides `N` and is a
   unit in every coefficient algebra. Tensor-pushout functoriality gives the maps
   between intermediate algebras, which are injective by their coset bases.
3. Each step is `A[T]/(T^d-u)` for a unit `u`: the monic quotient basis
   (`lem-weil-pbc-monic-quotient-free`) maps bijectively to the coset basis. This
   argument does not require torsion-free groups or a splitting of the extension.
4. The image `t` of `T` is a unit, so `d*t^(d-1)` is a unit. The standard-etale
   derivative presentation (`lem-weil-pbc-standard-etale-monic-derivative`) therefore
   identifies the step as etale. Compose the steps using
   `lem-weil-pbc-etale-composition-cancellation`; the zero-step case is the identity.
5. Apply `lem-weil-pbc-finite-over-complete-local-product` to the finite algebra.
   Its factors are Noetherian, local and complete; discard zero factors. The coset
   basis makes the product nonzero when the coefficient ring is nonzero.
6. Projections make each factor finite over `E`. By
   `lem-sbc-finite-product-principal-open` and `lem-weil-pbc-scheme-coproduct-family`,
   its spectrum is an open-and-closed component. Etale permanence makes each factor
   etale. Orthogonal coordinate idempotents show that every maximal ideal comes
   from exactly one local factor, giving the stated indexing and contraction formula.
7. By `lem-weil-pbc-finite-algebra-local-radical`, each factor's maximal ideal lies
   over the base maximal ideal, defining the local map and its residue extension.
   Its residue field is a quotient of the finite-dimensional closed fibre, hence
   finite. `lem-weil-pbc-etale-residue-field-extension-separable` supplies separability.
-/
theorem finite_free_etale_and_complete_local_factors
    {L : Type u} {M : Type v} {E : Type w}
    [AddCommGroup L] [AddCommGroup M] [AddGroup.FG L] [AddGroup.FG M] [CommRing E]
    (i : L →+ M) (_hi : Function.Injective i) (ρ : Multiplicative L →* Eˣ)
    [Finite (M ⧸ i.range)] (N : ℕ) (_hN : 0 < N) (_hunit : IsUnit (N : E))
    (_hkill : ∀ c : M ⧸ i.range, N • c = 0) :
    Nonempty (Module.Basis (M ⧸ i.range) E (BaseChange i ρ)) ∧
      Algebra.Etale E (BaseChange i ρ) ∧
      (∀ (_ : Nontrivial E) (_ : IsNoetherianRing E) (_ : IsLocalRing E)
          (_ : IsAdicComplete (IsLocalRing.maximalIdeal E) E),
        Finite (MaximalSpectrum (BaseChange i ρ)) ∧
          ∃ (A : MaximalSpectrum (BaseChange i ρ) → Type (max u v w))
            (_ : ∀ p, CommRing (A p)) (_ : ∀ p, Algebra E (A p))
            (_ : ∀ p, Nontrivial (A p)) (_ : ∀ p, IsLocalRing (A p))
            (_ : ∀ p, IsLocalHom (algebraMap E (A p))),
            ∃ e : BaseChange i ρ ≃ₐ[E] (∀ p, A p),
              ∀ p, IsNoetherianRing (A p) ∧
                IsAdicComplete (IsLocalRing.maximalIdeal (A p)) (A p) ∧
                Module.Finite E (A p) ∧ Algebra.Etale E (A p) ∧
                (IsLocalRing.maximalIdeal (A p)).comap
                  ((Pi.evalRingHom A p).comp e.toRingHom) = p.asIdeal ∧
                Module.Finite (IsLocalRing.ResidueField E)
                  (IsLocalRing.ResidueField (A p)) ∧
                Algebra.IsSeparable (IsLocalRing.ResidueField E)
                  (IsLocalRing.ResidueField (A p))) := by
  sorry

end Algebra.TameKummer
