module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.RingTheory.Etale.Field

/-! # The generic field of an injective ind-étale domain algebra

Source: Stacks Project, Tag 0BSD, the generic-field diagram in `section-ramification`;
Tags 092Q and 00U3 (blueprint: lem-dl-a1-ind-etale-domain-generic-field).
-/

@[expose] public section

set_option autoImplicit false

universe u v k l w

namespace Algebra

/-- For an injective ind-étale map of domains, the canonical map from the generic fibre
`K ⊗[A] C = (A \ {0})⁻¹C` to `L` is an isomorphism and `L/K` is separable algebraic.
Every map from `C` to a field that is injective on `A` is injective and extends uniquely
across `L`. The fraction-field models and their compatible scalar towers specify the
induced inclusion `K → L`; no finite-generation hypothesis is imposed.

Source: Stacks Project, Tag 0BSD, generic-field diagram; Tags 092Q and 00U3
(blueprint: lem-dl-a1-ind-etale-domain-generic-field).

Proof:
1. Put `S = A \ {0}`. Tensor balancing and fraction relations identify `K ⊗[A] C`
   with `S⁻¹C`, by `(a/s) ⊗ c ↦ u(a)c/u(s)` and `c/u(s) ↦ (1/s) ⊗ c`.
   Its canonical map `j` to `L` is injective: a zero fraction has zero numerator
   since `C` is a domain and `u(s)` is nonzero. Thus the generic fibre is a nonzero domain.
2. Base change along `A → K` preserves ind-étaleness, which implies weak étaleness,
   by `lem-weil-pbc-ind-etale-stability`. By `lem-weil-pbc-weak-etale-field`, every
   finitely generated `K`-subalgebra of the generic fibre is finite étale.
3. For each element `b`, its singly generated subalgebra `K[b]` is therefore finite étale.
   By `lem-weil-pbc-etale-algebra-over-field-product` (Tag 00U3), it is a finite product
   of finite separable fields. Being a nonzero domain, it has exactly one factor:
   an empty product is zero, and two factors give nonzero complementary idempotents.
4. The inverse of each nonzero `b` belongs to the field `K[b]`, hence to the generic fibre.
   This makes the generic fibre a field. Every element is algebraic and separable over
   `K`: its evaluation kernel and minimal polynomial agree with those in `K[b]`.
5. Every fraction `c/d` in `L` is `j((c/1)(d/1)⁻¹)`. Thus `j` is also surjective,
   and transports separable algebraicity to `L`.
6. Given `f : C → F` injective on `A`, all denominators from `S` have nonzero images.
   The localization map `c/u(s) ↦ f(c)/f(u(s))` is well-defined by cross-multiplication.
   It is injective since its source is a field, so its restriction `f` is injective.
   Compose with `j⁻¹` to extend to `L`. Every extension sends `c/d` to `f(c)/f(d)`,
   proving uniqueness. A unital homomorphism between fields is a field embedding.
-/
theorem indEtale_domain_genericField
    (A : Type u) (C : Type v) (K : Type k) (L : Type l)
    [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field K] [Field L] [Algebra A C] [Algebra A K] [IsFractionRing A K]
    [Algebra C L] [IsFractionRing C L] [Algebra A L] [IsScalarTower A C L]
    [Algebra K L] [IsScalarTower A K L]
    (hinj : Function.Injective (algebraMap A C))
    (hind : RingHom.IndEtaleAcrossUniverses (algebraMap A C)) :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId K L)
        (IsScalarTower.toAlgHom A C L)
        (fun x y ↦ Commute.all (algebraMap K L x) (algebraMap C L y))) ∧
    Algebra.IsSeparable K L ∧
    (∀ (F : Type w) [Field F] (f : C →+* F),
      Function.Injective (f.comp (algebraMap A C)) →
      Function.Injective f ∧
        ∃! g : L →+* F, g.comp (algebraMap C L) = f) := by
  sorry

end Algebra
