module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localization at the generic prime of an integral fibre

Source: Stacks Project, `flat.tex`, Tag 0810, final proof paragraph, and the elementary
localization algebra in `algebra.tex`, Tags 00E6, 00CP, 00DK, 00HT, 00CT and 00DF
(blueprint: lem-trf-fibre-generic-localization-residue-flat).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Localization

/-- Primality and contraction of the inverse image of the generic point of a domain fibre.
Source: Stacks, Tags 0810 and 00E6
(blueprint: lem-trf-fibre-generic-localization-residue-flat).

Proof: identify the fibre with the quotient of the base-localized algebra. The map from
κ(p) to the nonzero fibre is injective because its source is a field. Thus the kernel of
B → κ(p) ⊗ B contracts to p. The kernel is prime since the fibre is a domain. This is
step 1 of the node; the quotient comparison is lem-weil-pbc-fibre-ring-localization-quotient.
-/
theorem fibreGeneric_kernel_prime_liesOver
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] (p : Ideal R) [p.IsPrime] [IsDomain (p.Fiber B)] :
    (RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toRingHom).IsPrime ∧
      (RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toRingHom).LiesOver p :=
  by sorry

/-- The base-local-ring action on the localization of B ⊗ L, obtained by restricting
its canonical B_q-action along R_p → B_q. Source: Stacks, Tags 00CP and 00DK
(blueprint: lem-trf-fibre-generic-localization-residue-flat).
This uses the commuted model of L ⊗ B, so B acts on the left tensor factor. -/
noncomputable instance fibreGenericLocalizedTensorModule
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    (L : Type w) [AddCommGroup L] [Module R L] :
    Module (Localization.AtPrime p) (LocalizedModule q.primeCompl (B ⊗[R] L)) :=
  letI : Module (Localization.AtPrime q) (LocalizedModule q.primeCompl (B ⊗[R] L)) :=
    LocalizedModule.moduleOfIsLocalization
  Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))

/-- The natural tensor comparison for localization at the fibre-generic prime.
Source: Stacks, Tags 0810, 00DK and 00SI
(blueprint: lem-trf-fibre-generic-localization-residue-flat).

The tensor factors are commuted by TensorProduct.comm: the displayed formula is exactly
(l ⊗ b)/t ↦ l ⊗ (b/t) in the order of the node. The source action is the restriction of
the canonical B_q-action, as constructed above. The two additional algebra instances are
the canonical local-ring map, specified by IsLiesOverAlgebra; they exist by
Localization.AtPrime.algebraOfLiesOver. Primality and lying over are supplied by
fibreGeneric_kernel_prime_liesOver, so these binders impose no extra hypothesis on R → B.

Proof (step 3): apply lem-weil-pbc-prime-localized-module-base-change. Identify L_p with
L by l/s ↦ (s/1)⁻¹l, with inverse l ↦ l/1. Equality of localized fractions makes this
well defined because denominators act invertibly. Tensor the identification with B_q.
The resulting comparison sends (b ⊗ l)/t to (b/t) ⊗ l. For any A-linear map h, the two
naturality composites send this generator to (b/t) ⊗ h(l). Additivity and a common
denominator extend the equality to every localized tensor.
-/
theorem fibreGeneric_tensor_comparison
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] (p : Ideal R) [p.IsPrime] [IsDomain (p.Fiber B)]
    (q : Ideal B) [q.IsPrime]
    (hq : q = RingHom.ker
      (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toRingHom)
    [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    ∃ Φ : ∀ (L : Type w) [AddCommGroup L] [Module R L]
      [Module (Localization.AtPrime p) L] [IsScalarTower R (Localization.AtPrime p) L],
      LocalizedModule q.primeCompl (B ⊗[R] L) ≃ₗ[Localization.AtPrime p]
        Localization.AtPrime q ⊗[Localization.AtPrime p] L,
      (∀ (L : Type w) [AddCommGroup L] [Module R L]
        [Module (Localization.AtPrime p) L] [IsScalarTower R (Localization.AtPrime p) L]
        (l : L) (b : B) (t : q.primeCompl),
        Φ L (LocalizedModule.mk (b ⊗ₜ[R] l) t) = Localization.mk b t ⊗ₜ l) ∧
      (∀ (L L' : Type w) [AddCommGroup L] [AddCommGroup L']
        [Module R L] [Module R L']
        [Module (Localization.AtPrime p) L] [Module (Localization.AtPrime p) L']
        [IsScalarTower R (Localization.AtPrime p) L]
        [IsScalarTower R (Localization.AtPrime p) L']
        (h : L →ₗ[Localization.AtPrime p] L')
        (x : LocalizedModule q.primeCompl (B ⊗[R] L)),
        Φ L' (IsLocalizedModule.map q.primeCompl
          (LocalizedModule.mkLinearMap q.primeCompl (B ⊗[R] L))
          (LocalizedModule.mkLinearMap q.primeCompl (B ⊗[R] L'))
          (TensorProduct.AlgebraTensorModule.lTensor B B (h.restrictScalars R)) x) =
          h.lTensor (Localization.AtPrime q) (Φ L x)) := by
  sorry

/-- The existing fibre/quotient equivalence, with its B-algebra structure forgotten.
Source: Stacks, Tag 00E6; Mathlib's Ideal.Fiber.algEquivQuotient
(blueprint: lem-trf-fibre-generic-localization-residue-flat).
This wrapper supplies the right-factor B-action explicitly, so consumers need no local
instance to use the canonical equivalence. Its data is the existing Mathlib construction.
-/
noncomputable def fibreGenericFibreQuotientEquiv
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] :
    p.Fiber B ≃+* (Localization (Algebra.algebraMapSubmonoid B p.primeCompl) ⧸
      Ideal.map (algebraMap (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)))
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))) :=
  letI : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  (Ideal.Fiber.algEquivQuotient p).toRingEquiv

/-- Flatness and the fraction-normalized closed-fibre comparison of the fibre-generic
localization. Source: Stacks, Tags 0810, 00CP, 00HT, 00CT and 00DF
(blueprint: lem-trf-fibre-generic-localization-residue-flat).

The map u is the canonical factorization B_p → B_q. The map ρ is its actual reduction,
characterized on every quotient class, and θ is characterized on every fraction. Thus
no arbitrary comparison map or unspecified isomorphism is substituted for the canonical
ones. The fibre uses Mathlib's κ(p) ⊗ B convention. The equality of ring maps states that
θ after reduction is exactly localization, under Ideal.Fiber.algEquivQuotient.

Proof (steps 2, 4, 5 and 6): since q contracts to p, all images of R minus p are units
in B_q. The localization universal property (lem-weil-pbc-ring-localization-universal-property)
gives the compatible maps R_p → B_q and u, and localization-of-localization makes u a
localization at the image of B minus q. Localization-flatness, composition of flat maps
and flat-over-localization give flatness over R_p. Put I = mC. Then ID = mD since both
are generated by the image of m. Quotient base change identifies D/mD with D ⊗_C (C/I).
Identify C/I with F, exchange tensor factors, and apply localization base change to
obtain θ : D/mD ≃ Tbar⁻¹F. In the tensor ring the images of b and t on the two factors
agree, so θ([b/t]) = bbar/tbar. By the definition of q, each tbar is nonzero. Checking
the composite on every fraction b/f(s) in C shows that θ ∘ ρ is the localization map
from F. If z/1 = 0 then vz = 0 for some v in Tbar; the domain property and v ≠ 0 imply
z = 0. Thus localization is injective and so is ρ. These are precisely the six node
steps together with the tensor comparison stated above.
-/
theorem fibreGeneric_flat_closedFibre
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] (p : Ideal R) [p.IsPrime] [IsDomain (p.Fiber B)]
    (q : Ideal B) [q.IsPrime]
    (hq : q = RingHom.ker
      (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toRingHom)
    [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) ∧
      (∀ z ∈ q.primeCompl.map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toMonoidHom, z ≠ 0) ∧
      ∃ u : Localization (Algebra.algebraMapSubmonoid B p.primeCompl) →ₐ[Localization.AtPrime p]
        Localization.AtPrime q,
        u.toRingHom.comp (algebraMap B _) = algebraMap B (Localization.AtPrime q) ∧
        ∃ ρ : (Localization (Algebra.algebraMapSubmonoid B p.primeCompl) ⧸
          Ideal.map (algebraMap (Localization.AtPrime p) _)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))) →+*
          (Localization.AtPrime q ⧸ Ideal.map (algebraMap (Localization.AtPrime p) _)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))),
          (∀ c, ρ (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk _ (u c)) ∧
          ∃ θ : (Localization.AtPrime q ⧸ Ideal.map (algebraMap (Localization.AtPrime p) _)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))) ≃+*
            Localization (q.primeCompl.map
              (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toMonoidHom),
            (∀ (b : B) (t : q.primeCompl),
              θ (Ideal.Quotient.mk _ (Localization.mk b t)) =
                Localization.mk
                  ((Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B) b)
                  ⟨(Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B) t,
                    Submonoid.mem_map_of_mem _ t.property⟩) ∧
            θ.toRingHom.comp ρ =
              (algebraMap (p.Fiber B) _).comp
                (fibreGenericFibreQuotientEquiv (B := B) p).symm.toRingHom ∧
            Function.Injective ρ := by
  sorry

end Localization
