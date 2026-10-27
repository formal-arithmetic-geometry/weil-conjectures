/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Sheaf.RingTheory.CompletionKaehlerDifferentialComparison
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.RingTheory.FormalRelativeDerivationExpansion
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Continuous conormal lifts and augmentation maps

Source: Stacks Project, varieties.tex, Tag 0C52; algebra.tex, Tags 00RO, 00RT,
00RU, 00RX, 00MA, 05GG; curves.tex, Tags 0C4B and 0C4D.
(blueprint: lem-trf-continuous-conormal-lift-augmentation).

The chain maps below are pairs of linear maps satisfying the commuting square.
This is the component description of maps of the displayed two-term complexes
in degrees -1 and 0; no injectivity, regularity, or exactness is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.ContinuousConormal

/-- A localized polynomial presentation at a rational maximal ideal, without regularity.
Source: Stacks, 00RT and 0C52
(blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure PolynomialPresentation (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] where
  m : ℕ
  q : Ideal (MvPolynomial (Fin m) k)
  maximal : q.IsMaximal
  rational : Nonempty ((MvPolynomial (Fin m) k ⧸ q) ≃ₐ[k] k)
  map : letI := maximal; Localization.AtPrime q →ₐ[k] A
  surjective : Function.Surjective map

attribute [instance] PolynomialPresentation.maximal

/-- The actual quotient extension, retaining its kernel modulo its square.
Source: Stacks, 00RU (blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
abbrev PolynomialPresentation.extension
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (P : PolynomialPresentation k A) : Extension k A :=
  Extension.ofSurjective P.map P.surjective

/-- A continuous local formal presentation, allowing zero variables and arbitrary kernels.
Source: Stacks, 0C52 (blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure FormalPresentation (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R] (a : Ideal R) where
  n : ℕ
  map : MvPowerSeries (Fin n) k →ₐ[k] R
  surjective : Function.Surjective map
  local_map : IsLocalHom map.toRingHom
  continuous : ∀ r : ℕ, ∃ N : ℕ,
    ((Ideal.span (Set.range (MvPowerSeries.X : Fin n →
      MvPowerSeries (Fin n) k))) ^ N).map map.toRingHom ≤ a ^ r

/-- The actual formal quotient extension, without replacing its conormal by a free module.
Source: Stacks, 00RU (blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
abbrev FormalPresentation.extension
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    {a : Ideal R} (T : FormalPresentation k R a) : Extension k R :=
  Extension.ofSurjective T.map T.surjective

/-- The differential and augmentation of the formal two-term conormal complex.
Their values on all ideal classes and coordinate vectors specify the maps uniquely.
Source: Stacks, 00RU and 0C4D
(blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure FormalData
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    {a : Ideal R} (T : FormalPresentation k R a)
    (M : Type w) [AddCommGroup M] [Module R M] (D : R → M) where
  differential : T.extension.Cotangent →ₗ[R] (Fin T.n → R)
  differential_class : ∀ h : T.extension.ker,
    differential (Extension.Cotangent.mk h) =
      fun i => T.map (MvPowerSeries.pderiv k i h.val)
  augmentation : (Fin T.n → R) →ₗ[R] M
  augmentation_basis : ∀ i : Fin T.n,
    augmentation (Pi.single i 1) = D (T.map (MvPowerSeries.X i))
  augmentation_differential : augmentation ∘ₗ differential = 0

/-- A map of formal presentations over their common quotient.
Source: Stacks, 0C4B (blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure FormalHom
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    {a : Ideal R} (T U : FormalPresentation k R a) where
  map : MvPowerSeries (Fin T.n) k →ₐ[k] MvPowerSeries (Fin U.n) k
  commutes : U.map.comp map = T.map
  local_map : IsLocalHom map.toRingHom
  continuous : ∀ r : ℕ, ∃ N : ℕ,
    ((Ideal.span (Set.range (MvPowerSeries.X : Fin T.n →
      MvPowerSeries (Fin T.n) k))) ^ N).map map.toRingHom ≤
      (Ideal.span (Set.range (MvPowerSeries.X : Fin U.n →
        MvPowerSeries (Fin U.n) k))) ^ r

/-- A polynomial-to-formal lift over the completion map.
Source: Stacks, 0C52 (blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure Lift
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : PolynomialPresentation k A)
    (T : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A)))) where
  map : Localization.AtPrime P.q →ₐ[k] MvPowerSeries (Fin T.n) k
  commutes : T.map.comp map = (IsScalarTower.toAlgHom k A (LocalCompletion A)).comp P.map
  local_map : IsLocalHom map.toRingHom

/-- The polynomial augmentation after scalar extension, fixed on universal differentials.
Source: Stacks, 00RO and 00RU
(blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure PolynomialData
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : PolynomialPresentation k A) where
  augmentation : (LocalCompletion A ⊗[A] P.extension.CotangentSpace) →ₗ[LocalCompletion A]
    CompletedDifferentials k A
  augmentation_d : ∀ x : P.extension.Ring,
    augmentation (1 ⊗ₜ[A] ((1 : A) ⊗ₜ[P.extension.Ring]
      KaehlerDifferential.D k P.extension.Ring x)) =
        (1 : LocalCompletion A) ⊗ₜ[A] KaehlerDifferential.D k A (P.map x)
  augmentation_differential : augmentation ∘ₗ
    LinearMap.baseChange (LocalCompletion A) P.extension.cotangentComplex = 0

/-- Component formulas for a conormal map attached to a formal presentation map.
Source: Stacks, 00RU and 0C4B
(blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure FormalMap
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    {a : Ideal R} {T U : FormalPresentation k R a} (β : FormalHom T U)
    {M : Type w} [AddCommGroup M] [Module R M] {D : R → M}
    (t : FormalData T M D) (s : FormalData U M D) where
  neg : T.extension.Cotangent →ₗ[R] U.extension.Cotangent
  pos : (Fin T.n → R) →ₗ[R] (Fin U.n → R)
  neg_class : ∀ h : T.extension.ker, ∃ h' : U.extension.ker,
    h'.val = β.map h.val ∧ neg (Extension.Cotangent.mk h) = Extension.Cotangent.mk h'
  pos_basis : ∀ i : Fin T.n, pos (Pi.single i 1) =
    fun j => U.map (MvPowerSeries.pderiv k j (β.map (MvPowerSeries.X i)))
  chain : pos ∘ₗ t.differential = s.differential ∘ₗ neg
  augmentation : s.augmentation ∘ₗ pos = t.augmentation

/-- Component formulas for a lift of a polynomial presentation to a formal one.
Source: Stacks, 00RO, 00RT and 00RU
(blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure LiftMap
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    {P : PolynomialPresentation k A}
    {T : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A)))}
    (α : Lift P T) (p : PolynomialData P)
    {D : LocalCompletion A → CompletedDifferentials k A}
    (t : FormalData T (CompletedDifferentials k A) D) where
  neg : (LocalCompletion A ⊗[A] P.extension.Cotangent) →ₗ[LocalCompletion A]
    T.extension.Cotangent
  pos : (LocalCompletion A ⊗[A] P.extension.CotangentSpace) →ₗ[LocalCompletion A]
    (Fin T.n → LocalCompletion A)
  neg_class : ∀ h : P.extension.ker, ∃ h' : T.extension.ker,
    h'.val = α.map h.val ∧
      neg (1 ⊗ₜ[A] Extension.Cotangent.mk h) = Extension.Cotangent.mk h'
  pos_d : ∀ x : P.extension.Ring,
    pos (1 ⊗ₜ[A] ((1 : A) ⊗ₜ[P.extension.Ring]
      KaehlerDifferential.D k P.extension.Ring x)) =
        fun i => T.map (MvPowerSeries.pderiv k i (α.map x))
  chain : pos ∘ₗ LinearMap.baseChange (LocalCompletion A) P.extension.cotangentComplex =
    t.differential ∘ₗ neg
  augmentation : t.augmentation ∘ₗ pos = p.augmentation

/-- Algebraic presentation maps, encoded by Mathlib's actual maps of extensions.
The local condition and the quotient square retain precisely the presentation-map hypotheses.
Source: Stacks, 00RO and 00RT
(blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure PolynomialHom
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (P Q : PolynomialPresentation k A) where
  hom : P.extension.Hom Q.extension
  local_map : IsLocalHom hom.toRingHom

/-- The entire compatible system of augmented conormal maps.
The identity and composition assertions compare components, so are independent of proof fields.
Source: Stacks, 00RU, 0C4B and 0C52
(blueprint: lem-trf-continuous-conormal-lift-augmentation). -/
structure System
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    (D : Derivation k (LocalCompletion A) (CompletedDifferentials k A)) where
  polynomial : ∀ P : PolynomialPresentation k A, PolynomialData P
  formal : ∀ T : FormalPresentation k (LocalCompletion A)
    ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))),
      FormalData T (CompletedDifferentials k A) D
  lifts : ∀ (P : PolynomialPresentation k A)
    (T : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A)))), Nonempty (Lift P T)
  liftMap : ∀ (P : PolynomialPresentation k A)
    (T : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))))
    (α : Lift P T), LiftMap α (polynomial P) (formal T)
  formalMap : ∀ (T U : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))))
    (β : FormalHom T U), FormalMap β (formal T) (formal U)
  chain_rule : ∀ (T : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))))
    (h : MvPowerSeries (Fin T.n) k),
      D (T.map h) = ∑ i : Fin T.n,
        T.map (MvPowerSeries.pderiv k i h) • D (T.map (MvPowerSeries.X i))
  formal_identity : ∀ (T : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))))
    (β : FormalHom T T), β.map = AlgHom.id k _ →
      (formalMap T T β).neg = LinearMap.id ∧ (formalMap T T β).pos = LinearMap.id
  formal_composition : ∀ (T U V : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))))
    (β : FormalHom T U) (γ : FormalHom U V) (δ : FormalHom T V),
    δ.map = γ.map.comp β.map →
      (formalMap T V δ).neg = (formalMap U V γ).neg ∘ₗ (formalMap T U β).neg ∧
      (formalMap T V δ).pos = (formalMap U V γ).pos ∘ₗ (formalMap T U β).pos
  lift_formal_composition : ∀ (P : PolynomialPresentation k A)
    (T U : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))))
    (α : Lift P T) (β : FormalHom T U) (γ : Lift P U),
    γ.map = β.map.comp α.map →
      (liftMap P U γ).neg = (formalMap T U β).neg ∘ₗ (liftMap P T α).neg ∧
      (liftMap P U γ).pos = (formalMap T U β).pos ∘ₗ (liftMap P T α).pos
  algebraic_augmentation : ∀ (P Q : PolynomialPresentation k A) (ρ : PolynomialHom P Q),
    Q.extension.toKaehler ∘ₗ Extension.CotangentSpace.map ρ.hom = P.extension.toKaehler
  algebraic_chain : ∀ (P Q : PolynomialPresentation k A) (ρ : PolynomialHom P Q),
    Extension.CotangentSpace.map ρ.hom ∘ₗ P.extension.cotangentComplex =
      Q.extension.cotangentComplex ∘ₗ Extension.Cotangent.map ρ.hom
  algebraic_completed_augmentation :
    ∀ (P Q : PolynomialPresentation k A) (ρ : PolynomialHom P Q),
    (polynomial Q).augmentation ∘ₗ LinearMap.baseChange (LocalCompletion A)
      (Extension.CotangentSpace.map ρ.hom) = (polynomial P).augmentation
  algebraic_identity : ∀ (P : PolynomialPresentation k A) (ρ : PolynomialHom P P),
    ρ.hom.toRingHom = RingHom.id _ →
      Extension.Cotangent.map ρ.hom = LinearMap.id ∧
      Extension.CotangentSpace.map ρ.hom = LinearMap.id
  algebraic_composition : ∀ (P Q H : PolynomialPresentation k A)
    (ρ : PolynomialHom P Q) (σ : PolynomialHom Q H) (τ : PolynomialHom P H),
    τ.hom.toRingHom = σ.hom.toRingHom.comp ρ.hom.toRingHom →
      Extension.Cotangent.map τ.hom =
        Extension.Cotangent.map σ.hom ∘ₗ Extension.Cotangent.map ρ.hom ∧
      Extension.CotangentSpace.map τ.hom =
        Extension.CotangentSpace.map σ.hom ∘ₗ Extension.CotangentSpace.map ρ.hom
  lift_algebraic_composition : ∀ (P Q : PolynomialPresentation k A)
    (T : FormalPresentation k (LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))))
    (ρ : PolynomialHom P Q) (α : Lift Q T) (γ : Lift P T),
    γ.map = α.map.comp ρ.hom.toAlgHom →
      (liftMap P T γ).neg = (liftMap Q T α).neg ∘ₗ
        LinearMap.baseChange (LocalCompletion A) (Extension.Cotangent.map ρ.hom) ∧
      (liftMap P T γ).pos = (liftMap Q T α).pos ∘ₗ
        LinearMap.baseChange (LocalCompletion A) (Extension.CotangentSpace.map ρ.hom)

/-- Local polynomial lifts and continuous formal presentation maps induce functorial chain
maps of augmented conormal complexes, without any regularity hypothesis.
Source: Stacks Project, varieties.tex, Tag 0C52; algebra.tex, Tags 00RO, 00RT,
00RU, 00RX, 00MA and 05GG; curves.tex, Tags 0C4B and 0C4D
(blueprint: lem-trf-continuous-conormal-lift-augmentation).

Proof:
1. Lift every polynomial coordinate through the formal surjection. Its residue is the
   prescribed rational coordinate. Every denominator outside the centre then has nonzero
   constant coefficient and is a unit (lem-weil-pbc-power-series-local-ring), so evaluation
   extends uniquely to the localization and is local.
2. The polynomial differential basis (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables)
   and localization (lem-weil-pbc-kahler-differentials-localization) identify the degree-zero
   term. Apply the universal derivation property to the formal gradient of the lift. Mapping
   ideal classes is well defined since the lift maps the kernel and its square into theirs.
3. Leibniz kills products of two kernel elements after reduction; this constructs the
   conormal differentials and proves the chain equation on ideal-class generators. The
   universal differential on the quotient gives the polynomial augmentation.
4. Apply lem-trf-completion-kahler-differential-comparison with the structural rational
   coefficient section. Its uniqueness identifies the given continuous extension. At every
   positive ideal-power quotient, lem-trf-power-series-adic-gradient-control gives the gradient
   formula. The completion comparison is injective and yields the asserted chain rule.
5. Apply that rule to the lifted polynomial coordinates and use the defining extension
   property. The polynomial differential basis then proves augmentation equality. For a
   relation the chain rule gives zero, so the formal augmentation kills its differential.
6. For a formal map, ideal classes map to ideal classes. Apply
   lem-trf-formal-relative-derivation-expansion to each partial derivative composed with the
   map. Reducing this equality proves its chain equation; the chain rule from step 4 proves
   its augmentation equality.
7. Identity maps act identically on classes and have identity Jacobian. For composition,
   ideal classes compose by evaluation and Jacobians multiply by the same relative-derivation
   expansion. Evaluate also at lifted polynomial coordinates for mixed composition.
8. Algebraic local presentation maps act by universal differentials and ideal classes.
   Leibniz gives the chain square; both augmentation composites take dp to the differential
   of its common image in A. These symbols span. Tensoring gives the completed equality.
   Identities, composition and polynomial-then-formal composition follow on the same
   generators, using d(s inverse) = -s inverse squared times ds for fractions.
-/
theorem continuous_conormal_lift_augmentation
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : (algebraMap k S).FiniteType) (m : Ideal S) [m.IsMaximal]
    (hm : Nonempty (m.ResidueField ≃ₐ[k] k))
    (D : Derivation k (LocalCompletion (Localization.AtPrime m))
      (CompletedDifferentials k (Localization.AtPrime m)))
    (hD : IsCompletedDifferentialExtension k (Localization.AtPrime m) D) :
    Nonempty (System k (Localization.AtPrime m) D) := by
  sorry

end Algebra.ContinuousConormal
