/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.RingTheory.LogRegularSaturationNormality
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.RingTheory.FormalMonoidRingDimension
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.TraceFormula.FsFaceSharpening

/-!
# Formal models after a group-isomorphism monoid extension

Source: ILO, Travaux de Gabber, VI 1.6, printed p. 70, and VIII 3.1.1--3.1.5,
printed pp. 98--99 (blueprint: lem-trf-formal-monoid-extension-model).
The base-change assertion is the agent-supplied local algebra input of the DAG,
not a quotation of VI 1.8. Localizations and their sharpenings use Mathlib's
`Localization` and `Associates`; the completed model rings are the published
`AddMonoidAlgebra.CompletedLocalModel`, with zero variables for the output.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- The actual tensor ring `A ⊗[ℤ[R]] ℤ[Q]`, with the algebra structures induced by
`α` and `h`. Source: the algebraic input attached to ILO VI 1.6 and VIII 3.1.2
(blueprint: lem-trf-formal-monoid-extension-model). -/
noncomputable def monoidChartTensor {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] {Q : Type w} [CommMonoid Q]
    (α : R →* A) (h : R →* Q) : CommRingCat.{max u w} := by
  letI := (MonoidAlgebra.lift ℤ A R α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ h).toAlgebra
  exact CommRingCat.of (A ⊗[MonoidAlgebra ℤ R] MonoidAlgebra ℤ Q)

/-- The canonical base-ring map into the chart tensor ring.
Source: the tensor presentation of ILO VI 1.6, VIII 3.1.2
(blueprint: lem-trf-formal-monoid-extension-model). -/
noncomputable def monoidChartTensorBase {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] {Q : Type w} [CommMonoid Q]
    (α : R →* A) (h : R →* Q) : A →+* monoidChartTensor α h := by
  letI := (MonoidAlgebra.lift ℤ A R α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ h).toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom (R := MonoidAlgebra ℤ R)
    (A := A) (B := MonoidAlgebra ℤ Q)

/-- The canonical `Q`-monomials in the chart tensor ring.
Source: the tensor presentation of ILO VI 1.6, VIII 3.1.2
(blueprint: lem-trf-formal-monoid-extension-model). -/
noncomputable def monoidChartTensorMonomial {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] {Q : Type w} [CommMonoid Q]
    (α : R →* A) (h : R →* Q) : Q →* monoidChartTensor α h := by
  letI := (MonoidAlgebra.lift ℤ A R α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ h).toAlgebra
  exact (Algebra.TensorProduct.includeRight (R := MonoidAlgebra ℤ R)
    (A := A) (B := MonoidAlgebra ℤ Q)).toMonoidHom.comp (MonoidAlgebra.of ℤ Q)

/-- The sharp localization at the inverse image of the ring units, in additive notation.
For an integral fs monoid, localization is canonically its submonoid of fractions
inside the group completion, and its units are precisely the group of the face.
Source: ILO VIII 3.1.1--3.1.5
(blueprint: lem-trf-formal-monoid-extension-model). -/
abbrev chartSharpMonoid {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] (α : R →* A) :=
  Additive (Associates (Localization ((IsUnit.submonoid A).comap α)))

/-- Extension of the chart by inverting exactly the monomials that map to units.
Source: ILO VIII 3.1.2 (blueprint: lem-trf-formal-monoid-extension-model). -/
noncomputable def localizedUnitChart {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] (α : R →* A) :
    Localization ((IsUnit.submonoid A).comap α) →* A :=
  (Localization.monoidOf ((IsUnit.submonoid A).comap α)).lift (fun g ↦ g.2)

/-- The canonical map from a face localization to the ambient group completion.
Source: ILO VIII 3.1.2 (blueprint: lem-trf-formal-monoid-extension-model). -/
noncomputable def unitChartGroupMap {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] (α : R →* A) :
    Localization ((IsUnit.submonoid A).comap α) →* GrothendieckGroup R :=
  (Localization.monoidOf ((IsUnit.submonoid A).comap α)).lift
    (g := GrothendieckGroup.of) (fun _ ↦ Group.isUnit _)

end Algebra

namespace AddMonoidAlgebra

/-- A ring equivalence of pairs, continuous in both directions for the two indicated
adic topologies. Source: the completed-pair assertion attached to ILO VI 1.6
(blueprint: lem-trf-formal-monoid-extension-model). -/
def IsAdicPairEquiv {B : Type u} [CommRing B] {H : Type v} [CommRing H]
    (b J : Ideal B) (c L : Ideal H) (e : B ≃+* H) : Prop :=
  Ideal.map e.toRingHom J = L ∧
    @Continuous B H b.adicTopology c.adicTopology e ∧
    @Continuous H B c.adicTopology b.adicTopology e.symm

/-- The conclusion of the formal-model extension, retaining the coefficient residue
field, the actual monomial ideal, and both adic topologies. The Boolean selects the
field model (`false`) or the parameter hypersurface (`true`). The zero-variable
completed model is canonically the completion of `D[T]` at `(m_D,[v]:v≠0)`.
Source: ILO VI 1.6, VIII 3.1.1--3.1.5 and the DAG's independent local algebra input
(blueprint: lem-trf-formal-monoid-extension-model). -/
def HasExtendedFormalMonoidModel
    (B : Type u) [CommRing B] [IsLocalRing B]
    (T : Type v) [AddCommMonoid T] (J : Ideal B) (mixed : Bool) : Prop :=
  ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Nontrivial D)
    (_ : IsRegularLocalRing D),
    IsAdicComplete (IsLocalRing.maximalIdeal D) D ∧
    Nonempty (IsLocalRing.ResidueField D ≃+* IsLocalRing.ResidueField B) ∧
    match mixed with
    | false => ∃ e : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+*
          CompletedLocalModel D T 0,
        IsAdicPairEquiv
          (Ideal.map (algebraMap B _) (IsLocalRing.maximalIdeal B))
          (Ideal.map (algebraMap B _) J)
          (Ideal.map (algebraMap (MvPolynomial (Fin 0) (AddMonoidAlgebra D T)) _)
            (localModelCompletionIdeal D T 0))
          (completedLocalModelBoundaryIdeal D T 0) e
    | true => ∃ (η : CompletedLocalModel D T 0)
        (ρ : (CompletedLocalModel D T 0 ⧸ completedLocalModelBoundaryIdeal D T 0) ≃ₐ[D] D),
        ρ (Ideal.Quotient.mk (completedLocalModelBoundaryIdeal D T 0) η) ∈
          IsLocalRing.maximalIdeal D ∧
        ρ (Ideal.Quotient.mk (completedLocalModelBoundaryIdeal D T 0) η) ∉
          (IsLocalRing.maximalIdeal D) ^ 2 ∧
        ∃ e : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+*
            (CompletedLocalModel D T 0 ⧸ Ideal.span {η}),
          IsAdicPairEquiv
            (Ideal.map (algebraMap B _) (IsLocalRing.maximalIdeal B))
            (Ideal.map (algebraMap B _) J)
            (Ideal.map (Ideal.Quotient.mk (Ideal.span {η}))
              (Ideal.map (algebraMap (MvPolynomial (Fin 0) (AddMonoidAlgebra D T)) _)
                (localModelCompletionIdeal D T 0)))
            (Ideal.map (Ideal.Quotient.mk (Ideal.span {η}))
              (completedLocalModelBoundaryIdeal D T 0)) e

end AddMonoidAlgebra

namespace Algebra

/-- The chart monomials in the prescribed prime localization of the tensor ring.
Source: ILO VIII 3.1.2 and the DAG's local algebra input
(blueprint: lem-trf-formal-monoid-extension-model). -/
noncomputable def localizedTensorMonomial {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] {Q : Type w} [CommMonoid Q]
    (α : R →* A) (h : R →* Q) (q : Ideal (monoidChartTensor α h)) [q.IsPrime] :
    Q →* Localization.AtPrime q :=
  (algebraMap (monoidChartTensor α h) (Localization.AtPrime q)).toMonoidHom.comp
    (monoidChartTensorMonomial α h)

/-- The ideal generated by the nonunit chart monomials at the selected prime.
Source: ILO VI 1.6 and VIII 3.1.5
(blueprint: lem-trf-formal-monoid-extension-model). -/
noncomputable def localizedTensorBoundary {A : Type u} [CommRing A]
    {R : Type v} [CommMonoid R] {Q : Type w} [CommMonoid Q]
    (α : R →* A) (h : R →* Q) (q : Ideal (monoidChartTensor α h)) [q.IsPrime] :
    Ideal (Localization.AtPrime q) :=
  Ideal.span {b | ∃ x : Q, ¬ IsUnit (localizedTensorMonomial α h q x) ∧
    b = localizedTensorMonomial α h q x}

/-- A group-isomorphism chart extension preserves the two specified formal monoid
models, with the new sharp monoid and the actual nonface monomial ideal.
Source: ILO VI 1.6, printed p. 70, VIII 3.1.1--3.1.5, pp. 98--99;
the base-change assertion is the independent agent-origin algebra input of the DAG
(blueprint: lem-trf-formal-monoid-extension-model).

Proof plan (the fourteen steps of the node):
1. The contraction condition makes `A → B` local and unit-reflecting. The unit
   preimages are faces, and `h⁻¹(F)=G`. Apply `lem-trf-fs-face-sharpening` to both:
   the localized units are their face groups, and `S,T` are sharp fs with free
   finite-rank group completions. Their ranks need not agree.
2. Transfer `ε` along the inverse group isomorphism. Multiplying every `Q`-monomial
   by this character gives an algebra automorphism untwisting the relations;
   it preserves the chosen primes and all nonface monomial ideals.
3. Invert `F` and retain the unit relations. For `N=h(G^gp)`, put `P=Q_F/N`.
   Balancing tensors gives `C_F = A ⊗[ℤ[S]] ℤ[P]`; do not discard `F^gp/N`.
4. The residual unit group `K=F^gp/N` is a subgroup of the finite free group
   `R^gp/G^gp`, so `lem-weil-subgroup-finite-free-abelian-group-free` makes it free.
   Split the free sharp quotient to obtain `P=K⊕T`. Write the chart as `(δ,β)`;
   unit reflection gives `β(s)≠0` for every `s≠0`.
5. Replace `A` by its completion. The chosen local rings have canonically the
   same quotients by every maximal-ideal power, by
   `lem-weil-pbc-adic-completion-mod-power` and balanced tensors, hence the same
   completions with all monomials retained.
6. Before imposing any relation, use `R₀=L[S][t]`, its completion `H_S`,
   `U=L[P][t]` and `W=H_S ⊗[R₀] U`. Associating tensors gives the chart base change.
   Finite type and completion Noetherianity give the required Noetherian rings.
7. With `E=L[K][t]`, one has `U=E[T]`. The selected stratum prime is
   `r=pU+([v]:v≠0)`, and `Frac(E/p)` is exactly `κ(q)`.
8. Compare the localizations of `W` and `U` modulo every maximal-ideal power.
   Polynomial representatives of formal coefficients give inverse maps on each
   quotient, using `lem-weil-pbc-adic-completion-mod-power`. Take inverse limits.
9. Construct `D` as the completion of `E_p`, before imposing the mixed relation.
   Polynomial regularity, regular-local localization and
   `lem-weil-pbc-completion-regular-local` make it regular local; completion gives
   completeness and the unchanged residue field `κ(q)`, hence nonzeroness.
10. Finite geometric inversion and coefficient replacement modulo powers identify
    the completed localization of `E[T]` with the completion of `D[T]` at
    `(m_D,[v]:v≠0)`, compatibly at every finite level.
11. Combine the comparisons. In the mixed case apply
    `lem-weil-pbc-local-completion-quotient` to the actual relation `θ`, obtaining
    its full substituted image `η`. The chart monomials substitute as
    `[δ(s)][β(s)]`; no coefficient-only replacement is made.
12. Modulo the old variables, the Cohen stratum and its quotient by `p` are regular
    local. The kernel-parameter and cotangent-dimension lemmas imply `p∉m²`.
13. The stratum quotient of `D[[T]]` is canonically `D`, by
    `lem-trf-formal-monoid-ring-dimension`. Modulo the old variables, the reduced
    relation equals `p`. Completion preserves its nonzero cotangent class.
    Thus its reduction belongs to `m_D` and not `m_D²`, allowing linear t-terms.
14. A nonface `Q`-monomial maps to a unit times a nonzero `T`-monomial. Conversely
    every nonzero `T`-class has a representative `q-f` with `q∉F`, so its monomial
    is a unit multiple of a generator of `J`. This proves equality of the actual
    generated ideals. The finite-quotient comparisons are continuous both ways.
    Empty parameter lists, trivial `T` and trivial `K` use the same constructions.
-/
theorem formalMonoidExtension_model
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (R : Type v) [CommMonoid R] (Q : Type w) [CommMonoid Q]
    (_hR : AlgebraicGeometry.IsFineSaturatedMonoid R)
    (_hQ : AlgebraicGeometry.IsFineSaturatedMonoid Q) (h : R →* Q)
    (_hgp : Function.Bijective
      (GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)))
    (α : R →* A) (a : Multiplicative (chartSharpMonoid α) →* A)
    (ε : GrothendieckGroup R →* Aˣ)
    (_hα : ∀ r : Localization ((IsUnit.submonoid A).comap α),
      localizedUnitChart α r =
        (ε (unitChartGroupMap α r) : A) * a (Multiplicative.ofAdd
          (Additive.ofMul (Associates.mk r))))
    (q : Ideal (monoidChartTensor α h)) [q.IsPrime]
    (_hq : Ideal.comap (monoidChartTensorBase α h) q = IsLocalRing.maximalIdeal A) :
    ((∃ (n : ℕ)
        (e : AddMonoidAlgebra.CompletedLocalModel (IsLocalRing.ResidueField A)
          (chartSharpMonoid α) n ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A),
        ∀ s : chartSharpMonoid α,
          e (algebraMap (MvPolynomial (Fin n)
              (AddMonoidAlgebra (IsLocalRing.ResidueField A) (chartSharpMonoid α))) _
            (MvPolynomial.C (AddMonoidAlgebra.single s (1 : IsLocalRing.ResidueField A)))) =
            algebraMap A _ (a (Multiplicative.ofAdd s))) →
      AddMonoidAlgebra.HasExtendedFormalMonoidModel (Localization.AtPrime q)
        (chartSharpMonoid (localizedTensorMonomial α h q))
        (localizedTensorBoundary α h q) false) ∧
    ((∃ (V : Type (max u v w)) (_ : CommRing V) (_ : IsLocalRing V) (p : ℕ),
        IsCohenRing p V ∧
        Nonempty (IsLocalRing.ResidueField V ≃+* IsLocalRing.ResidueField A) ∧
        ∃ (n : ℕ) (θ : AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n),
          θ - (p : AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n) ∈
            AddMonoidAlgebra.completedLocalModelBoundaryIdeal V (chartSharpMonoid α) n ∧
          ∃ e : (AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n ⧸
              Ideal.span {θ}) ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
            ∀ s : chartSharpMonoid α,
              e (Ideal.Quotient.mk (Ideal.span {θ})
                (algebraMap (MvPolynomial (Fin n)
                    (AddMonoidAlgebra V (chartSharpMonoid α))) _
                  (MvPolynomial.C (AddMonoidAlgebra.single s (1 : V))))) =
                  algebraMap A _ (a (Multiplicative.ofAdd s))) →
      AddMonoidAlgebra.HasExtendedFormalMonoidModel (Localization.AtPrime q)
        (chartSharpMonoid (localizedTensorMonomial α h q))
        (localizedTensorBoundary α h q) true) := by
  sorry

end Algebra
