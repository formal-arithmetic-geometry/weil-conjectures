/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison

public import Sheaf.AlgebraicGeometry.LogRegularSharpChart
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Sheaf.RingTheory.LogRegularSaturationNormality
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.RingTheory.CompleteToricModel
import Sheaf.AlgebraicGeometry.PointwiseLogRegularCompletion
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Completed sharp charts of log regular schemes

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70
(blueprint: lem-trf-log-regular-completed-chart).

The model rings and their boundary ideals are the existing `AddMonoidAlgebra`
constructions. Multiplicative characteristic monoids are converted with `Additive`.

## Main definitions

* `strictLocalRingStrictHenselizationIso`: re-exported from the definition module.
* `EtaleLogStructure.sharpChartRingMap`: the structural chart map in that colimit.
* `AddMonoidAlgebra.completedLocalModelMonomial`: the canonical model monomial.

## Main statements

* `exists_completed_chart_of_logRegular`: both characteristic cases with chart compatibility.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The ring-valued germ of a sharp chart in the affine-colimit strict henselization.
Source: ILO VI 1.6, printed p. 70
(blueprint: lem-trf-log-regular-completed-chart). -/
noncomputable def EtaleLogStructure.sharpChartRingMap
    {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (β : M.characteristic t →* M.monoidSheaf.obj.obj (op W)) :
    M.characteristic t →* Scheme.strictHenselizationRing t :=
  (strictLocalRingStrictHenselizationIso X t).hom.hom.toMonoidHom.comp
    ((M.toEtalePrelogStructure.stalkAlpha t).comp
      ((M.toEtalePrelogStructure.germ t W w).hom.comp β))

end AlgebraicGeometry

namespace AddMonoidAlgebra

/-- The canonical completed chart monomial `z^q` in the existing model ring.
Source: ILO VI 1.6, printed p. 70
(blueprint: lem-trf-log-regular-completed-chart). -/
noncomputable def completedLocalModelMonomial
    (L : Type u) [CommRing L] [IsLocalRing L]
    (P : Type u) [AddCommMonoid P] (n : ℕ) (q : P) : CompletedLocalModel L P n :=
  algebraMap (MvPolynomial (Fin n) (AddMonoidAlgebra L P)) (CompletedLocalModel L P n)
    (MvPolynomial.C (single q (1 : L)))

end AddMonoidAlgebra

namespace AlgebraicGeometry

private theorem completed_field_model_equiv
    (K L : Type u) [Field K] [Field L] (e : K ≃+* L)
    (P : Type u) [AddCommMonoid P] (n : ℕ) :
    ∃ E : AddMonoidAlgebra.CompletedLocalModel K P n ≃+*
        AddMonoidAlgebra.CompletedLocalModel L P n,
      ∀ q : P, E (AddMonoidAlgebra.completedLocalModelMonomial K P n q) =
        AddMonoidAlgebra.completedLocalModelMonomial L P n q := by
  let f := MvPolynomial.mapEquiv (Fin n) (AddMonoidAlgebra.mapRingEquiv P e)
  have hf (q : P) : f (MvPolynomial.C (AddMonoidAlgebra.single q (1 : K))) =
      MvPolynomial.C (AddMonoidAlgebra.single q (1 : L)) := by
    simp [f, MvPolynomial.mapEquiv_apply]
  have hmon : f.toRingHom '' {g | ∃ q : P, q ≠ 0 ∧
        g = MvPolynomial.C (AddMonoidAlgebra.single q (1 : K))} =
      {g | ∃ q : P, q ≠ 0 ∧
        g = MvPolynomial.C (AddMonoidAlgebra.single q (1 : L))} := by
    ext g
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, hf q⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨_, ⟨q, hq, rfl⟩, hf q⟩
  have hvar : f.toRingHom '' Set.range (MvPolynomial.X : Fin n →
        MvPolynomial (Fin n) (AddMonoidAlgebra K P)) =
      Set.range (MvPolynomial.X : Fin n →
        MvPolynomial (Fin n) (AddMonoidAlgebra L P)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [f, MvPolynomial.mapEquiv_apply]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, by simp [f, MvPolynomial.mapEquiv_apply]⟩
  have hboundary : (AddMonoidAlgebra.localModelBoundaryIdeal K P n).map f.toRingHom =
      AddMonoidAlgebra.localModelBoundaryIdeal L P n := by
    simp only [AddMonoidAlgebra.localModelBoundaryIdeal, Ideal.map_sup, Ideal.map_span]
    rw [hmon, hvar]
  have hcompletion : AddMonoidAlgebra.localModelCompletionIdeal L P n =
      (AddMonoidAlgebra.localModelCompletionIdeal K P n).map f.toRingHom := by
    simpa only [AddMonoidAlgebra.localModelCompletionIdeal,
      IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq] using hboundary.symm
  obtain ⟨E, hE⟩ := AdicCompletion.exists_ringEquiv _ _ f hcompletion
  refine ⟨E, fun q ↦ ?_⟩
  have h := DFunLike.congr_fun hE (MvPolynomial.C (AddMonoidAlgebra.single q (1 : K)))
  change E (algebraMap _ _ (MvPolynomial.C (AddMonoidAlgebra.single q (1 : K)))) =
    algebraMap _ _ (MvPolynomial.C (AddMonoidAlgebra.single q (1 : L)))
  change E (algebraMap _ _ (MvPolynomial.C (AddMonoidAlgebra.single q (1 : K)))) =
    algebraMap _ _ (f (MvPolynomial.C (AddMonoidAlgebra.single q (1 : K)))) at h
  rw [hf] at h
  exact h

private theorem charZero_of_no_field
    (A : Type u) [CommRing A] [IsDomain A]
    (h : ¬ ∃ (K : Type u) (_ : Field K), Nonempty (K →+* A)) : CharZero A := by
  apply (CharZero.charZero_iff_forall_prime_ne_zero A).2
  intro p hp hz
  let : Fact p.Prime := ⟨hp⟩
  let : CharP A p := (CharP.charP_iff_prime_eq_zero hp).2 hz
  exact h ⟨ULift.{u} (ZMod p), inferInstance,
    ⟨(ZMod.castHom (dvd_refl p) A).comp ULift.ringEquiv.toRingHom⟩⟩

/-- Completed local charts in equal and mixed characteristic, with the prescribed
characteristic monoid and compatibility with the replacement chart.
Source: ILO VI 1.6(i)--(ii), printed p. 70, citing Kato (1994), Theorem 3.2
(blueprint: lem-trf-log-regular-completed-chart).

Proof plan:
1. Take the affine sharp chart from `lem-trf-log-regular-sharp-chart` and keep it as
`W'`. Write `A` for the strict local ring, `I` for its log nonunit ideal, and `r` for
the rank of the characteristic group. The stalk-chart pushout and sharpness identify
`I` with `(a(q) : q ≠ 0)`. Finite generation of `P` makes this ideal finitely generated.
Log regularity (`def-trf-fs-log-blowup`) says `R = A/I` is regular local and
`dim A = dim R + r`. The local ring at x is Noetherian, so its strict henselization A
is Noetherian by `lem-sc-strict-henselization-noetherian`.
2. Put `n = dim R` and lift a regular system of parameters of R to elements `t_i`
of A. Then `m_A = I + (t_i)`. By `lem-weil-pbc-adic-completion-noetherian`,
`lem-weil-pbc-local-completion-local-ring`, `lem-weil-pbc-adic-completion-mod-ideal`
and `lem-weil-pbc-completion-dimension`, the completion H of A is Noetherian local,
complete, with maximal ideal `m_A H`, residue field k, and dimension `n + r`.
Apply `lem-weil-pbc-cohen-power-series-presentation` to H and restrict its surjection
to the coefficient ring. In residue characteristic zero this gives a coefficient
field k. In positive residue characteristic it gives a Cohen ring C with residue k.
If A contains a field of characteristic p, p vanishes in H, so the Cohen map factors
through `C/(p) = k`, again giving a coefficient field. If A contains no field, its
residue characteristic is a prime p: otherwise all nonzero integers would be units
and A would contain the rationals. Use C as coefficient ring in this case.
Map `L[P][t_i]` to H by its coefficient map, `z^q ↦ a(q)` and the chosen parameter
lifts. The completion ideal maps into `m_A H`, so completeness extends this map to
`φ : B_L(P,n) → H`. The source is complete by
`lem-weil-pbc-adic-completion-mod-ideal`; the extended completion ideal is `m_A H`,
for which H is Hausdorff, and the map onto k is surjective. Thus
`lem-weil-pbc-complete-source-surjective-mod-ideal` makes φ surjective.
3. Put `D = L[[t_i]]`, using `def-weil-pbc-multivariate-power-series`.
`lem-weil-pbc-power-series-field-cohen-regular-complete` makes D complete regular
local of dimension n for a field and n+1 for a Cohen ring. In the latter case
`p,t_i` is a regular system of parameters. Modulo every power of the completion
ideal, replacing polynomial parameters by power series changes nothing: terms of
parameter degree at least that power vanish. Hence `B_L(P,n)` is the completion
of D[P] at `(m_D,z^q : q ≠ 0)`. By `lem-trf-formal-monoid-ring-dimension`, it is a
Noetherian local domain of dimension `dim D + r`, and its monomial quotient is D.
An element reducing to a parameter in D is a nonzerodivisor and its quotient has
dimension `dim D + r - 1`.
4. In equal characteristic φ is a surjection from a Noetherian local domain of
dimension `n+r` onto H of the same dimension. If its kernel were nonzero, every
prime containing it would be nonzero. Any prime chain in the quotient could then
be extended downward by the zero prime in the source, contradicting the equality
of the finite dimensions (`def-weil-pbc-krull-dimension-ring`). Thus φ is bijective.
5. In the Cohen case let J be the completed ideal `(z^q : q ≠ 0,t_i)`. Its image
under the surjection φ is `m_A H`. Choose `j ∈ J` with `φ(j) = p`, and put
`θ = p-j`. Then `φ(θ) = 0` and `θ-p ∈ J`. Modulo monomials, θ is congruent to p
modulo `(t_i)` in D. Since `p,t_i` is a regular system of parameters, this reduction
belongs to `m_D` but not `m_D²`. The model dimension lemma therefore gives dimension
`n+r` for `B_C(P,n)/(θ)`, and `lem-trf-log-regular-saturation-normality` makes this
quotient a domain. It is Noetherian local as a quotient of the model. The induced
surjection to H is injective by exactly the prime-chain argument of step 4. This
makes H a domain. The Noetherian local completion map is injective, so A is a domain.
A positive-characteristic domain contains its finite prime field; this is excluded,
so A has characteristic zero in the case where it contains no field.
6. All maps were constructed with `z^q ↦ a(q)`, so both isomorphisms have the stated
monomial formulas, with the quotient map inserted in the Cohen case. The initial
chart itself serves as the allowed replacement and retains its characteristic
identification. The canonical colimit comparison in this module expresses the same
ring germs in the recorded affine-colimit model of the strict henselization.
7. For the trivial monoid there are no nonzero monomial generators; for n=0 there
are no parameter generators. The ideal constructions, completion maps and preceding
arguments still apply. When both occur for A, it is a field and the first model is
k itself. The coefficient maximal ideals are zero for k and `(p)` for C, by
`def-weil-pbc-cohen-ring` and `def-weil-pbc-adic-completion`.
-/
theorem exists_completed_chart_of_logRegular
    (X : FineSaturatedLogScheme.{u}) (_hX : X.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (W : X.scheme.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (β : X.logStructure.characteristic t →* X.logStructure.monoidSheaf.obj.obj (op W))
    (_hβ : X.logStructure.IsChart W β)
    (_hident : ∀ q : X.logStructure.characteristic t,
      Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W w (β q)) = q) :
    ∃ (_ : IsLocalRing (Scheme.strictHenselizationRing t))
      (W' : X.scheme.Etale) (w' : (Scheme.pointSmallEtale t).fiber.obj W')
      (β' : X.logStructure.characteristic t →*
        X.logStructure.monoidSheaf.obj.obj (op W')),
      IsAffine W'.left ∧ X.logStructure.IsChart W' β' ∧
      (∀ q : X.logStructure.characteristic t,
        Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W' w' (β' q)) = q) ∧
      ∃ n : ℕ,
        ((∃ (K : Type u) (_ : Field K), Nonempty (K →+* Scheme.strictHenselizationRing t)) →
          ∃ e : AddMonoidAlgebra.CompletedLocalModel
              (IsLocalRing.ResidueField (Scheme.strictHenselizationRing t))
              (Additive (X.logStructure.characteristic t)) n ≃+*
            AdicCompletion (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing t))
              (Scheme.strictHenselizationRing t),
            ∀ q : X.logStructure.characteristic t,
              e (AddMonoidAlgebra.completedLocalModelMonomial _ _ n (Additive.ofMul q)) =
                algebraMap _ _ (X.logStructure.sharpChartRingMap t W' w' β' q)) ∧
        ((¬ ∃ (K : Type u) (_ : Field K),
            Nonempty (K →+* Scheme.strictHenselizationRing t)) →
          ∃ p : ℕ, Nat.Prime p ∧
            CharP (IsLocalRing.ResidueField (Scheme.strictHenselizationRing t)) p ∧
            CharZero (Scheme.strictHenselizationRing t) ∧
            ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C), IsCohenRing p C ∧
              Nonempty ((C ⧸ Ideal.span {(p : C)}) ≃+*
                IsLocalRing.ResidueField (Scheme.strictHenselizationRing t)) ∧
              ∃ θ : AddMonoidAlgebra.CompletedLocalModel C
                  (Additive (X.logStructure.characteristic t)) n,
                θ - (p : AddMonoidAlgebra.CompletedLocalModel C
                    (Additive (X.logStructure.characteristic t)) n) ∈
                  AddMonoidAlgebra.completedLocalModelBoundaryIdeal C
                    (Additive (X.logStructure.characteristic t)) n ∧
                ∃ e : (AddMonoidAlgebra.CompletedLocalModel C
                    (Additive (X.logStructure.characteristic t)) n ⧸ Ideal.span {θ}) ≃+*
                    AdicCompletion
                      (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing t))
                      (Scheme.strictHenselizationRing t),
                  ∀ q : X.logStructure.characteristic t,
                    e (Ideal.Quotient.mk (Ideal.span {θ})
                      (AddMonoidAlgebra.completedLocalModelMonomial C _ n
                        (Additive.ofMul q))) =
                      algebraMap _ _ (X.logStructure.sharpChartRingMap t W' w' β' q)) := by
  classical
  obtain ⟨hA, _⟩ := strictHenselizationLocalStructure t
  let := hA
  let c := (strictLocalRingStrictHenselizationIso X.scheme t).commRingCatIsoToRingEquiv
  let : IsLocalRing (strictLocalRing X.scheme t) := c.symm.isLocalRing
  have hI : X.logStructure.nonunitIdeal t ≤
      IsLocalRing.maximalIdeal (strictLocalRing X.scheme t) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).2
      (fun h ↦ hm (X.logStructure.reflectsUnits Ω t m h))
  let : Nontrivial (strictLocalRing X.scheme t ⧸ X.logStructure.nonunitIdeal t) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hI)
  let : IsLocalRing (strictLocalRing X.scheme t ⧸ X.logStructure.nonunitIdeal t) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let := (_hX Ω t).1
  have hreg := IsRegularLocalRing.of_isRegularRing_of_isLocalRing
    (strictLocalRing X.scheme t ⧸ X.logStructure.nonunitIdeal t)
  obtain ⟨hR, hRN, hRL, hfs, hsharp, W', w', hW', β', hβ', hident', hstrict,
    hS, hSN, hSL, n, hequal, hmixed⟩ :=
    exists_completed_chart_of_logRegularAt X t hreg (_hX Ω t).2
  let := hR
  let := hRN
  let := hRL
  let := hS
  let := hSN
  let := hSL
  obtain ⟨E, hE⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
    (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing t)) c
    (IsLocalRing.map_ringEquiv_maximalIdeal c).symm
  have hfield_iff :
      (∃ (K : Type u) (_ : Field K), Nonempty (K →+* Scheme.strictHenselizationRing t)) ↔
      (∃ (K : Type u) (_ : Field K), Nonempty (K →+* strictLocalRing X.scheme t)) := by
    constructor
    · rintro ⟨K, hK, ⟨f⟩⟩
      exact ⟨K, hK, ⟨c.symm.toRingHom.comp f⟩⟩
    · rintro ⟨K, hK, ⟨f⟩⟩
      exact ⟨K, hK, ⟨c.toRingHom.comp f⟩⟩
  let k := IsLocalRing.ResidueField.mapEquiv c
  have hEchart (q : X.logStructure.characteristic t) :
      E (algebraMap _ _ (X.logStructure.toEtalePrelogStructure.stalkAlpha t
        (X.logStructure.toEtalePrelogStructure.germ t W' w' (β' q)))) =
        algebraMap _ _ (X.logStructure.sharpChartRingMap t W' w' β' q) := by
    exact DFunLike.congr_fun hE _
  refine ⟨hA, W', w', β', hW', hβ', hident', n, ?_, ?_⟩
  · intro hfield
    obtain ⟨e, he⟩ := hequal (hfield_iff.mp hfield)
    obtain ⟨F, hF⟩ := completed_field_model_equiv _ _ k.symm
      (Additive (X.logStructure.characteristic t)) n
    refine ⟨F.trans (e.symm.trans E), fun q ↦ ?_⟩
    change E (e.symm (F _)) = _
    rw [hF]
    change E (e.symm (ToricMonoid.monomial _ _ n (Additive.ofMul q))) = _
    rw [← he q, RingEquiv.symm_apply_apply]
    exact hEchart q
  · intro hnfield
    have hnfield' := hnfield ∘ hfield_iff.mpr
    obtain ⟨p, hp, hchar, C, hC, hCL, hCohen, ⟨eC⟩, θ, hθ, e, he⟩ :=
      hmixed hnfield'
    let := hC
    let := hCL
    let := hchar
    have hchar' : CharP (IsLocalRing.ResidueField (Scheme.strictHenselizationRing t)) p :=
      charP_of_injective_ringHom k.injective p
    have hCmax : IsLocalRing.maximalIdeal C = Ideal.span {(p : C)} := by
      obtain ⟨_, hCD, hDVR, hmax, _⟩ := hCohen
      exact hmax
    have hdomain := (AddMonoidAlgebra.completedLocalModel_normal
      (Additive (X.logStructure.characteristic t)) hfs (by
        intro a b hab
        have hab' : Additive.toMul b * Additive.toMul a = 1 :=
          (mul_comm _ _).trans hab
        have ha : IsUnit (Additive.toMul a) := ⟨⟨_, _, hab, hab'⟩, rfl⟩
        have hb : IsUnit (Additive.toMul b) := ⟨⟨_, _, hab', hab⟩, rfl⟩
        exact ⟨hsharp _ ha, hsharp _ hb⟩) n).2 C p hCohen θ hθ |>.1
    let := hdomain
    let : IsDomain (AdicCompletion
        (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
        (strictLocalRing X.scheme t)) := Function.Injective.isDomain e e.injective
    let : Module.FaithfullyFlat (strictLocalRing X.scheme t)
        (AdicCompletion (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
          (strictLocalRing X.scheme t)) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    let : IsDomain (strictLocalRing X.scheme t) :=
      Function.Injective.isDomain (algebraMap _
        (AdicCompletion (IsLocalRing.maximalIdeal (strictLocalRing X.scheme t))
          (strictLocalRing X.scheme t)))
        (FaithfulSMul.algebraMap_injective _ _)
    have hzero := charZero_of_no_field (strictLocalRing X.scheme t) hnfield'
    let := hzero
    have hzero' : CharZero (Scheme.strictHenselizationRing t) :=
      charZero_of_injective_ringHom c.injective
    refine ⟨p, hp, hchar', hzero', C, hC, hCL, hCohen, ?_, θ, hθ,
      e.symm.trans E, fun q ↦ ?_⟩
    · exact ⟨(Ideal.quotEquivOfEq hCmax.symm).trans (eC.trans k)⟩
    · change E (e.symm (Ideal.Quotient.mk (Ideal.span {θ})
        (ToricMonoid.monomial C _ n (Additive.ofMul q)))) = _
      rw [← he q, RingEquiv.symm_apply_apply]
      exact hEchart q

end AlgebraicGeometry

