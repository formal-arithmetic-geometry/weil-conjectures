/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.Functoriality
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.FlatModInjective

/-!
# Completion presentations after extension of the residue field

Source: Stacks Project, varieties.tex, Tag 0C54 (lemma-base-change-complete-local-ring),
with Tags 0C4Y and 0C50 (blueprint: lem-trf-field-extension-completion-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A chosen formal presentation at a finite separable closed point extends to the
completion at the point specified by a residue-field embedding.

`q` is fixed by its equality with the kernel of the tensor evaluation. The local map
`g` is fixed on `S`, and its completion `h` is fixed at every finite quotient. Thus the
last compatibility uses the canonical map of completions. The ring equivalence `e`,
together with its displayed action on constant series, is an equivalence of `K`-algebras
for the action on the target induced by `c ↦ 1 ⊗ c`. Locality and completeness are
recorded explicitly. The equality for every coefficient-transported series includes
both the chosen coefficient section and the image of each variable.

Source: Stacks Project, varieties.tex, Tag 0C54, with Tags 0C4Y and 0C50
(blueprint: lem-trf-field-extension-completion-presentation).

Proof:
1. Finite type gives Noetherianity (lem-weil-pbc-finite-type-algebra-noetherian).
   Field extension is faithfully flat (lem-weil-pbc-field-extension-base-change-faithfully-flat)
   and localization gives the flat local map g (lem-weil-pbc-flat-local-ring-maps).
   The finite separable closed fibre is reduced
   (lem-weil-pbc-finite-separable-tensor-field-reduced), hence its localization is the field K.
   Thus the maximal ideal extends to the maximal ideal of B. The pointwise dimension
   comparison is lem-weil-pbc-dimension-at-point-field-extension, as in Tags 0C4Y and 0C50.
2. Both completions are Noetherian and local with the same residue fields, and complete
   (lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring,
   lem-weil-pbc-adic-completion-mod-ideal). The levelwise map h is flat by
   lem-weil-pbc-flat-completion, and induces the specified embedding on residues.
3. The chosen variable images generate the completed maximal ideal. Their images under h
   generate the target maximal ideal. Apply
   lem-weil-pbc-power-series-universal-property-complete with coefficients K to construct
   the map sending variables to those images. The coefficient sections agree by the
   canonical factorization of the finite separable tensor fibre (Tag 0C50).
4. The transported relations vanish because they vanish under the original presentation.
   The full power series source is complete by
   lem-weil-pbc-power-series-field-cohen-regular-complete. Reduction to K is the identity;
   lem-weil-pbc-complete-source-surjective-mod-ideal gives surjectivity of the power series
   map, hence of its quotient by the transported relations.
5. The target is flat over the original completed ring by step 2. Apply
   lem-weil-pbc-flat-mod-injective to the quotient map, whose reduction is the identity of K;
   the quotient source is a finite module over its Noetherian local self. This gives
   injectivity.
6. Package the bijective quotient map as e. Its construction fixes constants, preserves
   the whole coefficient-extended presentation and in particular each variable. As a
   local ring isomorphism it preserves maximal ideals and their powers, giving the
   asserted isomorphism of complete local K-algebras.
-/
theorem field_extension_completion_presentation
    {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [Field K] [Algebra k K]
    (p : Ideal S) [p.IsMaximal]
    [FiniteDimensional k p.ResidueField] [Algebra.IsSeparable k p.ResidueField]
    (ι : p.ResidueField →ₐ[k] K)
    (q : Ideal (S ⊗[k] K)) [q.IsPrime]
    (hq : q = RingHom.ker
      (Algebra.TensorProduct.lift
        (ι.comp (IsScalarTower.toAlgHom k S p.ResidueField)) (AlgHom.id k K)
        (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (σ : p.ResidueField →ₐ[k]
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p))
    (hσ : ∀ c : p.ResidueField,
      AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (σ c) = c)
    (n s : ℕ)
    (φ : MvPowerSeries (Fin n) p.ResidueField →ₐ[k]
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p))
    (hφ_constants : ∀ c : p.ResidueField, φ (MvPowerSeries.C c) = σ c)
    (hφ_surjective : Function.Surjective φ)
    (f : Fin s → MvPowerSeries (Fin n) p.ResidueField)
    (hφ_kernel : RingHom.ker φ.toRingHom = Ideal.span (Set.range f))
    (hf : Ideal.span (Set.range f) ≤
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) p.ResidueField)))
    (hφ_continuous : ∀ r : ℕ, ∃ N : ℕ,
      (Ideal.span
        (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) p.ResidueField)) ^ N).map
          φ.toRingHom ≤
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p)))) ^ r) :
    ∃ g : Localization.AtPrime p →+* Localization.AtPrime q,
      (∀ a : S, g (algebraMap S (Localization.AtPrime p) a) =
        algebraMap (S ⊗[k] K) (Localization.AtPrime q) (a ⊗ₜ[k] (1 : K))) ∧
      ∃ h : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p) →+*
        AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q),
        (∀ (r : ℕ)
            (z : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p)) (a : Localization.AtPrime p),
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) r z =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ r) a →
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q)) r (h z) =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ r)
                (g a)) ∧
        ∃ e : (MvPowerSeries (Fin n) K ⧸ Ideal.span
            (Set.range (fun j : Fin s ↦ MvPowerSeries.map ι.toRingHom (f j)))) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
            (Localization.AtPrime q),
          (∀ c : K, e (Ideal.Quotient.mk _ (MvPowerSeries.C c)) =
            algebraMap (Localization.AtPrime q)
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
                (Localization.AtPrime q))
              (algebraMap (S ⊗[k] K) (Localization.AtPrime q) ((1 : S) ⊗ₜ[k] c))) ∧
          (∀ z : MvPowerSeries (Fin n) p.ResidueField,
            e (Ideal.Quotient.mk _ (MvPowerSeries.map ι.toRingHom z)) = h (φ z)) ∧
          (∀ i : Fin n, e (Ideal.Quotient.mk _ (MvPowerSeries.X i)) =
            h (φ (MvPowerSeries.X i))) ∧
          ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) K ⧸ Ideal.span
              (Set.range (fun j : Fin s ↦ MvPowerSeries.map ι.toRingHom (f j)))))
            (_ : IsLocalRing
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
                (Localization.AtPrime q))),
            IsLocalHom e.toRingHom ∧
            IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K ⧸ Ideal.span
                (Set.range (fun j : Fin s ↦ MvPowerSeries.map ι.toRingHom (f j)))))
              (MvPowerSeries (Fin n) K ⧸ Ideal.span
                (Set.range (fun j : Fin s ↦ MvPowerSeries.map ι.toRingHom (f j)))) ∧
            IsAdicComplete
              (IsLocalRing.maximalIdeal
                (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
                  (Localization.AtPrime q)))
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
                (Localization.AtPrime q)) := by
  sorry

end Algebra
