/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Generic algebraicity in a localized affine model

Source: Stacks Project, Tag 0AB6, localization paragraph, expanded using Tags 01T2,
00DK, 00E3, 00ES, 01HV and 01I4
(blueprint: lem-sfb-generic-algebraicity-localized-affine-model).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The affine model over the local ring of a target point preserves algebraicity
at generic points. The charts `i` and `j` present the affine opens `U` and `V`,
respectively; the target point is `j p`. The ring `C` in the source is the displayed
`A ⊗[R] Localization.AtPrime p.asIdeal`.

Source: Stacks Project, Tag 0AB6, localization paragraph
(blueprint: lem-sfb-generic-algebraicity-localized-affine-model).

Proof:
1. Apply lem-weil-pbc-lft-affine-pairs (Tag 01T2) to the chart square. The finitely
   many generators of `A` over `R` tensor to generators of `C` over `B`.
2. Apply lem-weil-pbc-localization-tensor-over-base (Tag 00DK) and tensor symmetry.
   The map sends `a ⊗ (r/t)` to `a*r/t`; its inverse sends `a/t` to `(a ⊗ 1)/(1 ⊗ t)`.
   These formulas give a ring localization, including when a denominator becomes zero.
3. By def-weil-pbc-localization-at-prime, `B` is local with maximal ideal `pB`.
   Use lem-weil-pbc-affine-open-stalk-localization (01HV) for the canonical stalk
   isomorphism; taking residue fields identifies its residue field with that at `j p`.
   Use lem-weil-pbc-fibre-product-affine-spectra (01I4) for the tensor spectrum and
   its two canonical projections.
4. Apply lem-weil-pbc-localization-prime-residue-field-iso (00E3) to contract a
   minimal prime `Q'`. A smaller prime of `A` avoids the denominators and extends
   to a smaller prime of `C`, so contraction is minimal. Extension recovers `Q'`.
   Commutativity of the tensor square identifies both contractions to `R`; the
   prime correspondence for `R → B` gives `q = q₀B` and `q₀ ≤ p`.
5. By lem-weil-pbc-spec-irreducible-components-minimal-primes (00ES), `V(Q)` is an
   irreducible component of the chart. Its generic point is generic for a component
   of `Z`: close that point in `Z`; any larger irreducible closed set meets the
   chart in an irreducible set containing `V(Q)`, hence has the same dense open.
   This uses no finiteness of the family of components.
6. Use lem-weil-pbc-affine-open-stalk-localization to identify the chart stalk map
   with `r/t ↦ image(r)/image(t)`. Passing to residues identifies the extension
   at this generic point with `κ(q₀) → κ(Q)`. Apply the hypothesis.
7. Use lem-weil-pbc-localization-prime-residue-field-iso on both localization maps.
   The resulting residue-field isomorphisms commute with the two field maps:
   on every fraction `r/t` both composites have the same image. Transport a nonzero
   annihilating polynomial along the lower field isomorphism; injectivity preserves
   its nonzeroness and the commuting square preserves its vanishing. No Noetherian
   or dimension assumption is used. -/
theorem generic_algebraicity_localized_affine_model
    {Z S : Scheme.{u}} (g : Z ⟶ S) [LocallyOfFiniteType g]
    (R A : CommRingCat.{u}) [Algebra R A]
    (i : Spec A ⟶ Z) (j : Spec R ⟶ S) [IsOpenImmersion i] [IsOpenImmersion j]
    (hchart : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j)
    (p : PrimeSpectrum R)
    (hgeneric : ∀ (D : Set Z), D ∈ irreducibleComponents Z →
      ∀ (η : Z), IsGenericPoint η D →
        @Algebra.IsAlgebraic (S.residueField (g η)) (Z.residueField η) _ _
          (g.residueFieldMap η).hom.toAlgebra) :
    (algebraMap R A).FiniteType ∧
    ((Algebra.TensorProduct.includeRight (R := R) (A := A)
      (B := Localization.AtPrime p.asIdeal)).toRingHom).FiniteType ∧
    IsLocalRing (Localization.AtPrime p.asIdeal) ∧
    Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ∧
    IsLocalization (p.asIdeal.primeCompl.map (algebraMap R A))
      (A ⊗[R] Localization.AtPrime p.asIdeal) ∧
    IsIso ((Spec.stalkIso R p).inv ≫ inv (j.stalkMap p)) ∧
    (∃ ρ : CommRingCat.of p.asIdeal.ResidueField ≅ S.residueField (j p),
      CommRingCat.ofHom (IsLocalRing.residue (Localization.AtPrime p.asIdeal)) ≫ ρ.hom =
        ((Spec.stalkIso R p).inv ≫ inv (j.stalkMap p)) ≫ S.residue (j p)) ∧
    (∃ e : Spec (CommRingCat.of (A ⊗[R] Localization.AtPrime p.asIdeal)) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))),
      e.hom ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] Localization.AtPrime p.asIdeal))) ∧
      e.hom ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := A)
            (B := Localization.AtPrime p.asIdeal)).toRingHom)) ∧
    ∀ (Q' : PrimeSpectrum (A ⊗[R] Localization.AtPrime p.asIdeal)),
      Q'.asIdeal ∈ minimalPrimes (A ⊗[R] Localization.AtPrime p.asIdeal) →
      ∃ (Q : PrimeSpectrum A) (q₀ : PrimeSpectrum R)
        (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)),
        ∃ (hQ : Q.asIdeal = Q'.asIdeal.comap (algebraMap A (A ⊗[R] Localization.AtPrime p.asIdeal)))
          (hq₀ : q₀.asIdeal = Q.asIdeal.comap (algebraMap R A))
          (hq : q.asIdeal = Q'.asIdeal.comap
            (Algebra.TensorProduct.includeRight (R := R) (A := A)
              (B := Localization.AtPrime p.asIdeal)).toRingHom)
          (hbase : q₀.asIdeal = q.asIdeal.comap (algebraMap R (Localization.AtPrime p.asIdeal))),
        Q.asIdeal ∈ minimalPrimes A ∧
        Disjoint (p.asIdeal.primeCompl.map (algebraMap R A) : Set A) (Q.asIdeal : Set A) ∧
        Ideal.map (algebraMap A (A ⊗[R] Localization.AtPrime p.asIdeal)) Q.asIdeal = Q'.asIdeal ∧
        Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) q₀.asIdeal = q.asIdeal ∧
        q₀.asIdeal ≤ p.asIdeal ∧
        ∃ (α : Q.asIdeal.ResidueField ≃+* Q'.asIdeal.ResidueField)
          (β : q₀.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField),
          α.toRingHom = Ideal.ResidueField.map Q.asIdeal Q'.asIdeal
            (algebraMap A (A ⊗[R] Localization.AtPrime p.asIdeal)) hQ ∧
          β.toRingHom = Ideal.ResidueField.map q₀.asIdeal q.asIdeal
            (algebraMap R (Localization.AtPrime p.asIdeal)) hbase ∧
          α.toRingHom.comp
              (Ideal.ResidueField.map q₀.asIdeal Q.asIdeal (algebraMap R A) hq₀) =
            (Ideal.ResidueField.map q.asIdeal Q'.asIdeal
              (Algebra.TensorProduct.includeRight (R := R) (A := A)
                (B := Localization.AtPrime p.asIdeal)).toRingHom hq).comp β.toRingHom ∧
          @Algebra.IsAlgebraic q.asIdeal.ResidueField Q'.asIdeal.ResidueField _ _
            (Ideal.ResidueField.map q.asIdeal Q'.asIdeal
              (Algebra.TensorProduct.includeRight (R := R) (A := A)
                (B := Localization.AtPrime p.asIdeal)).toRingHom hq).toAlgebra := by
  sorry

end AlgebraicGeometry
