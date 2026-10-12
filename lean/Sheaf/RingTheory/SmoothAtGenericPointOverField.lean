module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Sheaf.FieldTheory.SeparableExtension
public import Sheaf.RingTheory.SingularIdeal
import Sheaf.RingTheory.RegularLocalSeparableResidueSmooth

@[expose] public section
universe u v w
namespace Algebra

/-- Core finitely generated subextension transport used to prove separability of the
zero-prime residue field. Source: Stacks Project, Algebra, Lemma 07ND. The proof
identifies the zero-prime residue field with the fraction field, transports the
finitely generated intermediate field across that identification, and applies
separable generation supplied by `hsep`.
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable-fg) -/
theorem separableExtension_bot_residueField_finitelyGenerated
    (k : Type u) (S : Type v) (L : Type w)
    [Field k] [CommRing S] [IsDomain S] [Field L]
    [Algebra k S] [Algebra S L] [Algebra k L] [IsScalarTower k S L]
    [FiniteType k S] [IsFractionRing S L]
    (hsep : IsSeparableExtension k L)
    (F : IntermediateField k (⊥ : Ideal S).ResidueField) (hF : F.FG) :
    IsSeparablyGenerated k F := by
  sorry

/-- Separability of the fraction field transfers to the residue field at the generic point.
Source: Stacks Project, Algebra, Lemma 07ND. The proof identifies the residue field at
the zero prime with the fraction field through the localization and residue-field
isomorphisms for a domain, then transports `IsSeparableExtension` across that
field isomorphism. The required compatibility with the given `k`-algebra structures
follows from the canonical maps in the localization construction.
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable) -/
theorem separableExtension_bot_residueField
    (k : Type u) (S : Type v) (L : Type w)
    [Field k] [CommRing S] [IsDomain S] [Field L]
    [Algebra k S] [Algebra S L] [Algebra k L] [IsScalarTower k S L]
    [FiniteType k S] [IsFractionRing S L] (hsep : IsSeparableExtension k L) :
    IsSeparableExtension k (⊥ : Ideal S).ResidueField := by
  intro F hF
  exact separableExtension_bot_residueField_finitelyGenerated k S L hsep F hF


/-- A finite type domain over a field with separable fraction field is smooth at the zero prime.
Source: Stacks Project, Algebra, Lemma 07ND.
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field) -/
theorem smoothAtPrime_bot_of_isSeparable_fractionRing
    (k : Type u) (S : Type v) (L : Type w)
    [Field k] [CommRing S] [IsDomain S] [Field L]
    [Algebra k S] [Algebra S L] [Algebra k L] [IsScalarTower k S L]
    [FiniteType k S] [IsFractionRing S L] (hsep : IsSeparableExtension k L) :
    IsSmoothAtPrime k (⟨(⊥ : Ideal S), inferInstance⟩ : PrimeSpectrum S) := by
  let _ : IsLocalization (⊥ : Ideal S).primeCompl (FractionRing S) := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  let e : Localization.AtPrime (⊥ : Ideal S) ≃+* FractionRing S :=
    (IsLocalization.algEquiv (⊥ : Ideal S).primeCompl
      (Localization.AtPrime (⊥ : Ideal S)) (FractionRing S)).toRingEquiv
  have hreg : IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal S)) :=
    IsRegularLocalRing.of_ringEquiv (R := FractionRing S) e.symm
  exact (regularLocal_iff_smoothAtPrime k S (⊥ : Ideal S)
    (separableExtension_bot_residueField k S L hsep)).mpr hreg

end Algebra
