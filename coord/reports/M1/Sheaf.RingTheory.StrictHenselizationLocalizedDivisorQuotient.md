## What changed

Retired the zero-hole duplicate Sheaf.RingTheory.StrictHenselizationLocalizedDivisorQuotient
under its coord/retire-items.tsv assignment. deleted.txt withdraws that file only.
The sole direct consumer, Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation,
now privately imports WeilConjectures.RingTheory.StrictHenselizationLocalizedDivisorQuotient.
Its exact theorem signature and all public imports are unchanged.

The consumer constructs p=q/(f), the canonical separable closure of the residue field
of B=(R/(f))_p, and the quotient action with Ideal.Quotient.lift followed by
IsLocalization.lift. Denominators map to units by the original local-base algebra
map. IsLocalization.lift_eq proves the compatibility required by the upstream theorem.
This construction reuses the corresponding existing upstream consumer argument.
No upstream file, definition, target statement, or new public declaration is changed.

The item's node attaches to the upstream theorem with its verbatim chosen-action
signature and an explanation deriving the unchanged existential node statement.
Its proof and the consumer node's final step describe the resulting argument.
See coord/changes/M1-retire-strict-henselization-localized-divisor-quotient.md.

Validation: the adapted consumer compiled without errors or warnings (2.1 s).
An independent sandbox-only derivation of the entire original existential signature
compiled (1.7 s) with exactly [propext, Classical.choice, Quot.sound].
The unchanged consumer with only its proof import migrated fails at line 80:89:
hf has type f in q but the upstream theorem expects an ideal of R/(f).
Thus the additional proof construction is necessary. Import-direction checking accepts
the replacement import. A source-graph comparison introduces no duplicate-module pair
and removes the retiring module from the consumer's import closure. The existing
StrictHenselizationStructuralMap wrapper/upstream pair is unchanged.

The construction covers f=0, q=0 over a field, nilpotent f, and arbitrary local bases:
it uses only f in q and preservation of units, with no domain, regularity,
Noetherianity or nonzerodivisor assumption. A unit f cannot belong to the prime q.
The quotient action is explicitly induced by b, rather than chosen without compatibility.

Complete sandbox-only attachment check recovering the old statement:

```lean
module

public import WeilConjectures.RingTheory.StrictHenselizationLocalizedDivisorQuotient

@[expose] public section

universe u
namespace Algebra

theorem exists_localized_divisor_quotient_attachment
    (R C : Type u) [CommRing R] [CommRing C]
    (q : Ideal R) [q.IsPrime]
    (K : Type u) [Field K]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
    [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
    [Algebra (Localization.AtPrime q) K]
    [IsScalarTower (Localization.AtPrime q)
      (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
    [Algebra (Localization.AtPrime q) C]
    (hC : IsStrictHenselization (Localization.AtPrime q) K C)
    (b : R →+* C)
    (hbase : ∀ r : R, algebraMap (Localization.AtPrime q) C
      (algebraMap R (Localization.AtPrime q) r) = b r)
    (f : R) (hf : f ∈ q) :
    ∃ (p : Ideal (R ⧸ Ideal.span {f})) (_ : p.IsPrime)
      (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) L)
      (_ : Algebra (Localization.AtPrime p) L)
      (_ : IsScalarTower (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) L)
      (_ : Algebra (Localization.AtPrime p) (C ⧸ Ideal.span {b f})),
      IsStrictHenselization (Localization.AtPrime p) L
        (C ⧸ Ideal.span {b f}) := by
  classical
  let J : Ideal R := Ideal.span {f}
  have hJ : J ≤ q := (Ideal.span_singleton_le_iff_mem q).2 hf
  let p : Ideal (R ⧸ J) := q.map (Ideal.Quotient.mk J)
  have hpprime : p.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hp : p.comap (Ideal.Quotient.mk J) = q := Ideal.comap_map_mk hJ
  let L := SeparableClosure (IsLocalRing.ResidueField (Localization.AtPrime p))
  let aL : Algebra (Localization.AtPrime p) L :=
    ((algebraMap (IsLocalRing.ResidueField (Localization.AtPrime p)) L).comp
      (IsLocalRing.residue _)).toAlgebra
  have tL : IsScalarTower (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) L :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let ψ : R ⧸ J →+* C ⧸ Ideal.span {b f} :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk _).comp b) (fun a ha ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  have hunit : ∀ s : p.primeCompl, IsUnit (ψ s) := by
    rintro ⟨s, hs⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hr : r ∈ q.primeCompl := fun hr ↦ hs (Ideal.mem_map_of_mem _ hr)
    have hu := (IsLocalization.map_units (Localization.AtPrime q) ⟨r, hr⟩).map
      (algebraMap (Localization.AtPrime q) (C))
    rw [hbase r] at hu
    exact hu.map (Ideal.Quotient.mk _)
  let φ : Localization.AtPrime p →+* C ⧸ Ideal.span {b f} :=
    IsLocalization.lift hunit
  let aφ : Algebra (Localization.AtPrime p) (C ⧸ Ideal.span {b f}) :=
    φ.toAlgebra
  have hcomp : ∀ r : R, algebraMap (Localization.AtPrime p)
      (C ⧸ Ideal.span {b f})
      (algebraMap (R ⧸ J) _ (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (b r) :=
    fun r ↦ IsLocalization.lift_eq hunit _
  exact ⟨p, hpprime, L, inferInstance, inferInstance, inferInstance, aL, tL, aφ,
    hC.localized_divisor_quotient R (C) q K b hbase f p hp L hcomp⟩

#print axioms exists_localized_divisor_quotient_attachment
end Algebra

```

## Proved and sorry left

This is a retirement repair with 0 direct holes in the assigned module.
Closed: 0 of 0; added: 0; split off: 0. No sorry remains in any delivered Lean file.

AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_presentation remains
completely proved with exactly its original signature. The old existential
Algebra.IsStrictHenselization.localized_divisor_quotient statement is fully derived
from the upstream compatible-action theorem by the attachment check above.
No existing proved declaration is replaced by a sorry. No new node or hollow
definition is introduced.

## No longer needed

Withdrawn module: Sheaf.RingTheory.StrictHenselizationLocalizedDivisorQuotient.
Removed its sole proof import from
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation and replaced it
with the official upstream twin. The withdrawing file's imports disappear with it.

No mathematical dependency node is pruned: both
lem-weil-pbc-localization-at-prime-of-quotient and
lem-sbc-strict-henselization-surjective-quotient remain used by the upstream theorem.
The geometric consumer retains its local-presentation node and the localized-divisor
node through the latter's corrected upstream attachment. The only DAG parent is
adapted in this packet; no quarantine parent references the retiring declaration.
No blueprint unit route is bypassed and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not identify the concrete retirement assignment:
coord/retire-items.tsv lists this already proved, zero-hole duplicate for migration.
The upstream theorem has a different compatible-action interface, so replacing only
the import does not preserve the consumer proof. Explicit witnesses recover the full
original existential statement and preserve the consumer's mathematical strength.

The prescribed semantic search found localization/residue-field and henselian lemmas;
Loogle located IsLocalization.algEquiv and its API; Mathlib grep located the quotient
and localization lift equations. Local rg found the exact upstream theorem and the
upstream consumer's complete witness construction, which is the shortest available route.
Read Stacks algebra.tex at lemma-quotient-strict-henselization (Tag 05WS) and
proposition-localize-quotient (Tag 00CT), and the current blueprint unit text.
No new statement is needed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
