## What changed

Retired the zero-hole Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient copy under
its coord/retire-items.tsv assignment. deleted.txt withdraws only that module.
Both direct consumers now privately import the official
WeilConjectures.RingTheory.StrictHenselizationSurjectiveQuotient.

Algebra.IsStrictHenselization.localized_divisor_quotient keeps its public signature.
Its proof now chooses the canonical separable closure of the new base residue field,
constructs the quotient action with RingHom.liftOfSurjective, proves the composition
identity, and applies the upstream compatible-action theorem. The final ideal equality
transports the action and proof to the required quotient. The unused maximal-ideal
containment calculation was removed. The coordinate-stratum consumer only changes its
proof import. No upstream file changes.

The retiring node now attaches to the upstream theorem, with the actual upstream
signature and a note deriving its unchanged existential statement. Its proof dependencies
are the finality and quotient-base-change nodes used by the upstream proof. The localized
consumer's node records its changed construction. No statement, definition, target,
or blueprint unit route is changed. See
coord/changes/M3-retire-strict-henselization-surjective-quotient.md.

Validation: both adapted consumer files compiled on the project server, without errors
or warnings (2.8 s and 2.5 s). Import-direction checks accept both new imports.
The complete old existential signature was separately derived from the upstream
interface in a sandbox-only attachment check (1.7 s); #print axioms reports exactly
[propext, Classical.choice, Quot.sound]. No new declaration from that check is delivered.
This also checks the I = 0 case: the construction descends the original action along pi,
and does not choose an arbitrary quotient action. B is a nonzero local ring, excluding
the impossible unit-ideal kernel. No regularity, domain, or Noetherian hypothesis is added.

Complete server-compiled attachment check, proving the original existential statement:

```lean
module

public import WeilConjectures.RingTheory.StrictHenselizationSurjectiveQuotient

@[expose] public section

universe u
namespace Algebra

/-- Attachment check: recover the full old existential statement from upstream. -/
theorem exists_surjective_quotient_attachment
    (A K C B : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField B) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField B) L)
      (_ : Algebra B L) (_ : IsScalarTower B (IsLocalRing.ResidueField B) L)
      (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      IsStrictHenselization B L (C ⧸ I.map (algebraMap A C)) := by
  have _ := hI
  let L := SeparableClosure (IsLocalRing.ResidueField B)
  let : Algebra B L := ((algebraMap (IsLocalRing.ResidueField B) L).comp
    (IsLocalRing.residue B)).toAlgebra
  have : IsScalarTower B (IsLocalRing.ResidueField B) L :=
    IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  let Q := C ⧸ I.map (algebraMap A C)
  let q : C →+* Q := Ideal.Quotient.mk _
  have hk : RingHom.ker π ≤ RingHom.ker (q.comp (algebraMap A C)) := by
    rw [hker, ← RingHom.comap_ker, Ideal.mk_ker]
    exact Ideal.le_comap_map
  let β : B →+* Q := π.liftOfSurjective hπ ⟨q.comp (algebraMap A C), hk⟩
  let : Algebra B Q := β.toAlgebra
  have hcomp : (algebraMap B Q).comp π = q.comp (algebraMap A C) := by
    ext a
    exact π.liftOfSurjective_comp_apply hπ ⟨q.comp (algebraMap A C), hk⟩ a
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    β.toAlgebra, hC.surjective_quotient A K C B L π hπ I hker hcomp⟩

#print axioms exists_surjective_quotient_attachment

end Algebra
```

## Proved and sorry left

This is a retirement repair with zero holes in the assigned module, not a hole closure.
Closed: 0 of 0. Added: 0. Split off: 0.

Algebra.IsStrictHenselization.localized_divisor_quotient remains completely proved;
its proof now uses the upstream theorem with explicitly constructed compatible structures.
Algebra.exists_surjective_quotient_attachment is a sandbox-only verification of the full
old statement and uses only the three allowed axioms.

The adapted consumer's pre-existing hole is unchanged:
AlgebraicGeometry.Scheme.IdealSheafData.coordinate_maximal_branch_stratum
(node lem-trf-nc-coordinate-max-stratum). No sorry remains in the retired module and
no other delivery file contains a sorry.

## No longer needed

Withdrawn module: Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient.
Removed its imports from Sheaf.RingTheory.StrictHenselizationLocalizedDivisorQuotient
and Sheaf.TraceFormula.CoordinateMaximalBranchStratum; both use the official twin.

The retired assembly's direct proof dependencies
Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientData
(lem-sbc-strict-henselization-surjective-quotient-data) and
Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore
(lem-sbc-strict-henselization-surjective-quotient-core) are no longer needed for this route.
They are not withdrawn: independent DAG parents may still need them. The adopted upstream
proof still uses lem-sbc-pointed-etale-quotient-final and
lem-sbc-surjective-quotient-base-change, through their upstream modules; those remain
needed. No other proof dependency or blueprint unit is pruned.

All DAG references to the retired node retain the same mathematics via its upstream
attachment, including the coordinate-stratum, localized-divisor, and complete-local-branch
approximation parents. Quarantined consumer archives remain intact. Source import-closure
checks find no new Sheaf/upstream twin pair; the coordinate consumer's existing
StrictHenselizationStructuralMap pair is unrelated and remains with its claimed worker.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not mention the current retire assignment: the module has
zero direct sorries, as the queue's retire row and the human's retirement hand-off explain.
The official twin proves the stronger compatible-action interface, whereas the old
Sheaf theorem packages the closure and action existentially. Replacing the import alone
would therefore break localized_divisor_quotient. This delivery supplies the missing
explicit constructions and preserves that consumer's exact statement.

Searches: the prescribed leanfinder query returned HenselianLocalRing and completion
results, without the project's colimit quotient theorem; loogle did not know the project
identifier. Local rg found the already proved upstream quotient theorem and its explicit
hcomp API, which provides the complete shorter route. No new node is needed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
