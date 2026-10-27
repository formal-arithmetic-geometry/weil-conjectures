## Worker report

The module `Sheaf.RingTheory.CharacteristicZeroDedekindExcellent` states the general
Dedekind-domain result as `isExcellent_of_dedekind_of_charZero` and its final DVR
specialization as `IsDiscreteValuationRing.isExcellent_of_fractionField_charZero`.
Both proofs are `sorry`; there are no new definitions, auxiliary nodes, dependency
repairs, or statement corrections. The copied node changes only `lean`.

The sources read were Stacks `more-algebra.tex`, Tag 07QW,
`proposition-ubiquity-excellent`, clauses (1) and (4) and its proof, together with
Tags 07PX and 07PJ; and `algebra.tex`, Tag 00PD, `lemma-characterize-dvr`, its five
equivalent conditions and proof. The theorem docstrings reproduce the node's six
Dedekind steps and seventh DVR-specialization step with their dependency citations.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The commutative domain `A` is `(A : Type u) [CommRing A] [IsDomain A]`.
* Noetherianity is `[IsNoetherianRing A]`, exactly the recorded Noetherian predicate.
* Integral closedness in the fraction field is `[IsIntegrallyClosed A]`.
  This is the recorded normal-domain notion, not normality of an unrelated ring.
  Mathlib's `isIntegrallyClosed_iff K` identifies it with every integral element of
  the specified fraction field `K` lying in the image of `A`.
* Every nonzero prime is maximal is the literal predicate
  `hmax : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p.IsMaximal`.
  It does not require a nonzero prime to exist or impose dimension exactly one.
* The named fraction field is `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`, with independent explicitly bound universes `u v`.
  `[CharZero K]` is precisely the characteristic assumption in the node.
* The conclusion is `IsExcellent A`, using the dependency's four-condition
  excellence predicate through `Sheaf.RingTheory.ExcellentRing`.
* The field clause is included in the general theorem: a field has no nonzero
  prime ideals, so `hmax` is vacuous. No non-field assumption is present there.
* For the final clause, `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]` is exactly the recorded local PID with nonzero
  maximal ideal. Its fraction field has the same four field/algebra/localization/
  characteristic binders, with `A` replaced by `R`; the conclusion is `IsExcellent R`.
* The equivalence of DVR descriptions in the node is explanatory, not an extra
  assumption: the recorded Mathlib DVR class is used unchanged. Tag 00PD and the
  imported Mathlib TFAE identify it with the local principal-ideal, Noetherian local
  principal-maximal-ideal, and Noetherian local normal dimension-one forms.
* Neither statement assumes completeness, henselianity, finite type over the integers,
  equal characteristic, characteristic zero of the residue field, or a chosen uniformizer.

Statement dependency declarations, read with their full definitions and docstrings:

| Node | Module | Declaration used |
| --- | --- | --- |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsIntegrallyClosed |
| def-exc-excellent-ring | Sheaf.RingTheory.ExcellentRing | IsExcellent |
| def-sc-discrete-valuation-ring | Mathlib.RingTheory.DiscreteValuationRing.Basic | IsDiscreteValuationRing |

`IsFractionRing` comes from `Mathlib.RingTheory.Localization.FractionRing`.
The dependency `def-sc-discrete-valuation-ring` is a Mathlib leaf without a `lean`
record; its `mathlib_match` supplies the class directly, as the brief requires.
The normal-ring node explicitly records its domain specialization, so no repair
of its broader prime-local normal-ring clause is necessary here.

The proof plan imports all recorded proof-dependency modules. In particular it uses
`IsRegularRing.isUniversallyCatenary` from
`Sheaf.RingTheory.RegularRingUniversallyCatenary`,
`AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero` from
`WeilConjectures.RingTheory.DVRCompletionRegular`, and
`isOpen_regularLocus_of_residueField_finite_models` from
`Sheaf.RingTheory.JTwoResidueFieldCriterion`. The G-ring predicate comes from its
published upstream module `WeilConjectures.RingTheory.GRing`. The ring clauses of
`def-weil-regular-scheme` use `IsRegularRing` and `IsRegularLocalRing` from Mathlib;
its recorded scheme module is also imported. The remaining Mathlib proof imports
supply `ringKrullDim`, `Localization.AtPrime`, `IsPurelyInseparable`,
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`,
`IsDiscreteValuationRing.ringKrullDim_eq_one`,
`PrincipalIdealRing.isNoetherianRing`,
`PrincipalIdealRing.to_uniqueFactorizationMonoid`, and
`UniqueFactorizationMonoid.instIsIntegrallyClosed`.

Edge cases checked mathematically before writing:

* `A = ℚ`: the field case is included; requiring dimension exactly one would lose it.
* `A = ℤ`: a nonlocal Dedekind domain is included. Locality is not assumed in the
  main theorem, and characteristic zero of the fraction field suffices.
* `R = ℤ_(p)` and `R = ℤ_p`: mixed-characteristic DVRs are included. Their residue
  characteristic is positive, which is permitted; completeness of the first example
  is not required.
* Characteristic-zero fields of arbitrary size are included by the general theorem,
  with any chosen isomorphic fraction field in any universe admitting it.
* A positive-characteristic field or DVR fails `[CharZero K]`; that hypothesis is
  not dropped, and excellence of arbitrary positive-characteristic DVRs is not claimed.
* The zero ring is excluded exactly by `IsDomain`. A field is excluded only from
  the DVR specialization by the canonical DVR class, as the source specifies.

Searches actually run (via the prescribed wrapper):

* `leanfinder`, query `Every Dedekind domain with fraction field of characteristic zero
  is excellent`: eight hits. They are Dedekind predicates, localization-at-prime/DVR
  facts, integral closure and dimension-at-most-one facts. No excellence conclusion.
* `loogle`, query `"Excellent", "IsDedekindDomain"`: zero hits.
* `grep`, query `IsExcellent|ExcellentRing|excellent|catenary` in Mathlib `RingTheory`:
  zero hits.
* Repository `rg` on `lean/WeilConjectures` and `lean/Sheaf` for excellence and
  Dedekind/characteristic-zero combinations: the existing excellence predicates,
  theorems for fields, integers and complete local rings, and stability results exist,
  but no theorem for the full class of characteristic-zero Dedekind domains or DVRs.
* Exact item-id `grep -rn` in `lean/WeilConjectures`: no matches.
* Exact proposed declaration-name `rg` in Mathlib, both project trees and
  `dag/lean_names_upstream.json`: no matches.

No statement dispute or node fault was found. No new nodes were needed.

## Second reading by Q112

A separate second pass through the node, source and completed module found no mismatch.
The general statement lists domain, Noetherianity and integral closedness individually;
its explicit nonzero-prime hypothesis preserves fields. `IsFractionRing A K` links the
characteristic assumption to the actual fraction field, rather than to an arbitrary field
extension. The second theorem needs only the canonical DVR class and that fraction-field
assumption: it adds no regularity, completeness, henselianity or residue-characteristic
assumption. Every theorem is named, has the source/blueprint tag and natural-language proof,
and ends in `sorry`. `autoImplicit` is disabled and both universes are explicitly declared.
No change was necessary on this pass. This is the dispatcher's single-worker pass;
the maintainer's independent delivery review is separate, and no other agent was started.

Validation: `scompile.py` compiled the module cleanly as both a sandbox module and its
library module (7.0 s and 3.7 s). `deliver2.py --no-push` then returned
`OK (dry run)` with commit `fb8626032b4`: server preflight and per-file compilation passed.
