## Worker report

The module `Sheaf.RingTheory.LocalDomainSameFieldDvr` states
`IsLocalRing.exists_dvr_subalgebra_same_fraction_field`, with `sorry` as its only proof.
The node's mathematical statement, proof and dependencies are unchanged. Only its `lean`
record is added. There are no new nodes, helper definitions or dependency repairs.

Source read: `literature/stacks-project/algebra.tex`, Tag 00PH,
`lemma-exists-dvr`, statement and full proof, specialized to L = K.
The declaration docstring gives the node's five-step proof: dimension-one birational
reduction (00P8), integral closure and a prime over the closed point (09IG), maximality
and nonzeroness of that prime (031F), localization inside K and the DVR criterion
(00GY, 034X), and contraction of maximal ideals along the resulting inclusions.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| B is a commutative ring | `(B : Type u) [CommRing B]` |
| B is Noetherian | `[IsNoetherianRing B]` |
| B is a nonzero integral domain | `[IsDomain B]`, which includes nontriviality and absence of zero divisors |
| B is local with a unique maximal ideal | `[IsLocalRing B]`; its ideal is `IsLocalRing.maximalIdeal B` |
| B is not a field, equivalently its maximal ideal is nonzero | `(hB : ¬ IsField B)` |
| K is a field | `(K : Type v) [Field K]` |
| K contains B, and each element is b/c with c nonzero | `[Algebra B K] [IsFractionRing B K]`; for a domain the fraction-ring structure makes `algebraMap B K` injective and represents all fractions |
| A is a subring of this specific K containing B | `∃ (A : Subalgebra B K), ...`; Mathlib's subalgebra of a commutative ring has the underlying subring and contains the image of `algebraMap B K` |
| A is a DVR | the dependent existential `(_ : IsDiscreteValuationRing A)`; A inherits its domain and ring structures from K |
| A has fraction field K | `IsFractionRing A K`, using the canonical subtype inclusion into K, rather than an arbitrary map |
| The maximal ideal contracts to that of B | `(IsLocalRing.maximalIdeal A).comap (algebraMap B A) = IsLocalRing.maximalIdeal B` |
| Thus B into A is local | `IsLocalHom (algebraMap B A)` |

The maps B into A and A into K are the canonical subalgebra maps, whose composite
is the given map B into K. No freely chosen homomorphism or independent algebra
structure replaces the inclusion. A `Subalgebra B K` adds no extra mathematical
condition beyond being a subring of K containing B: its scalars act by multiplication
by elements of B. The final local-hom clause records explicitly the stated consequence
of the contraction equality, without changing its strength.

Dependency declarations used, with their source signatures and docstrings read:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, together with its definition as `IsNoetherian B B`
  and `isNoetherianRing_iff_ideal_fg`. Available through the public DVR import.
- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, extending
  `CommRing` and `DivisionRing`. Available through the public fraction-ring import.
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, a local principal ideal domain
  with nonzero maximal ideal. This is exactly the recorded Mathlib match; this item
  does not use the uniformizer clause of the definition node.
- The supporting Mathlib notions are `Subalgebra` from
  `Mathlib.Algebra.Algebra.Subalgebra.Basic` and `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`; both are existing constructions.

Proof-dependency modules that are already stated are imported privately:
`WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`
(`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`),
`WeilConjectures.RingTheory.DimOneResidueFieldsFinite`
(`Ideal.dim_one_residue_fields_finite`), and the Mathlib modules
`Localization.AtPrime.Basic`, `Localization.LocalizationLocalization`,
`IntegralClosure.IntegrallyClosed`, `DedekindDomain.Dvr` under `Mathlib.RingTheory`.
The integral-closure construction is also imported through the normalization module.
`lem-sfb-local-domain-birational-dimension-one` currently has neither a Lean module
nor a Mathlib match, so no import can yet be added for that proof-only dependency.
It is not needed to type the theorem's statement. No import cycle is introduced.

Edge cases checked before writing:

- A field B is excluded, as necessary: if B = K, any subring of K containing B is K
  and cannot be a DVR. `hB` records precisely that exclusion.
- The zero ring is excluded by the nontriviality in `IsDomain B` and cannot embed
  unitaly into a field. This matches the explicit B nonzero clause.
- If B is already a DVR, its image in K is the expected witness. The statement
  does not require an overring strictly larger than B.
- For `k[t²,t³]_(t²,t³)`, the normalization `k[t]_(t)` gives the expected DVR in
  the same field. Normality of B is not assumed.
- For `k[x,y]_(x,y)`, the dimension-one local overring obtained on the y/x chart
  admits the prescribed field k(x,y) and contracts its maximal ideal to (x,y).
  The statement does not restrict the dimension of B to one.
- The universe parameters `u` and `v` are independent and explicitly bound.
  The witness A is a genuine subring of K in K's universe, with no equality
  imposed between the universes of B and K. No characteristic, completeness,
  excellence or residue-field finiteness restriction is added.

Searches performed with the prescribed `msearch.py NS` wrapper:

- LeanFinder: `A nonfield Noetherian local domain has a dominating discrete valuation
  subring in its prescribed fraction field`. Eight hits, including
  `IsDiscreteValuationRing.TFAE` and
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`.
  These classify or localize already given rings; none supplies this witness.
- Loogle: `IsDiscreteValuationRing, IsFractionRing`. Twelve hits, including
  `IsDiscreteValuationRing.equivValuationSubring` and
  `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`. They assume the DVR
  already exists and cannot attach this existence statement.
- Mathlib grep: `exists.*[Dd]vr|exists.*[Dd]iscreteValuationRing|dominat`, restricted
  to `RingTheory/DiscreteValuationRing`. Zero hits.
- LeanSearch: `Every nonfield Noetherian local domain admits a discrete valuation
  subring of its fraction field dominating the original domain`. Eight hits;
  `LocalSubring.exists_le_valuationSubring` supplies a valuation ring without
  discreteness. The other hits are DVR classifications and Dedekind localizations.
- Local `rg` in the project `WeilConjectures` and `Sheaf` trees for the new name,
  `exists.*[Dd]vr.*[Ss]ub`, `exists.*[Dd]iscreteValuation.*[Ss]ub`, `00PH`,
  domination and same-fraction-field phrases; and `grep -rn` for the exact node id
  in `WeilConjectures`. The only 00PH existence theorem is
  `IsLocalRing.exists_isDiscreteValuationRing` in
  `WeilConjectures.RingTheory.DiscreteValuationRing.Dominating`, whose full
  signature and docstring were read. It concludes an abstract injective local map
  into a DVR and omits the prescribed fraction-field condition. It is not an exact
  attachment. No declaration for this node or collision with the chosen name was found.
  The Sheaf generic-DVR criterion mentions this node in its proof docstring only.

The required example `Sheaf.CategoryTheory.CompactObject` was inspected; it is now
withdrawn and contains no declarations. This delivery uses the current module-mode
header, public statement imports, private proof imports, and exposed public section.
No statement fault or STATEMENT-DISPUTED issue was found.

Validation: the prescribed `scompile.py NS lem-sfb-local-domain-same-field-dvr`
compiled this module against the server's published build. Both the sandbox compile
(2.5 s) and library-module compile (1.8 s) finished without errors or warnings.
The dry-run preflight and final delivery follow this report.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
