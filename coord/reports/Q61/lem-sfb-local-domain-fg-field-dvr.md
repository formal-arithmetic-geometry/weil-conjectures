## Worker report

The module `Sheaf.RingTheory.DiscreteValuationRing.FinitelyGeneratedExtension` states
`IsLocalRing.exists_discreteValuationSubring_of_fg_extension`, with `sorry` as its only
proof. It introduces no definitions. Source read in full: Stacks Project, Algebra,
Tag 00PH, `lemma-exists-dvr`, including all three proof paragraphs in
`literature/stacks-project/algebra.tex:29312`. The current node already has its approved
stage-1 split by Q26; this delivery changes only `lean`, not that split. The example
CompactObject module is now withdrawn, so the module-mode/public-section convention
in the standing brief and current upstream modules supplies the header convention.

Each hypothesis and conclusion is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` |
| R is nonzero and has no zero divisors | `[IsDomain R]`, which includes `Nontrivial R` |
| R is local, with a unique maximal ideal | `[IsLocalRing R]`; the distinguished ideal is `IsLocalRing.maximalIdeal R` |
| R is Noetherian | `[IsNoetherianRing R]` |
| R is not a field, equivalently its maximal ideal is nonzero | `(hR : ¬ IsField R)`; the equivalence is `IsLocalRing.isField_iff_maximalIdeal_eq` |
| K and L are fields | `(K : Type v) (L : Type w) [Field K] [Field L]` |
| R is included in K, with every element of K a ratio from R | `[Algebra R K] [IsFractionRing R K]`; the fraction-ring algebra map from a domain is injective |
| K is included in L | `[Algebra K L]`; a unital homomorphism of fields is injective |
| L is generated as a field by finitely many elements over K | `(hL : (⊤ : IntermediateField K L).FG)`; `FG` means that the intermediate field equals `IntermediateField.adjoin K` of a finset |
| A is a subring of this prescribed L | `∃ (A : LocalSubring L)` and its underlying `A.toSubring` |
| A is a DVR | `IsDiscreteValuationRing A.toSubring`; the underlying ring is automatically a domain because it is a subring of a field |
| A contains R by the prescribed inclusion into L | `(f : R →+* A.toSubring)` and `A.toSubring.subtype.comp f = (algebraMap K L).comp (algebraMap R K)` |
| Every element of L is a quotient from A | `IsFractionRing A.toSubring L`, using the canonical subring algebra structure, hence the actual inclusion into L |
| The maximal ideal contracts to the maximal ideal of R | `Ideal.comap f (IsLocalRing.maximalIdeal A.toSubring) = IsLocalRing.maximalIdeal R` |

The ring-map equality is the precise expression of containing the given copy of R:
its right side is injective, so f is injective too, and its composite into L is fixed.
It imposes no extra structure or alternative embedding. LocalSubring merely packages
a subring and its local-ring property, already required for a DVR. Its use does not
restrict A. No independent universe equality is imposed: `universe u v w` and all
objects and hypotheses are explicitly bound. There are no auto-bound variables.

Statement-dependency declarations read with their signatures and docstrings:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, together with `isNoetherianRing_iff_ideal_fg`. This is exactly
  finite generation of every ideal.
- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, a commutative ring
  with nontriviality and inverses for nonzero elements, inherited from DivisionRing.
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing`, extending `IsPrincipalIdealRing` and `IsLocalRing` with
  nonzero maximal ideal. The theorem does not require a chosen uniformizer; the node's
  uniformizer terminology is supported by `irreducible_iff_uniformizer`.

Other standard Mathlib interfaces reused without copies: `LocalSubring` from
`Mathlib.RingTheory.LocalRing.LocalSubring`, `IntermediateField.FG` from
`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, and `IsFractionRing` from
`Mathlib.RingTheory.Localization.FractionRing`. Read their definitions: FG is
adjoining a finset as a field, and the fraction-ring predicate is localization at
nonzero divisors. In a domain these are precisely the nonzero denominators.

All recorded proof-dependency modules are imported privately, including
`WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres` and
`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`. The one
proof dependency `lem-sfb-local-domain-birational-dimension-one` has no Lean record
or Mathlib match at this reading; no module import exists to add for it. It is only
a proof dependency, not a prerequisite for typing this statement. The declaration
docstring carries all eight node proof steps verbatim in mathematical content,
including the polynomial-origin reduction, inseparable finite extensions, and the
successive contractions of maximal ideals.

Edge cases checked before writing:

- L = K is allowed: the hypothesis FG admits the empty generating set and the
  conclusion is a DVR in the original fraction field.
- Zero transcendence degree, nontrivial finite extensions, and inseparable
  extensions are all allowed. There is no separability hypothesis or finite-algebra
  hypothesis. Positive transcendence degree is allowed as FG uses subfields.
- Higher-dimensional local domains are allowed; there is no dimension hypothesis.
- If R is itself a DVR and L = K, its image in K is a valid A. For R = Z localized
  at a prime and L = Q(t), the source's origin localization and normalization
  construction retains the full prescribed fraction field.
- The zero ring is excluded by IsDomain, just as the node requires. A field R is
  excluded by hR. Omitting this exclusion would fail already for R = K = L a field,
  because the only subring of L containing R would be L, which is not a DVR.
- All characteristics and independent universes u, v, w are admitted.

Searches for exact reuse (all run for Q61 and this item):

1. `msearch.py leanfinder`, query: "A Noetherian local domain that is not a field is
   dominated by a discrete valuation subring of a prescribed finitely generated
   extension of its fraction field". Eight hits, including
   `IsDiscreteValuationRing.TFAE`,
   `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`,
   `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, and valuation
   subring existence. These characterize an existing ring or give a general valuation
   ring; none supplies the required DVR in the prescribed extension.
2. `msearch.py loogle`, query: `IsDiscreteValuationRing, IsFractionRing`.
   Twelve hits, including `exists_units_eq_smul_zpow_of_irreducible`,
   `isRankOneDiscrete`, `equivValuationSubring`, and `exists_lift_of_le_one`.
   Each already assumes a DVR and fraction field; none states the item.
3. `msearch.py grep`, query: `exists.*[Dd]iscreteValuationRing|dominat|[Aa]kizuki`,
   subdirectory `RingTheory`. Ten hits, chiefly valuation-ring domination and
   LocalSubring's domination order. Read `LocalSubring.exists_le_valuationSubring`:
   it does not guarantee discreteness or prescribe the fraction field.
4. `msearch.py leansearch`, query: "A discrete valuation subring of a prescribed
   finitely generated field extension dominates a Noetherian local domain and has
   that extension as fraction field". Eight hits: DVR constructors, valuation-subring
   constructors, `exists_lift_of_le_one`, and `LocalSubring.exists_le_valuationSubring`.
   No exact theorem.
5. `rg -n 'exists.*[Dd]iscreteValuationRing|dominat|[Aa]kizuki'` on both project roots,
   and the same-name search in Mathlib, Sheaf, WeilConjectures, and the upstream name
   index: no declaration with this full conclusion. Read the closest upstream
   `IsLocalRing.exists_isDiscreteValuationRing` in
   `WeilConjectures.RingTheory.DiscreteValuationRing.Dominating`: it gives an abstract
   DVR with an injective local map, and says nothing about its fraction field being
   the prescribed L. It is therefore insufficient for an existing binding here.
6. `grep -rn 'lem-sfb-local-domain-fg-field-dvr' lean/WeilConjectures`:
   no upstream attachment. No duplicate notion is introduced.

No node fault, statement correction, new node, dependency repair, or mathematical
statement dispute was found. The earlier worker's stage-1 live-state refusal is
inapplicable to this stage-2-only packet: the existing split and review are retained.

Validation: the first scompile pass elaborated both sandbox and library module and
reported only a docstring whitespace warning. Removed the extra blank line before
the declaration docstring's closing delimiter. The final scompile pass is clean in both sandbox and library module checks (2.2 s
and 1.8 s). The first delivery preflight requested that lean.statement stop immediately
before the definition delimiter `:=`; adjusted that record boundary to the tool
convention, preserving the signature verbatim. Re-running the prescribed dry run.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
