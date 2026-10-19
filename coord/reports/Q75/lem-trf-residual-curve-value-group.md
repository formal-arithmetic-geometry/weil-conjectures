## Worker report

The item is stated as `residual_curve_value_group` in
`Sheaf.TraceFormula.ResidualCurveValueGroup`, with proof `sorry`. Its signature
is unchanged from the returned packet. The helper module
`Sheaf.RingTheory.ValuationComapResidue` now declares only the canonical residue
algebra structure, using the already published restriction and residue map from
`Sheaf.FieldTheory.AbhyankarInequality`. No statement correction is needed.

Each hypothesis and clause of the item is rendered as follows:

- Fields and their inclusion: `(K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L]`, with embedding `algebraMap K L`. A ring homomorphism between
  fields is injective. The universes `u` and `v` are independent.
- Finite field generation: `(hfg : (⊤ : IntermediateField K L).FG)`, rather
  than finite generation as a ring algebra.
- Transcendence degree one: `(htrdeg : Algebra.trdeg K L = 1)`.
- Separably closed ground field: `[IsSepClosed K]`. Neither perfectness nor
  algebraic closedness is assumed.
- Valuation ring: `(O : ValuationSubring L)`. Mathlib requires an element or
  its inverse to lie in the subring, and supplies `IsFractionRing O L`.
- Restricted valuation ring: `O.comap (algebraMap K L)`, precisely the inverse
  image of O under the ground-field embedding, hence the stated `O ∩ K`.
- Maximal ideals and residue fields: `IsLocalRing.maximalIdeal` is the ideal
  of nonunits, and `IsLocalRing.ResidueField` is its quotient field.
- Residue transcendence degree: `hres` explicitly supplies
  `O.comapResidueAlgebra (algebraMap K L)` to `Algebra.trdeg`, giving exactly
  `trdeg_{κ(R)} κ(O) = 1` for the canonical restricted residue extension.
- First conclusion: `∀ z : Lˣ, ∃ c : Kˣ, ∃ a : Oˣ, ...`, with
  `((a : O) : L) = (z : L) / algebraMap K L (c : K)`. A unit of O with this
  image says exactly that `z/c` belongs to `Oˣ`.
- Integral refinement: `∀ z : O, z ≠ 0 → ∃ c : O.comap (algebraMap K L),
  c ≠ 0 ∧ ∃ a : Oˣ, ...`, with the same division identity. These are exactly
  the nonzero z in O and the nonzero c in R.
- Maximal-ideal refinement: for `z : O` with
  `z ∈ IsLocalRing.maximalIdeal O` and `z ≠ 0`, the witness c belongs to
  `IsLocalRing.maximalIdeal (O.comap (algebraMap K L))`, is nonzero, and the
  same division identity exhibits `z/c` as a unit of O.

The conjunction retains all three assertions. The theorem docstring retains
all four proof steps: relative Abhyankar, rational-rank-zero torsion,
divisibility and torsion-free cancellation, then the integral and ideal unit
calculations. No value-group construction is an additional hypothesis.

Dependency declarations used:

- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`.
- `def-kun-transcendence-degree`:
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field`.
- `def-weil-residue-field`: the recorded scheme residue-field construction
  uses Mathlib's `IsLocalRing.ResidueField` and `IsLocalRing.ResidueField.map`;
  the valuation-ring statement uses those same underlying definitions.
- `def-trf-valuation-comap-residue`:
  `Sheaf.RingTheory.ValuationComapResidue`,
  `ValuationSubring.comapResidueAlgebra`.
- Reused canonical helpers: `Sheaf.FieldTheory.AbhyankarInequality`,
  `ValuationSubring.comapInclusion`,
  `ValuationSubring.comapInclusion_isLocalHom`, and
  `ValuationSubring.comapResidueFieldMap`.

The Abhyankar module is a public import of the helper because its residue map
is part of the construction. The now-published proof dependency
`Sheaf.GroupTheory.RationalRankZeroTorsion` is imported without `public` in the
item. Its declaration is
`AddCommGroup.exists_pos_zsmul_eq_zero_of_rationalRank_eq_zero`.
`lem-trf-separably-closed-value-group-divisible` still has no recorded Lean
module, so no speculative import is added for it.

Edge cases checked: the trivial valuation O = L, R = K is admitted; its zero
maximal ideals make the third clause vacuous. The integral clause includes
units and requires no nonunit ground representative in that case. Zero is
excluded exactly where the node excludes it. Higher-rank valuations,
independent universes, positive characteristic, and imperfect separably
closed fields remain admitted. No finite-field or cardinal-size restriction
has been added. There is no STATEMENT-DISPUTED issue.

The retained packet records these searches:

- LeanFinder: “In a residually transcendental extension of transcendence degree
  one over a separably closed field every nonzero element has a ground field
  multiple which is a valuation unit”: eight valuation/unit hits, no exact
  residual-curve statement.
- Loogle: `ValuationSubring, IsUnit`: four hits, including
  `ValuationSubring.valuation_eq_one_iff`, no exact item.
- Mathlib grep: `residu.*transcend|transcend.*residu|residual.*curve` in
  RingTheory: one unrelated quasi-finite-polynomial hit.
- Project and upstream rg: item id, `residualCurve`, `residual_curve`, and
  residue/transcendence patterns: no existing item statement.

The retained source reading is Temkin, *Stable modification of relative
curves*, Proposition 4.3.1 proof, first stage, printed p. 28. Its equality of
values and ground representative give the three clauses above.

## New nodes

`def-trf-valuation-comap-residue` records the canonical residue extension of
R = f⁻¹(O), including its induced residue algebra. Its hypotheses are
`{K : Type u} {L : Type v} [Field K] [Field L] (O : ValuationSubring L)
(f : K →+* L)`. The restricted inclusion, locality, and quotient map are now
reused from `Sheaf.FieldTheory.AbhyankarInequality`. The only declaration in
this node's module is `ValuationSubring.comapResidueAlgebra`, with real data
`(O.comapResidueFieldMap f).toAlgebra`. There is no new postponed helper theorem.
The existing locality theorem supplies the proof needed by the existing
quotient construction. Thus no arbitrary embedding or existence choice is
introduced. Identity embeddings, trivial valuations, independent universes,
and arbitrary characteristic are included.

Its source is Temkin §2.1 and Proposition 4.3.1, p. 28. Its original searches
are retained verbatim in `mathlib_searches`: LeanSearch found the general
`IsLocalRing.ResidueField.map`; Loogle found the valuation comap and carrier
lemmas; Mathlib grep found no restricted residue extension. The recorded DAG
and blueprint search found no separate definition node for the residue
algebra. Upstream `ValuationSubring.comapResidue` constructs a valuation from
a valuation on a residue field and is a different notion. The repair search
found the now-published restricted residue map in AbhyankarInequality, so the
module reuses it and adds only its algebra structure. The node's mathematical
statement, searches, and ancestry remain as in the retained packet; its Lean
record lists only the declaration actually provided here.

## Repair of return 07199231e302

The returned head duplicated `ValuationSubring.comapInclusion` and
`ValuationSubring.comapInclusion_isLocalHom`, already declared by
`Sheaf.FieldTheory.AbhyankarInequality`. Removed both declarations and imported
that module. Also removed `comapResidueMap`: the published
`comapResidueFieldMap` has the same canonical quotient construction and is
used directly. No declaration was renamed to conceal a duplicate.

Read the full published module through `scompile.py --source` and compared
its signatures and docstrings with the retained helper. Its restricted map
is the same `RingHom.restrict`, its locality statement has the same field
hypotheses, and its residue map is the same `ResidueField.map`. The remaining
algebra definition is therefore unchanged mathematically and definitionally
uses the exact residue algebra occurring in `abhyankar_inequality`.

Before repair the required saved-packet dry run passed at `770301089b`.
Its per-file checks did not expose the independent reader's cross-module
collision; the explicit collision return is repaired despite that pass.
Compared the retained item with the current shared node: only `lean` and the
single added helper dependency differ. The theorem signature is retained
verbatim. Delivery wrappers rebase the packet onto the current
`newtargets-dag` base. No direct Git command or live-source edit was used.

## Second reading by Q75

Worker self-check for this repair; the maintainer supplies the independent
review. No other agent was started. Read the node, both delivered modules,
and the full reused Abhyankar module. The fields and algebra map, finite field
generation, field transcendence degree one, separable closedness, valuation
subring and its comap, and canonical residue transcendence degree one match
the node. The three conclusions separately quantify over L units, nonzero
integral elements, and nonzero maximal-ideal elements, and supply ground
representatives in K units, nonzero R, and nonzero m_R respectively, with the
same division identity and a unit of O.

The mismatch found was duplicate ownership of the restricted inclusion and
its locality theorem, plus a second construction of the same residue map.
Those declarations have been removed, and their published versions are
imported. The helper now contains only the algebra structure obtained by
`RingHom.toAlgebra` from that published map. It has no `sorry` data or new
postponed property. Only the item's theorem is left as `sorry` in this packet.
The theorem's statement and edge cases are unchanged. Recorded signatures
were checked verbatim, every variable and universe is explicitly bound,
and delivered Lean lines remain within 100 characters.

Repair validation: `scompile.py Q75 lem-trf-residual-curve-value-group`
compiled both delivered modules separately in dependency order, including
sandbox and library-name checks, with exit code 0 and no compiler warnings
or errors. The helper imports AbhyankarInequality in these successful checks,
so the reported duplicate names are no longer declared twice.
