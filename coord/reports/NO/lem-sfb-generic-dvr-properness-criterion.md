## Worker report

States `AlgebraicGeometry.isProper_iff_generic_dvr_extensions` in
`Sheaf.AlgebraicGeometry.Morphisms.GenericDvrPropernessCriterion`.
The only postponed proof is this named theorem. No definitions, helper axioms,
new nodes, or dependency replacements were needed. The natural-language node and
its dependencies are unchanged; only its `lean` record is supplied.

The previous worker confused the existing stage-1 review with a stage-2 completion.
The node has `reviewed` for the NR proof split, but neither `lean` nor `reviewed_lean`.
This delivery supplies its missing statement without changing the reviewed proof split.

Source read: `literature/stacks-project/limits.tex`, lines 3926–4022,
`limits-lemma-Noetherian-dvr-valuative-proper`, Tag 0208, especially (1) and (4)
and the boundary-DVR proof. The node specializes this to an integral source and
assumes separatedness, so existence suffices, while uniqueness follows independently
from separatedness (Tag 01L0). The docstring carries all nine argument steps of the
node, including its integral refinement of the Chow modification by reduced closure
of the generic point. The import plan includes all currently stated proof dependencies;
`lem-sfb-local-domain-same-field-dvr` has neither a Lean declaration nor a Mathlib match,
so its future module cannot yet be imported. It is a proof prerequisite only and is
explicitly named in the proof docstring.

Hypothesis-by-hypothesis and clause-by-clause match:

- Schemes R and S: `{R S : Scheme.{u}}`, with the universe `u` explicitly bound.
- S locally Noetherian: `[IsLocallyNoetherian S]`.
- Integral R: `[IsIntegral R]`, including nonemptiness; empty sources are correctly
  excluded by the node itself.
- The given morphism: `(f : R ⟶ S)`.
- Separatedness: `[IsSeparated f]`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two parts
  recorded by `def-weil-finite-type-morphism`.
- Generic point ξ: `genericPoint R`. An integral scheme is irreducible and sober,
  so this is its unique generic point. Choosing this existing canonical representative
  imposes no further hypothesis or restriction on the given generic point.
- Function field L = κ(ξ): `R.functionField`, the existing abbreviation for
  `R.presheaf.stalk (genericPoint R)`. For integral R this stalk is already a field;
  its residue-field quotient is canonically itself. No alternative field is chosen.
- DVR subring A of L: `(A : Subring R.functionField) [IsDiscreteValuationRing A]`.
  The subring inherits its commutative ring and integral-domain structures from L.
  The class means a local principal ideal domain which is not a field.
- Fraction field exactly L: `[IsFractionRing A R.functionField]`, for the canonical
  subring algebra structure, whose algebra map is the subtype inclusion.
- Arbitrary b: `(b : Spec (.of A) ⟶ S)`.
- Restrict b to the generic spectrum: `Spec.map (CommRingCat.ofHom A.subtype) ≫ b`.
  Thus the test map uses the actual inclusion A into the given L, not an unrelated
  algebra map or a larger fraction field.
- Required generic restriction of b: the equation
  `Spec.map (CommRingCat.ofHom A.subtype) ≫ b =
  R.fromSpecStalk (genericPoint R) ≫ f`.
- The canonical generic-point map to R: `R.fromSpecStalk (genericPoint R)`.
  `Scheme.fromSpecStalk` is the existing canonical map from the spectrum of the
  local ring; here that local ring is exactly L.
- Existence of an extension: `∃ a : Spec (.of A) ⟶ R`.
- Extension of the specified canonical generic map: the conjunct
  `Spec.map (CommRingCat.ofHom A.subtype) ≫ a = R.fromSpecStalk (genericPoint R)`.
- The extension is over b: the conjunct `a ≫ f = b`.
- Sufficiency and converse: `IsProper f ↔` this universally quantified existence
  property. Both implications are present.
- Uniqueness whenever an extension exists: a separate outer conjunct universally
  asserts `Subsingleton {a : Spec (.of A) ⟶ R // generic_restriction_equation ∧
  a ≫ f = b}`. This remains independent of existence and properness. The subtype
  is empty when there is no lift, and any two lifts have equal underlying morphisms
  when it is inhabited. The commutativity hypothesis on b is unnecessary in this
  uniqueness clause: existence of either candidate already implies it. Thus the
  clause is exactly the same at-most-one assertion, including the no-lift case.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (lines 56–59).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral` (lines 238–243).
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint` (lines 37–40)
  and `genericPoint`, supplied through the function-field abbreviation.
- `def-sc-function-field`: imports the recorded module
  `WeilConjectures.AlgebraicGeometry.FunctionField`, whose module docstring explicitly
  assigns the arbitrary integral-scheme clause to the existing `Scheme.functionField`.
  That abbreviation and its field instance were read in
  `Mathlib.AlgebraicGeometry.FunctionField`, lines 35–52. The component product
  `Scheme.functionFieldOfComponents` is for the other clause of that definition node.
- `def-sc-discrete-valuation-ring`: its `mathlib_match` is
  `IsDiscreteValuationRing` in `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  lines 56–60. The node is a Mathlib leaf and needs no replacement Lean record.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map` (lines 469–480).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (lines 40–42), and `IsSeparated` in the publicly
  imported separated-morphism module (lines 42–46).
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`
  (lines 39–46), together with `QuasiCompact` (QuasiCompact.lean, lines 38–46).
- The generic-point canonical map reuses `Scheme.fromSpecStalk` in
  `Mathlib.AlgebraicGeometry.Stalk`, lines 61–68. The standard fraction-field
  predicate is `IsFractionRing` in `Mathlib.RingTheory.Localization.FractionRing`,
  lines 52–54. These are existing constructions, not new independent notions.

Edge cases checked before writing:

- The integral source is nonempty by definition. An empty target admits no morphism
  from it, so the statement does not manufacture an excluded empty-source case.
- Properness gives existence for every test; separatedness alone gives at most one
  extension even before the equivalence is used. An empty lift subtype is subsingleton.
- Fields themselves are excluded as DVRs by the class's nonzero-maximal-ideal field;
  no spurious trivial-valuation hypothesis was inserted.
- If L has no DVR subring (for example a finite field), the universal condition is
  allowed to be vacuous. No nonemptiness of the test family is assumed by either
  the source or the Lean statement.
- Subrings have the universe of the fixed L, and range over every subring of L.
  There is no independently smaller test-ring universe that could hide valuations.
- No characteristic, dimension, algebraic-closure, regularity, or global Noetherianity
  hypothesis has been added. S is only locally Noetherian, as in Tag 0208.

Searches actually run through `msearch.py NO lem-sfb-generic-dvr-properness-criterion`:

- LeanFinder: “A separated finite type morphism from an integral scheme to a locally
  Noetherian scheme is proper if and only if its generic point extends over every DVR
  subring of its function field”. Eight hits, including `IsProper.of_valuativeCriterion`
  and `IsSeparated.valuativeCriterion`; none restricts to the generic-field DVR tests.
- Loogle: `"IsProper", "IsDiscreteValuationRing"`. Zero hits.
- Mathlib grep: `valuativeCriterion|[Dd][Vv][Rr]|discrete valuation`, subdirectory
  `AlgebraicGeometry`. Eleven hits, in ProjectiveSpectrum/Proper and ValuativeCriterion.
  ValuativeCriterion.lean, lines 29–30, explicitly lists the Noetherian DVR restriction
  as future work; the existing criterion quantifies over all valuation-ring diagrams.
- LeanSearch: “Properness of a separated finite type morphism from an integral scheme
  can be tested on discrete valuation subrings of its function field”. Eight hits:
  general properness and valuative results, not this refined criterion.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id, generic/DVR
  properness, and `isProper_iff_generic_dvr_extensions`; no matching statement.
  The broader DVR searches found generic-stalk and normalization results only.
- The prescribed `grep -rn` for the item id in `lean/WeilConjectures` found no attachment.
  Existing function-field and canonical-stalk-spectrum constructions were read directly
  and reused. No duplicate definition was introduced.

Validation: `scompile.py` compiled the file in both sandbox and library module modes
against the published server library, cleanly (2.5 s and 3.7 s respectively).
The recorded `lean.statement` is extracted verbatim from the theorem signature.
No statement dispute or node correction is required.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
