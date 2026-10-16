## What changed

Constructed the coefficient pullback family explicitly. In
`Sheaf.Paper.FiniteDiscreteCoefficientRestriction`, the normalized underlying-sheaf
restriction isomorphism is built from the existing encoding forget isomorphisms.
A named scalar-linearity obligation lifts this specified map with `Mod.isoMk`; its
naturality follows from the faithful forgetful functor.

`Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso` conjugates that restriction
isomorphism through the ordinary adjunctions and encoding equivalences. It composes
with the existing etale/pro-etale pullback comparison, applies exact derivation,
restricts the source to D+, and identifies exact internal inverse image with its total
left derived functor. These constructions have complete Lean bodies, with no choice
of an arbitrary isomorphism from an existence theorem.

The assigned theorem constructs the coherence record from this specified family and
its separate square-coherence obligation. Its statement is unchanged. The new proof
import is private.

Also proved the normalized restriction-composition identity and a generic theorem that
exact derivation preserves pasting of comparison squares. These are completed steps
of the remaining square-coherence argument, with separate modules and nodes. The
remaining node cites them; its eventual proof can import them when it uses them.

Cached the unchanged family type and square predicate in
`Sheaf.Paper.CoefficientDerivedFunctorAPI`. The two consumer records in the unclaimed
`Sheaf.Paper.FiniteDiscreteDerivedCoefficientData` reuse the same cached types. This
repairs kernel normalization when assembling the concrete record. Only four field
types change in that consumer; its proofs and mathematical equations do not change.
See `coord/changes/A4-coefficient-coherence-field-cache.md`. The unchanged consumer
compiled against the published API, timed out against the changed API with expanded
fields, and compiled after the cache adaptation. Its claimed C3 direct importer and
the direct-image-origin API importer compiled unchanged against the adapted files.

## Proved and sorry left

Closed the assigned hole in
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_coherentPullbacks`.
The record assembly and ordinary/derived pullback constructions are complete Lean
proofs from the named lower obligations. This is a decomposition, not an unconditional
proof of the original theorem: one upper hole closed and two lower holes added,
net minus one hole closed. The assigned module has zero local holes.

The delivery adds exactly these two holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientRestrictionForgetIso_linear`
  (`lem-weil-pbc-finite-discrete-restriction-linearity`). What remains is the scalar-action
  calculation for the inverse sectionwise encoding and compatibility of the fixed
  scheme-ring identifications with `condensedPushforwardHom`.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientPullbackIso_square`
  (`lem-weil-pbc-finite-discrete-coefficient-square-coherence`). What remains is the
  transport of the proved restriction-composition equation
  through the specific conjugation, and the application of the proved derived-pasting
  theorem together with D+ inclusion and the exact-to-left-derived comparisons. The claim is only about the
  constructed canonical family, never arbitrary choices of pullback isomorphisms.

The supporting theorems
`finiteDiscreteCoefficientRestrictionIso_comp` and
`CategoryTheory.Functor.mapDerivedCategorySquareIso_paste` are proved without new holes.

No holes were added inside definitions. Empty schemes, identity morphisms and the
zero coefficient ring impose no extra hypotheses on either obligation. The original
finite/discrete hypotheses remain on the assigned theorem.

## No longer needed

None. Both original imports remain necessary. The new construction follows their
intended restriction/conjugation/derivation route; no blueprint unit or required
unit step is bypassed. No existing node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The two original proof-dependency nodes supply definitions, not a theorem of linear
restriction or a theorem of square coherence for the common encoding. Their route
can be implemented, but those specific compatibility equations must still be proved.
The additive comparison, its naturality, conjugation and exact derivation have now
been implemented rather than replacing the entire existence statement by another
name.

The expanded record fields also caused excessive kernel normalization at the concrete
coefficient ring, even with temporary placeholders in both fields. Naming the same
field types once and reusing them in the constructor, family, square predicate and
consumer records fixes this without changing any equation or raising any limit.

## New nodes

`lem-weil-pbc-finite-discrete-restriction-linearity` states scalar linearity of the
explicit normalized additive comparison. Its module also contains the explicit
restriction-isomorphism construction and the proved naturality argument.

`def-weil-pbc-canonical-finite-discrete-pullback` records the explicitly constructed
restriction, ordinary pullback and derived pullback family. It depends on the scalar
linearity obligation and uses existing categorical and exact-derived constructions.

`lem-weil-pbc-finite-discrete-coefficient-square-coherence` states only the square
condition for that specified family. Its source and full natural-language argument
are in its docstring and node. It is strictly the coherence part of the original
record, with the pullback data already fixed and constructed.

`lem-weil-pbc-finite-discrete-restriction-composition` records the proved composition
identity for the specified restriction comparison.

`lem-weil-pbc-derived-square-pasting` records the proved generic derived-pasting
identity, using the existing exact-derived composition and whiskering laws.

Change record: `coord/changes/A4-coefficient-coherence-field-cache.md`.

## Second reading by A4

1. **Statements and signatures — PASS.** I compared the delivered item module with
the repository version. The existing theorem signature is byte-for-byte unchanged;
the proof only supplies the explicitly constructed pullback and square fields. The
adapted consumer and cached API changes are recorded in the change record, and no
target statement was changed.

2. **Proof and axioms — PASS.** I compiled every delivered Lean module with
`lcompile.py --all`. The assigned theorem has no `sorry`; the only remaining
`sorry`s are the two named split-off obligations, each public, documented, and
matched by a DAG node. No definition contains `sorry`, and no forbidden declaration
form was introduced. Scratch-copy `#print axioms` checks show the three permitted
axioms for the additive restriction comparison and generic derived-pasting theorem;
the constructed linear comparisons and assigned theorem additionally depend on
`sorryAx` through their recorded lower obligations.

3. **Split-off statements — PASS.** I checked both new obligations against their
docstrings and nodes. Restriction linearity is the exact scalar-action compatibility
needed by `Mod.isoMk`; square coherence is stated only for the constructed canonical
family. The supporting composition and derived-pasting lemmas are strictly smaller
than the assigned theorem and are proved. Searches of the existing Lean sources
found no duplicate declarations.
I also made fresh LeanFinder searches for restriction linearity and preservation of
composition squares under exact derivation, and a Mathlib grep for conjugation
composition and derived-square pasting. They found generic scalar-restriction,
adjunction and localization infrastructure, not either split-off coefficient result.
For identities, the normalized forget comparisons cancel; on the empty scheme or
over the zero ring, the action and square equations impose no nonzero or inhabited
hypothesis. The two holes are linearity and coherence of fixed data, rather than a
renaming of the original existence theorem. I found no short closure of either.

4. **Pruning and route — PASS.** The canonical family follows the unit route:
explicit restriction, conjugation through adjunctions, etale/pro-etale comparison,
derivation, and D+ restriction. All imports used by the proofs remain necessary;
none of the old proof dependencies or unit steps is bypassed, so no module or node
is withdrawn.
I checked `sk-thm-properbasechange.realized`: its statement nodes and the projective
line, reduction, and torsion-assembly steps remain unchanged. The old encoding and
derived-API dependencies remain used transitively by the construction. I tested
making the `LowerStarAcyclic` import private; Lean rejects the exposed definition's
reference to `comparisonUpperStarCompUpperStarIso`, so its public import is required
by the public definition and was restored.

5. **DAG and report consistency — PASS.** The item node proof and `proof_deps` match
the record assembly, and each split-off node names the declaration, module, source,
proof origin, and dependencies used by the delivered code. The field-cache change
record lists its affected consumers and the forced adaptations compile.
The original expanded `FiniteDiscreteDerivedCoefficientData` timed out at 60 seconds
against the changed API; the adapted consumer compiled in 21.0 seconds. Its four
field-type edits are exactly abbreviations by the two new definitions, as confirmed
by comparing each defining expression with the old fields. Both adapted modules
were unclaimed according to the change record; this is a declared interface cache,
not an undeclared signature change in another group's module.

I added this second-reading record and completed the API node's `lean.declarations`
list with `CoefficientPullbackFamily` and `CoefficientPullbackSquare`. The import
experiment was reverted; no delivered Lean proof or statement required repair.
