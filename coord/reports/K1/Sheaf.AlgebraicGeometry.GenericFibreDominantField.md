## What changed

Proved `AlgebraicGeometry.exists_generic_fibre_dominant_field` in
`Sheaf.AlgebraicGeometry.GenericFibreDominantField`, preserving its statement and visibility.
Added the proved private helper `AlgebraicGeometry.reduced_generic_fibre` for the affine
localization step. The field is the actual Mathlib `Scheme.functionField` of the integral
fibre, and the map is `Scheme.fromSpecStalk` at its generic point. Finite generation follows
from Mathlib's finite-type and essentially-finite-type API. Added proof-only imports
`Mathlib.AlgebraicGeometry.FunctionField` and
`Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`.

Updated `lem-sbc-generic-fibre-dominant-field`'s proof and proof origin to describe the Lean
argument. The unit route is preserved: this implements the same generic function-field
construction of Tag 0559, without bypassing any unit statement or step.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_generic_fibre_dominant_field`
(node `lem-sbc-generic-fibre-dominant-field`). This is a complete proof, not a decomposition.
The private helper `AlgebraicGeometry.reduced_generic_fibre` is also proved.
No holes added; no `sorry` remains in the delivered module. Single-file compilation passes
with no warnings. The axiom check shows only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No original imports, planned dependency nodes, or dependency modules were pruned: the
original node has no proof dependencies. No Sheaf or WeilConjectures proof dependency is
needed. Trial explicit imports `Mathlib.AlgebraicGeometry.Stalk` and
`Mathlib.RingTheory.Localization.BaseChange` were removed after confirming their required
API is already available through the retained imports. No new module or node is needed.

## Where the brief, the DAG or earlier work was wrong

No statement or source error found. The generic-fibre reducedness step in the docstring is
valid without flatness; the proof retains the original flatness hypothesis unchanged.
Geometric irreducibility excludes the empty fibre; no geometric reducedness or separability
hypothesis was introduced. The construction and the fraction-ring and finite-generation
lemmas apply to zero-dimensional fibres as well.

## Second reading by K1

1. **Interfaces: PASS.** Compared the delivered Lean module and node with their repository
   versions using `diff -u`. The existing theorem signature, visibility, docstring, universe,
   hypotheses and conclusion are byte-for-byte unchanged. The only Lean additions are two
   plain proof-only imports, a proved private helper and the replacement proof. No definition,
   public import or target statement changed; no change record or adaptation is required.
2. **Proof and axioms: PASS.** Independently compiled the delivered module using `lcompile.py`
   with no errors or warnings. The scratch-copy axiom check of
   `AlgebraicGeometry.exists_generic_fibre_dominant_field` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No forbidden declaration or annotation, no `sorry`,
   and no hollow definition occurs. Read the localization pushout, fraction-field algebra
   compatibility, finite generation, dominance and final spectrum-map equality in detail.
   The field is Mathlib's actual generic stalk, not a witness of an unproved existence result.
3. **Split statements and edge cases: PASS.** No statements were split off and no holes were
   added. The proved private helper needs no flatness: base change to the generic residue
   field localizes the reduced source ring, even if that localization is the zero ring.
   The main theorem excludes an empty fibre through geometric irreducibility and handles
   zero-dimensional fibres and inseparable extensions without additional assumptions.
4. **Route and pruning: PASS.** Searched independently with LeanFinder for generic-base
   localization reducedness and with `rg` for reduced fibres and generic dominance in Mathlib,
   Sheaf and WeilConjectures. No existing lemma replaces the affine reducedness argument.
   Found the proved upstream instance `Scheme.isDominant_fromSpecFunctionField`; it uses
   the same short density argument. Retaining that argument here avoids an additional
   upstream import. The two new imports supply function-field and `IntermediateField.fg_top`
   API; every retained public import supplies a notion in the unchanged statement.
   The old node has empty `proof_deps`, so no dependency node is omitted from
   `## No longer needed`. Read `dag/units/sk-prop-normal-form.json`: its `realized` entries
   are empty, and this below-unit generic-field construction preserves the planned route.
5. **DAG agreement: PASS.** The sole delivered node changes only `proof` and `proof_origin`.
   Its five proof steps describe the actual Mathlib localization, integral fibre, explicit
   function field, finite generation and dominant spectrum map argument. Empty `proof_deps`
   agrees with the absence of Sheaf or WeilConjectures proof dependencies. No new node exists.

Second reading changed only this report and refreshed the scratch axiom checks. No repair
of the Lean proof or node was needed. Holes closed: one, namely
`AlgebraicGeometry.exists_generic_fibre_dominant_field`; holes added: zero.
