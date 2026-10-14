## What changed

The delivered module adds an inline explanation at the inverse-mate construction and
an elaborationally redundant `show _ from` around its final term. The repository
already constructs `AlgebraicGeometry.dualityEquationBaseChangeMap` directly as
`(mateEquiv adjf adjf' (inv β)).app K`; this delivery preserves that construction.
The existing signature, docstrings, imports and definition data are unchanged.
This is verification/documentation of the queued repair, not a new construction repair.

## Proved and sorry left

Holes closed: none (the repository module has no theorem holes).
Holes added: none. Split-off declarations: none.
`AlgebraicGeometry.dualityEquationBaseChangeMap` contains no `sorry`, and its local
naturality proof compiles. Its axiom check includes `sorryAx` from existing upstream
open results, alongside `propext`, `Classical.choice` and `Quot.sound`; it is therefore
not an axiom-complete target proof. Net holes closed minus holes added: zero.

## No longer needed

None. All three public imports occur in the signature; the proof-only Mates import
provides the construction. No old proof dependency, node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The repair queue describes the older auxiliary-adjunction construction. The current
repository version already eliminates those auxiliary choices using the inverse
mate. The first worker's report overstated the effect of adding `show _ from`:
it neither repairs hollow data nor changes the morphism. The second reader corrected
that account. Preflight requires a change record even for this definitionally equal
body edit, so `coord/changes/dualityEquationBaseChangeMap-repair.md` now records exact
old/new declarations and all users without claiming a semantic construction repair.

## Second reading by V4

1. Compared the entire delivered module with the repository using `diff -u` and
   checked the declaration prefix through its result type byte for byte. PASS:
   only two inline comment lines and `show _ from` differ; no public signature,
   definition data, import, option or docstring changed.
2. Compiled the delivered file locally with `lcompile.py`. PASS: no errors or
   warnings, no local sorry or prohibited declarations, and no hollow definition.
   An independent scratch copy checks the definition's axioms and recompiles the
   generic second-mate formula. The definition uses only the three standard axioms
   and inherited `sorryAx`; the generic identity uses only the standard axioms.
   Inverse data is uniquely determined by `IsIso β`, not an arbitrary witness.
3. PASS: there are no new or split-off statements to search for or test.
   The existing mate construction has the correct direction: inverse β has type
   `LgX ⋙ Rf' ⟶ Rf ⋙ Lg`, and its mate under the supplied adjunctions has type
   `a ⋙ LgX ⟶ Lg ⋙ a'`. Identity and zero-category cases introduce no extra
   assumptions or choices. Reviewed the existing `secondMate_formula` in
   QCohInverseBaseChangeMate and Mathlib's iterated mate identity.
4. PASS: the construction already uses Mathlib's direct mate equivalence. The
   three public imports are needed by the signature; Mates is proof-only.
   No former proof dependencies become unused. The unit record
   `dag/units/sk-thm-picard-duality.json` has empty realized statement/step lists,
   and no unit route or realization is altered by this delivery.
5. PASS: read `def-sc-duality-equation-base-change-map.json` in full. Its four
   proof steps, proof_deps and proof_origin describe exactly the existing lifted
   beta, naturality proof, reflection of invertibility and inverse mate.
   No node edits or new nodes are required.

Second-reading changes: corrected the inaccurate progress/repair claims in this
report and replaced the malformed change record with verbatim old/new declarations
and a complete user table, as required by preflight. Kept the working Lean code.
