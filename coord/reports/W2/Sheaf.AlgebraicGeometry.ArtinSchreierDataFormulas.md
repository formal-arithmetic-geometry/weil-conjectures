## What changed

Proved `AlgebraicGeometry.artinSchreier_formulas` in
`lean/Sheaf/AlgebraicGeometry/ArtinSchreierDataFormulas.lean`, without changing its signature.
The proof follows the existing three-step DAG plan directly: pull characteristic p into
section rings, construct the natural additive endomorphism by conjugation, extend the
constant-presheaf map using sheafification, and use Fermat plus sheafification uniqueness
for the zero composite. The constant ring map factors through k, so it works even when
an étale object's section ring is trivial. The binomial identity separately handles
subsingleton section rings before introducing a characteristic instance in the nontrivial case.
The docstring now records this factorization. No definitions or other statements changed.

## Proved and sorry left

Proved `AlgebraicGeometry.artinSchreier_formulas`
(node `lem-sc-as-sequence-formulas-helper`), the module's sole original sorry.
No sorry remains and none is added elsewhere. No intermediate theorem was split off.
The complete proof compiled locally without warnings through `lcompile.py`.

## No longer needed

None. Both original public imports are needed by the existing statement:
`WeilConjectures.AlgebraicGeometry.Sites.Kummer` supplies the constant sheaf and
`WeilConjectures.AlgebraicGeometry.Curve` supplies the curve hypothesis.
A trial proof import of `Mathlib.FieldTheory.Finite.Basic` was removed after checking
that the original imports already expose `ZMod.pow_card` and the characteristic lemmas.
Both original proof dependency nodes, `def-sc-constant-sheaves` and
`def-weil-pbc-sheafification`, are used. No DAG node or library module is pruned.
The unit record `sk-prop-h2` has no realized nodes; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. In Lean, a section ring of an empty étale object
cannot carry characteristic p for prime p. The proof explicitly separates trivial rings
and uses the map ZMod p → k → Gamma(U,O_U), avoiding that invalid instance while
implementing the existing plan. The helper's assumptions and conclusions remain unchanged.

## Second reading by W2

1. PASS: Reviewed the complete repository/sandbox diff and parsed both declaration tables.
   The sole existing declaration, `AlgebraicGeometry.artinSchreier_formulas`, has a
   byte-for-byte identical signature, also identical to its node's `lean.statement`.
   The only Lean changes are its proof and the explanatory constant-map docstring.
   No definition, attribute, public import, target, or other module changed.
2. PASS: Compiled the delivered module through `lcompile.py` without errors or warnings.
   A scratch copy with `#print axioms AlgebraicGeometry.artinSchreier_formulas` compiled
   and printed exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Searched every delivered Lean file for sorry and forbidden declarations: none.
   Read additivity, both naturality proofs, sheafification extension, section formulas,
   and the zero composite. The subsingleton branch covers the empty-object section ring;
   the nontrivial branch justifies characteristic p. Positive field characteristic
   excludes p = 0 and p = 1, and the argument also covers p = 2.
3. PASS: No statement was split off; no new declaration or new node exists. Every local
   intermediate assertion is proved. There is no renamed restatement or hollow definition.
4. PASS: The proof closes the original sorry directly using Mathlib characteristic,
   finite-field, and sheafification results. Read the upstream affine-space Artin--Schreier
   construction and searched the existing Sheaf Artin--Schreier modules: they do not
   replace the construction for an arbitrary G with the supplied natural equivalences.
   The general scheme section-data theorem remains sorry and fixes a particular G.
   Rechecked `sheafify_hom_ext` with Loogle and inspected the pinned Mathlib sources.
   Both existing public imports are required by the statement (constantZMod and IsCurve).
   Both old proof dependencies are still used, so `No longer needed: None` is complete.
   Checked `dag/units/sk-prop-h2.json`: its realized statement and step lists are empty;
   this delivery changes neither its route nor any unit record.
5. PASS after metadata clarification: Read the formulas-helper node and both dependency
   nodes. Its three proof steps and dependency union agree with the Lean proof. Updated
   step 2 to record the actual ZMod p → k → Gamma(U,O_U) factorization, including trivial
   rings, and updated `proof_origin` to identify the W2 implementation and its Mathlib
   ingredients. The original statement, statement dependencies, Lean signature record,
   and proof dependency list are unchanged. No new-node checks are applicable.

Second reading changed only the existing node's proof explanation and proof-origin
metadata, and added this review report. The Lean proof needed no repair.
