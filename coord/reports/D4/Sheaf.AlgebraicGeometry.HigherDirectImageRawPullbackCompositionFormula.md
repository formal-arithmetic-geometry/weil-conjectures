## What changed

Reduced `AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_function_comp`
without changing its signature or the raw pullback construction. The complete item
proof applies function extensionality, names the three single-complex coefficients
and their actual coefficient morphisms, applies arbitrary-coefficient triangle
composition, and rewrites its composed coefficient using a fully proved coefficient
identity. Unfolding the raw pullback definition completes the original equality.

Added two modules. `HigherDirectImageRestrictedCoefficientComposition` proves the
unshifted derived coefficient identity from single-functor naturality,
underived pullback associativity in `BaseChange.Pasting`, and the existing proved
`Etale.upperStarPlusComp_single`. `HigherDirectImageRawTrianglePullbackComposition`
states the remaining source/shift composition identity for arbitrary bounded-below
derived coefficient objects and arbitrary coefficient morphisms. It does not
identify the restricted single-complex coefficient maps; that independent part is
proved and combined with it by a real Lean rewrite in the item.

Updated the item node's proof and proof dependencies; added nodes for the two new
modules. No existing statement, definition, visibility or target signature changed.
No forced adaptations are needed.

Searches: Lean Finder found generic shift and Ext lemmas; Loogle found no result
for `upperStarPlusComp`; LeanSearch was unavailable (Internal Server Error). Local
`rg` found proved generic raw composition calculations and shift helpers in
`AbelianRawPullbackComposition` and `AbelianDerivedDirectImageTransitionShift`.
The coefficient proof directly uses the existing underived associativity and
single-comparison lemmas rather than adding holes for them.

## Proved and sorry left

Closed the item's one hole by a decomposition:
`AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_function_comp`
(node `lem-sbc-higher-image-raw-pullback-composition-formula`).

Fully proved `AlgebraicGeometry.Etale.higherDirectImageRestrictedCoefficient_comp`
(node `lem-sbc-restricted-single-coefficient-composition`). Its proof has no holes.

Added exactly one hole:
`AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_comp`
(node `lem-sbc-raw-triangle-pullback-composition`). Its proof is exactly `by sorry`.
No sorry remains inside the item's proof or any definition. One hole closed, one
added: this is a decomposition, not a net reduction in holes.

The coefficient lemma uses no base S, test object, cohomology class or shift.
The triangle lemma uses arbitrary derived coefficients and supplied coefficient
morphisms, with no single-complex presentation or invertibility assumption. These
are independent parts of the original five-factor calculation. Identity arrows,
zero objects/maps/classes and negative integer degrees satisfy the same naturality
and coherence identities. No affineness, limit, qcqs or positivity hypothesis was
introduced.

Validation: compile the full set through lcompile.py and run the required
`deliver3.py D4 Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula
--no-push` dry run, which checks the declaration probe and preflight. Nothing is pushed.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.EtalePullbackSingleComp` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. The first remains imported
by the proved coefficient module; the second remains visible through the statement
imports of the new modules. Neither is globally pruned.

The original direct proof dependencies `lem-weil-pbc-inverse-image-composition`,
`lem-sbc-pullback-single-comp`, and `lem-weil-pbc-exact-functor-derived-factorization`
are now used by the two component nodes instead of directly at the item. Their
content remains needed. No node or module is claimed globally unnecessary. The
unit's own statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement dispute. The original plan accurately lists
the coherence ingredients but does not separate source/shift composition from the
restricted coefficient identity. The latter is now fully proved.

A shorter route was investigated using the already proved private `rawGeneralComp`
from `AbelianRawPullbackComposition`, whose coefficient category and integer degree
are more general than its public abelian natural-number theorem. Direct reuse
encountered dependent structure-map transport and raw-presheaf-to-derived-morphism
conversion issues, with several checks exceeding the 60-second limit. The same
source calculation and shift compatibility helpers are recorded as existing tools
in the remaining triangle node's proof. They were not duplicated with new holes.
Scratch attempts are outside the delivered lean directory. No definition was
changed to make the statement easier or to bypass the compile limit.

## New nodes

`lem-sbc-raw-triangle-pullback-composition` records the arbitrary-derived-coefficient
triangle composition identity in
`lean/Sheaf/AlgebraicGeometry/HigherDirectImageRawTrianglePullbackComposition.lean`.
Its source and complete proof in words explain source comparison, naturality at
the class, shift compatibility and the final supplied coefficient composition.
This remains the one new theorem with sorry.

`lem-sbc-restricted-single-coefficient-composition` records the fully proved unshifted
coefficient identity in
`lean/Sheaf/AlgebraicGeometry/HigherDirectImageRestrictedCoefficientComposition.lean`.
It contains no base S, class, test object or degree. The item rewrites this equality
into the arbitrary-coefficient triangle statement before applying extensionality.

No change record is required: all existing signatures and definitions are unchanged.

## Second reading by D4

1. **Statements and interfaces.** Compared the delivered item with the repository version using `diff`. The existing target declaration has the same signature byte for byte; the two added theorem statements are coherent specializations and do not alter existing definitions. Verdict: pass.

2. **Proof and axioms.** Compiled the sandbox modules with `lcompile.py` (the prior dry-run log records a successful compile and preflight). The item proof contains no `sorry`; the only remaining `sorry` is the explicitly named `higherDirectImageRawTrianglePullback_comp` split-off theorem. No forbidden `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition was found. Verdict: pass, with the documented split hole.

3. **New statements.** Checked both new nodes against their Lean declarations and the edge cases described in their docstrings. `higherDirectImageRestrictedCoefficient_comp` is fully proved and strictly lower-level than the target. `higherDirectImageRawTrianglePullback_comp` is the independent arbitrary-coefficient source/shift composition required by the target, with no extra hypotheses or weakened conclusion; its `sorry` is exactly in the named theorem. Local searches found no duplicate declaration. Verdict: pass.

4. **Pruning and route.** The item imports only the two component modules needed by its proof in addition to `HigherDirectImageRawOverNaturality`; the removed direct proof imports are recorded under “No longer needed”. The item and new nodes retain unit `sk-lem-failure-field`, and the node proof/proof_deps match the written Lean route. Verdict: pass.

5. **Delivery checks.** The required `deliver3.py ... --no-push` dry run completed successfully (commit `82a8776813`, compile and preflight OK). Verdict: pass.

I changed only this report by adding the second-reading record; no Lean statements or proofs were changed.
