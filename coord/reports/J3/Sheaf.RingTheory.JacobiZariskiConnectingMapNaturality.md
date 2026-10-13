## What changed

Proved `Algebra.jacobiZariski_connectingMap_naturality` with its signature unchanged.
Constructed the comparison map with the universal property of tensor products and
KaehlerDifferential.map. Mathlib already supplies the quotient comparison identity.
Naturality follows from the coefficient derivative formula on monomials, additivity,
and kernel representatives of H1. Updated the docstring and the existing node's proof,
proof_deps, and proof_origin to record this shorter route. No definitions or statements changed.
Import change record: `coord/changes/jacobiZariski_connectingMap_naturality_imports.md`.
Both direct importers already import JacobiZariskiHomologySequence themselves; neither
requires adaptation.

## Proved and sorry left

Closed the one existing hole: `Algebra.jacobiZariski_connectingMap_naturality`
(node `lem-weil-pbc-jacobi-zariski-connecting-map-naturality`).
No sorry remains in the item's module; no holes or declarations were added.
This is a proof, not a decomposition. The single-file compiler passed without warnings.

## No longer needed

Removed the unused public import `Sheaf.RingTheory.JacobiZariskiHomologySequence`.
The proof does not need its theorem `Algebra.jacobiZariski_homology_sequence` or node
`lem-weil-pbc-jacobi-zariski-homology-sequence`: Mathlib's δ_eq_δAux supplies the formula
needed here. The sole retained import is `Mathlib.RingTheory.Extension.ExtendScalars`,
which publicly imports the Mathlib Jacobi-Zariski API needed by the statement and proof.

Pruned the planned proof dependency
`lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`
(Mathlib's polynomial differential basis). No polynomial differential basis, partial
derivative expansion, or choice of quotient lifts is needed in this proof.
The remaining planned nodes are used through their Mathlib declarations:
`def-weil-pbc-kahler-differentials`, `def-weil-pbc-mv-polynomial-ring`,
`def-weil-pbc-smooth-ring-map`, `lem-weil-pbc-nl-presentation-h1-functoriality`, and
`lem-weil-pbc-jacobi-zariski-surjection-h1`.
This is local pruning; other targets may still need the removed module or node.
The item realizes no unit statement or step, so the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old plan was longer than necessary. Its search already identified the Mathlib
quotient comparison theorem, but computing the naturality identity directly with
δAux avoids the planned evaluation-at-lifts and partial-derivative argument.
No false statement or tool failure was found.

## Second reading by J3

1. Compared the complete delivered module with the repository version and checked the
   theorem signature byte for byte: identical. No declaration, definition, hypothesis,
   conclusion, or visibility changed. The removed public import is documented in
   `coord/changes/jacobiZariski_connectingMap_naturality_imports.md`; both direct users
   independently import the removed module. Verdict: pass.
2. Compiled the module with lcompile.py without errors or warnings. Compiled a scratch
   copy with `#print axioms Algebra.jacobiZariski_connectingMap_naturality`: exactly
   propext, Classical.choice, Quot.sound. No sorry, forbidden declaration, or hollow
   definition occurs. The comparison map is explicitly constructed by liftBaseChange;
   the representative chosen by mk_surjective is from a proved Mathlib theorem.
   Verdict: a complete proof.
3. No statement or hole was split off and no new declaration was added. Read the
   monomial computation and representative reduction against Mathlib's definitions.
   They require neither a proper ideal nor injectivity of S -> B; the zero quotient,
   zero ideal, and identity S = B cause no exceptional step. Verdict: pass.
4. Searched the local RingTheory library and Mathlib's Kaehler API for connecting-map
   naturality and delta/map lemmas. Mathlib's delta_map changes presentations over a
   fixed middle ring and does not replace the middle-ring calculation here. The proof
   uses the existing quotient comparison theorem immediately and then the short
   monomial calculation. The sole retained public import supplies types and maps in
   the signature. Checked the old proof_deps: the polynomial differential basis is
   the only removed node and is reported above. Read sk-thm-p1.json realized: this item
   realizes no unit statement or step, so no unit route is bypassed. Verdict: pass.
5. Compared the node JSON: only proof, proof_deps, and proof_origin changed. The union
   of the proof steps' uses equals proof_deps. Checked retained nodes' Mathlib matches
   against the objects and functorial maps used in the Lean proof. The revised four
   steps describe construction, quotient comparison, coefficient naturality, and
   descent to H1 exactly as written. Verdict: pass.

Second reading changed only this review report and a spacing typo in its pruning
paragraph. No Lean or node repair was necessary. One original hole closed; zero added.
