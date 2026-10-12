## What changed

Proved both declarations in
`lean/Sheaf/AlgebraicGeometry/TorsionSheafCharacterizations.lean`, preserving their
statements, universes, public imports, and existing docstrings.

The characterization uses filtered stalk representatives, additivity, the source library's
closed local-torsion/stalk theorem, and a direct monic/epic proof of the torsion-kernel
colimit comparison. The Q/Z example uses the proved upstream constant-stalk isomorphism with an explicit bridge,
closed sheaf gluing tools, coproduct geometry, and two proved private arithmetic helpers.
Added only proof imports. No new modules or declarations with postponed proofs.
Updated the existing node's proof, proof_deps, and proof_origin to this route.
A scoped unused-variable linter option on the second theorem preserves the inherited
nondependent binder `n` in its statement while allowing a warning-free compile.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.isTorsionAbelianSheaf_characterizations` and
`AlgebraicGeometry.Scheme.constant_ratModIntSheaf_sections_not_torsion`:
2 of 2 original sorries removed; no sorry remains in the delivery.
Both private arithmetic helpers have complete proofs.

After the second reading, both theorems and both private helpers have only
`propext`, `Classical.choice`, and `Quot.sound` as axioms. There is no `sorryAx`
dependency: the postponed geometric constant-stalk comparison is no longer imported.

Local single-file compilation passed with no errors or warnings. The proof handles empty T
for the torsion claim and uses Nonempty T only to make the constant unit injective and obtain
the infinite-order section. Positive integer indexing prevents zero annihilators; choosing
n=k+1 guarantees a positive dyadic index.

## No longer needed

No original public import was removed: they support the inherited statements and interface.
The second reading removed the proof import
`Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk` and pruned
`lem-weil-pbc-constant-sheaf-geometric-stalk`. The proof now uses the proved upstream
constant-stalk isomorphism and explicitly identifies its inverse by naturality and cancellation.
Its constituent existing Mathlib leaves
`lem-weil-pbc-sheafification-geometric-stalk` and
`lem-weil-pbc-colimit-constant-connected-diagram` now appear in proof_deps.
The latter also records the connected constant-diagram colimit used in the monicity proof.
Removed redundant proof imports
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper`,
`Mathlib.Algebra.Ring.Rat`, `Mathlib.Tactic.Positivity`, and `Mathlib.Data.Rat.Cast.Order`.
The upstream Point.ConstantSheaf import tried during the second reading is also redundant:
its declarations are already publicly available through the retained proof imports.
The final additional imports are just EtaleTorsion and Hilbert90Etale;
removing either fails compilation on the actual declarations used.
Removed trial proof imports `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`,
`Mathlib.Tactic`, `Mathlib.Algebra.Category.Grp.AB`, and `Mathlib.Tactic.NormNum`.
The filtered-union module cannot be imported because it reaches this item; the necessary
argument is proved directly. The other imports were replaced by narrower existing imports.
No import of `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` is needed.

The immediate proof dependencies no longer include
`prop-weil-pbc-geometric-stalks-exact` (stalk additivity suffices),
`def-weil-pbc-pointed-etale-neighbourhoods`,
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`,
`lem-weil-pbc-etale-cover-geometric-point-lift`, or
`lem-weil-pbc-etale-composition-cancellation`.
The local/stalk equivalence is supplied by the already closed source theorem, so no new
neighbourhood comparison or lifting modules are imported or need to be proved here.
This is pruning of this item's route; these nodes may still be needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

The existing TorsionFilteredUnion proof is usable mathematically but its module imports
HighDegreeVanishing, which reaches this item. Importing either module would close a cycle.
The final proof avoids both imports and supplies the colimit argument directly.

The original plan preserves torsion kernels under stalks and identifies their union.
That kernel-preservation step is unnecessary: representing a stalk element using the mapped
colimit cocone and mapping kernel.condition already gives its positive annihilator.
The original local/stalk steps are now a closed theorem in the source library.

No false statement, changed target, new axiom, or hollow definition was found or introduced.

## Second reading by W2

1. Compared the complete Lean diff against the repository and checked both existing
   declaration signatures with the delivery parser: byte-for-byte equal. Public imports,
   universes, definitions, and inherited docstrings are unchanged. No change record is needed.
   The only new declarations are the two proved private arithmetic helpers.
2. Read both proofs and helpers in full. Single-file compilation is warning-free.
   Scratch `#print axioms` checks for all four declarations return exactly
   propext, Classical.choice, and Quot.sound, with no sorryAx. No sorry, axiom,
   unsafe, opaque, implemented_by, extern, or hollow definition occurs in the module.
   The kernel diagram uses positive divisibility indices and genuine local lifts;
   gluing checks both equal indices by monicity and unequal indices by emptiness.
3. There are zero split-off statements and zero new nodes. Checked arithmetic edge cases:
   q=0 is killed by its positive denominator, k=1 uses n=2, and k=0 is correctly excluded
   only from the infinite-order test. No point of T is chosen in the torsion assertion;
   the Nonempty hypothesis is used only for injectivity in the example.
   Searches by upstream constant-presheaf fibre/naturality names and Lean Finder's
   rational-quotient description found a proved upstream constant-stalk tool and
   AddCircle finite-order lemmas. The existing elementary denominator proof is already
   short and avoids an additional topology import.
4. Checked the top-down reduction: filtered representatives and additive kernel equations,
   the proved EtaleTorsion local/stalk equivalence, and the mono/local-epi comparison.
   Replaced the unnecessary postponed constant-stalk comparison with the proved upstream
   Point.sheafFiberConstantSheafIso and the explicit naturality/cancellation bridge.
   Tested omission of every additional import, then compiled with the combined minimal
   additional import set. All six removed old proof dependencies are named above.
   Read dag/units/sk-def-pbc.json: the item still realizes its torsion-equivalence clause;
   the unit has no proof steps, and its PBC definition and chapter route are unchanged.
5. Compared the node diff: only proof, proof_deps, and proof_origin change.
   Checked each retained/new dependency against its declaration or Mathlib match.
   The proof_deps are exactly the union of the proof-step uses. Updated the constant-stalk
   steps to describe the upstream isomorphism and bridge, with its two existing Mathlib
   constituent nodes, and recorded that route in proof_origin. No unit/node statement changed.

Changed during the second reading: removed the last sorryAx dependency using the proved
upstream constant-stalk isomorphism, removed redundant proof imports, and corrected the
DAG and report to the final proof. Both original theorems are fully proved; no split remains.
