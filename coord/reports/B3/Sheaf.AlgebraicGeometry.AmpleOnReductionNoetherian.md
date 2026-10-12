## What changed

Proved `AlgebraicGeometry.isAmple_iff_of_isClosedImmersion_of_isHomeomorph` in
`Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian`, with its signature unchanged.
The forward implication applies the existing affine tensor-pullback theorem.
The converse now contains an actual induction on a nilpotency exponent.

Three fully proved private helpers implement the argument:
- `exists_ker_pow_eq_bot`: a finite affine cover and the Mathlib finitely generated
  ideal radical-power result prove kernel nilpotence directly.
- `ker_square_eq_bot_of_comp`: sectionwise surjectivity along a closed immersion
  identifies the first factor's kernel as an ideal image and proves it square-zero.
- `isAmple_of_ker_pow_eq_bot`: induction through the subscheme of the squared ideal,
  transporting ampleness using tensor-pullback composition and module isomorphisms.

Added proof-only imports `Mathlib.RingTheory.Noetherian.Nilpotent` and
`Sheaf.AlgebraicGeometry.AmpleIso`. All public imports are preserved. Updated the
existing DAG node's proof, proof dependencies and proof origin to this argument.
The unit's statement and route are preserved: the item's node does not realize a
unit statement or step, and the existing square-zero lifting result is still used.

Local compilation passes without warnings. The private nilpotence and square-zero
kernel helpers use only standard axioms. The theorem is a stage-3 reduction to the
existing affine pullback, module-isomorphism and square-zero lifting declarations.

## Proved and sorry left

Removed the only local sorry, in
`AlgebraicGeometry.isAmple_iff_of_isClosedImmersion_of_isHomeomorph`
(node `lem-sc-ample-on-reduction-noetherian`). No sorry remains in the item's module,
and no new module, theorem with sorry, definition, or axiom is introduced.

The proof uses these existing declarations whose proofs are still sorry in the
read-only library snapshot:
- `Scheme.Modules.isAmple_tensorPullback_of_isAffineHom`
  (`lem-weil-pbc-pullback-ample-invertible`).
- `Scheme.Modules.isAmple_iff_of_iso` (`lem-sc-ample-iso`).
- `Scheme.Modules.isAmple_of_isAmple_tensorPullback_of_square_zero`
  (`lem-sc-ample-square-zero-thickening`).
These existing nodes are the intended next proof items, not new sorries in this delivery.

## No longer needed

Removed seven proof-only imports:
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`
- `Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills`
- `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`

Pruned proof dependencies because direct Mathlib ideal calculations replace the
coherent-module/support route:
`pqf-def-coherent`, `pqf-lem-coherent-ft-locnoeth`,
`def-weil-pbc-closed-subset-proper-over-base`,
`lem-weil-pbc-coherent-support-power-ideal-kills`,
`def-weil-pbc-coherent-formal-module`,
`lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`, and `def-weil-affine-spectrum`.

Also removed `lem-weil-pbc-closed-immersions-equal-ideal-isomorphic`: the induction
ends at a square-zero case, so no final identification with the identity immersion
is required. The identity clause of `lem-pc-module-pullback-identity-composition`
is unused, but its composition clause is used, so the node remains.

Removed redundant proof-dependency entries `lem-weil-pbc-invertible-pullback-invertible`
and `def-pur-sheaf-tensor-product`; actual tensor-pullback invertibility is supplied
by `lem-weil-pbc-invertible-pullback-tensor`. Definition nodes
`def-pc-module-pullback` and `def-weil-pbc-ample-invertible-module` remain statement
dependencies and their public imports are retained, although they are no longer
listed redundantly as proof dependencies.

These are dependencies pruned from this item; no claim is made that other targets
or modules do not still need them. The seven imports' modules can also remain
reachable transitively through the retained square-zero theorem.

## Where the brief, the DAG or earlier work was wrong

No statement was wrong or disputed. The DAG's coherent-module argument for
nilpotence was unnecessarily large: Mathlib's ideal-sheaf support/radical API and
finite affine-cover extensionality already allow a direct proof. Its consecutive
power chain is replaced below the unit level by induction through the squared
ideal, with the same square-zero lifting input.

The clone contains only the literature index, not the cited TeX. Read the exact
source online at https://stacks.math.columbia.edu/tag/09MS and
https://stacks.math.columbia.edu/tag/01Y9. The proof follows their first-paragraph
nilpotence and square-zero reduction, with all glue now checked in Lean.


## Second reading by B3

1. **Interface: PASS.** Compared the delivered Lean module and node with the
   repository using `diff -u`, then checked the complete existing theorem signature
   byte for byte through its proof delimiter. It is identical, including both
   Noetherian and compactness instances, the homeomorphism hypothesis, and the
   explicit pullback invertibility instance. No existing definition changes and no
   other module is delivered. The six public imports are unchanged; the two added
   imports are proof-only. No change record is required.

2. **Proof and axioms: PASS as a reduction to existing open declarations.**
   Independently compiled the delivered module with `lcompile.py`: exit 0, no
   warnings. Compiled the full scratch copy with `#print axioms` for all four
   declarations: the nilpotence and composite-kernel helpers use only `propext`,
   `Classical.choice`, and `Quot.sound`; the induction helper and public theorem
   additionally use `sorryAx` through existing imported open statements. The
   delivered text has no `sorry`, forbidden declaration, or hollow definition.
   This closes one local hole and adds zero holes; it does not certify the public
   theorem as axiom-clean before the imported open statements are proved.

3. **Split statements: PASS (none added).** Read all three private helpers and
   their proofs; all are proved, not split-off holes. Checked the empty scheme /
   empty finite affine cover (the supremum exponent is zero and extensionality is
   vacuous), zero kernel, exponent zero, square-zero base case, and successor
   bound `n + 3 ≤ 2 * (n + 2)`. The kernel helper uses surjectivity on affine
   sections of the closed immersion, not an unjustified global section
   surjectivity. The intermediate subscheme is locally Noetherian and compact by
   the finite-type and quasi-compact permanence instances. No duplicate new open
   theorem or restatement of the item exists in this delivery.

4. **Route and pruning: PASS.** Read Stacks [09MS](https://stacks.math.columbia.edu/tag/09MS)
   and [01Y9](https://stacks.math.columbia.edu/tag/01Y9). The source's nilpotence and
   reduction to square-zero lifting are preserved; squaring the ideal gives an
   actual decreasing induction bound. Ran a fresh LeanFinder search for
   ampleness preserved by a nilpotent closed immersion; its eight hits concern
   formally unramified morphisms, reducedness, and affine closed immersions, not
   this theorem. Searched the library with `rg` for nilpotence, kernel powers, and
   closed-immersion ampleness, and read upstream `Modules/AmpleReduced.lean`:
   it proves descent of an existential ample family in prime characteristic,
   not ampleness of the given line bundle in this characteristic-free statement.
   No shorter available result was found. The remaining proof imports each have
   a direct use. Compared old and new `proof_deps`: all twelve removed entries
   are accounted for in `## No longer needed`. Read
   `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`, with no realized steps. The present node realizes
   neither, and no unit route is bypassed.

5. **DAG: PASS.** Only `proof`, `proof_deps`, and `proof_origin` change. The six
   new proof steps match the actual forward pullback, finite-affine nilpotence,
   factorization through the squared ideal, composite-kernel calculation,
   pullback-composition/isomorphism transport, and induction. Read each retained
   dependency's Lean / Mathlib record and checked the declarations used against
   it. The set of `proof_deps` equals exactly the union of the proof steps' `uses`.
   No new node is needed, since no new open statement is introduced.

**Second-reader changes:** Added this independent review and explicit axiom / hole
accounting. No Lean proof or node repair was necessary.
