## What changed

Proved `AlgebraicGeometry.locallyOfFiniteType_and_openDiagonal_of_fpqcCover` in
`Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`, preserving its name, universes,
binders, hypotheses, conclusion, public imports, and public interface.

The proof generates the fpqc covering sieve and applies the existing closed source-library
`Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` twice, to local finite type and formal
unramifiedness. Mathlib supplies the locality, base-change stability, and single-morphism
descent instances. Each given open diagonal supplies formal unramifiedness; after descent,
`FormallyUnramified.isOpenImmersion_diagonal` recovers the required open diagonal.

Replaced the two private Sheaf proof imports with private imports of
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. Updated the proof docstring and the
item node's proof, proof_deps, and proof_origin. Added two metadata nodes attaching already
closed declarations; no additional Lean modules or statements were created.

Validation: local launcher compilation passes without warnings. A temporary `#print axioms`
check reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the theorem.
The source-library import passes `tools/import_direction.py may`.

The covering-family theorem admits arbitrary index universes and has no nonemptiness
assumption. The empty covering of the empty scheme is included, as are identity covers and
families whose individual maps are not surjective. The proof does not replace a covering
family by a single surjective member. `dag/units/sk-prop-h2.json` has no realization entry
requiring this auxiliary node's six-step route; the unit statement and its route are intact.

## Proved and sorry left

Proved: `AlgebraicGeometry.locallyOfFiniteType_and_openDiagonal_of_fpqcCover`
(node `lem-galois-fpqc-descend-unramified`). One of one original sorries closed.

No sorry remains in the item's module, and the delivery introduces no sorry anywhere.
No intermediate obligations were split off. All declarations used by the new route are
already proved in Mathlib or the source library; the temporary axiom check confirms that
no sorry is reachable from the theorem.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent`, node
  `lem-galois-fpqc-descend-open-immersion`.
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`, node
  `lem-weil-pbc-fpqc-descend-locally-finite-type`.

Removed from the item node's proof_deps because the explicit diagonal-pullback construction
is unnecessary:

- `lemma-nagata-diagonal-base-change` (module
  `Mathlib.CategoryTheory.Limits.Shapes.Diagonal`).
- `lem-weil-pbc-cartesian-square-pasting` (module
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`).
- `lem-galois-fpqc-covering-base-change` (module
  `Mathlib.CategoryTheory.Sites.Precoverage`).
- `lem-galois-fpqc-descend-open-immersion` and its module listed above.
- `lem-weil-pbc-fpqc-descend-locally-finite-type` and its module listed above.
- `def-weil-open-immersion` and `def-pc-scheme` as standalone proof dependency entries:
  the corresponding notions remain in the unchanged statement dependencies and in the
  unramified-characterization nodes, so their definitions remain necessary.

The two removed Sheaf modules had also privately imported
`Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion`
(node `lem-weil-pbc-fpqc-local-on-base-criterion`). This item's proof no longer reaches that
sorry-bearing module through either former import. The new generic metadata node attaches
the existing source-library family theorem with stability under arbitrary base change;
it does not duplicate the old criterion's more general flat-only hypothesis.

No assertion is made that these modules are globally unreachable: other targets or items
may still need them. The unchanged public Mathlib fpqc import may also transitively retain
some Mathlib modules listed above; their explicit proof steps are what was pruned.

## Where the brief, the DAG or earlier work was wrong

The existing six-step plan is mathematically valid but longer than necessary. Its recorded
Mathlib candidate already pointed to the source-library covering-family descent theorem.
Using that theorem and Mathlib's formal-unramified descent closes the item outright,
without the two Sheaf descent obligations or explicit diagonal base-change glue.

No statement was disputed or corrected. No source-library definition was changed.
The existing proof docstring described the old route and was updated to describe the
compiled proof. LeanSearch returned Internal Server Error for both new-node searches;
these attempts are recorded as unavailable, while LeanFinder and source grep succeeded.

The Stacks files were absent from the repository's literature directory on this machine.
Their relevant 02VM, 02KP and 02HE passages were read from the existing local Stacks copy.
The actual proof uses the existing source-library and Mathlib proofs, which were read
in the read-only project and Mathlib checkouts.

## New nodes

`lem-galois-fpqc-family-descent-of-local-property` attaches the already proved declaration
`AlgebraicGeometry.Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. It records the precise generic theorem
used twice by this proof: arbitrary base-change stability, Zariski locality, and descent
along surjective flat quasi-compact maps imply descent along an fpqc covering sieve family.
Its Lean record has `existing: true`; it creates no new module or proof obligation.

`lem-galois-lft-formally-unramified-single-fpqc-descent` attaches the two already proved
Mathlib `DescendsAlong` instances from
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`, one for local finite type and one
for formal unramifiedness. It is a Mathlib leaf with `existing: true`, not a new Lean
statement or an unproved reduction. Both names were verified by `#check`.

No change record is needed: the public interface is unchanged.

## Second reading by B3

1. **Diff and statements.** Compared the delivered module with the repository version. The
   theorem name, binders, hypotheses, conclusion, and universes are byte-for-byte unchanged;
   only proof text, proof-only imports, and its explanatory docstring changed. No definition or
   target statement changed. Verdict: pass.

2. **Compilation and axioms.** Compiled the module alone and with all sandbox modules using the
   launcher; both completed without errors or warnings. The theorem has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`; its checked axioms are only
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Split statements and searches.** No theorem with a new Lean statement was split off. The
   two added DAG records attach existing closed declarations and introduce no obligations or
   duplicate library theorem. The source-library covering-family theorem and both Mathlib
   descent instances were checked by name and signature. Verdict: pass.

4. **Route and pruning.** The proof follows the existing unit route at the target level while
   taking the shorter generic covering-family descent route below the unit. Removed imports and
   proof dependencies are listed above; no unused proof import remains. Verdict: pass.

5. **DAG agreement.** The item's node proof, proof dependencies, and proof origin describe the
   compiled four-step proof, and the attached metadata nodes record the exact declarations used.
   The unit's statement and realized route remain unchanged. Verdict: pass.

I changed the report only by adding this second-reading record; no Lean declarations or
   statements required repair.
