## What changed

Proved `AlgebraicGeometry.Etale.finiteEtaleModuleTraceData` without changing its
signature. The trace is the counit of the existing coefficient-linear reverse
adjunction `lowerStarUpperStarAdjunctionOfIsFinite`. The proof computes on geometric
stalks: ordinary restriction is diagonal, the reverse counit is the sum, and the
finite-fibre cardinality gives the scalar. Stalks detect equality.

Added `Sheaf.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion`, containing a fully
proved normalization of the reverse-adjunction unit on stalks. Its two private
helpers prove the module-valued pullback germ formula and the section formula for
the localization isomorphism. The generic pullback germ proof adapts the proved
abelian argument in `Sheaf.Paper.InverseImageStalkGerm`; the abelian-only statement
is not imported or reapplied to module sheaves.

Updated the item's DAG proof and dependencies and added the normalization node.
The unit's trace-splitting step stays: this is a shorter implementation below that
step, using existing reverse adjunctions and stalk formulas.

Validation: both files compile with no errors, warnings or local `sorry`.
The finite-sum proof covers degree zero without requiring a lift; empty base makes
the equality test vacuous. No invertibility, connectedness, nonzero-ring or
surjectivity hypothesis was introduced. The original universes are unchanged.

## Proved and sorry left

- `AlgebraicGeometry.Etale.finiteEtaleModuleTraceData`
  (`lem-weil-pbc-finite-etale-module-trace-data`): proved, one original sorry closed.
- `AlgebraicGeometry.Etale.finiteEtaleUnit_stalk_inclusion`
  (`lem-weil-pbc-finite-etale-unit-stalk-inclusion`): proved, no sorry.
- All four private helpers are proved.

No sorry remains in either delivered module. No new unproved dependency is added.
The second reading's scratch `#print axioms` checks show that both public theorems
depend only on `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.Paper.DirectImageSplitCoverProduct`
- `Sheaf.Paper.FiniteEtaleEtaleLocalSplit`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

The localization-restriction source module is still used transitively in the
new normalization proof. Its node `lem-weil-pbc-etale-inverse-image-restriction`
is retained there. The sheaf and fibre definitions remain statement dependencies.

The item's proof no longer needs the following planned dependencies/modules:

- `lem-weil-pbc-direct-image-split-cover-product`
  (`Sheaf.Paper.DirectImageSplitCoverProduct`)
- `lem-weil-pbc-finite-etale-etale-local-split`
  (`Sheaf.Paper.FiniteEtaleEtaleLocalSplit`)
- `lem-weil-pbc-finite-etale-trace-exists`
  (`Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`)
- `lem-weil-pbc-etale-covering-base-change` (no Lean record in this checkout)
- `def-weil-pbc-etale-sheaves` (`Sheaf.AlgebraicGeometry.EtaleSheaves`)
  as a proof dependency; its mathematical notion remains a statement dependency.

These are pruned from this item's route; other targets or source constructions
may still need them. In particular the existing source reverse-adjunction proof
has its own finite-morphism splitting machinery. This delivery makes no claim
that all splitting theory disappears from the library's transitive closure.

## Where the brief, the DAG or earlier work was wrong

The original plan reconstructed and glued a coefficient-linear trace using the
abelian trace family. The source library already supplies `f_* ⊣ f^*` in ModuleCat,
so reconstructing that family is unnecessary for this statement. The missing glue
was its normalization against `upperStarCompSheafFiberIso`; that is now proved.

The original proof dependency `lem-weil-pbc-etale-covering-base-change` has no Lean
record here, contrary to the queue premise that every planned dependency is stated.
It is not needed by the proof delivered.

The local literature checkout contains lists only, not the cited TeX. The Stacks
Section 03SH and Definition 03SE were read online at
https://stacks.math.columbia.edu/tag/03SH and
https://stacks.math.columbia.edu/tag/03SE; the normalization is proved from the
readable source-library definitions and the general-site germ lemmas. LeanSearch
returned Internal Server Error; Loogle, LeanFinder and source grep were used.

## New nodes

`lem-weil-pbc-finite-etale-unit-stalk-inclusion` records the fully proved theorem
in `lean/Sheaf/AlgebraicGeometry/FiniteEtaleUnitStalkInclusion.lean`. Its statement
identifies the stalk of the reverse-adjunction unit with the explicit extension
by zero summand inclusion, for any module sheaf on the source. It has no degree
hypothesis and is not a restatement of the item. Its proof gives the germ and
adjunction normalizations in full; no step is left as sorry. The blueprint was
searched for “finite etale unit stalk inclusion” and no matching node was found.
No definition or existing theorem statement changed; no change record is needed.


## Second reading by S2

1. Compared the entire item against the repository with `diff`. The existing
   `finiteEtaleModuleTraceData` signature is byte-for-byte identical. No existing
   definition, statement, universe, instance assumption or public import changed.
   The normalization module is new and has its own node. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py`: no errors or
   warnings. Inspected all four private helpers and both public proofs; no local
   `sorry`, hollow definition, axiom or prohibited implementation escape occurs.
   Scratch copies with `#print axioms` report exactly `propext`, `Classical.choice`
   and `Quot.sound` for each public theorem, without `sorryAx`. Verdict: pass.
3. There are no unproved split-off statements. The new, proved normalization is a
   strictly intermediate assertion for arbitrary source sheaves, not the trace
   degree theorem under another name. Its docstring and node give the germ proof.
   Checked the identity-map/single-summand case, empty fibres (normalization is
   vacuous), degree zero (empty sum), empty base, and zero coefficient ring.
   Independent Loogle search `"sheafFiber", "Adjunction"` returned no hits;
   LeanFinder search for graph extension and the pushforward-left-adjoint unit
   returned only topological presheaf/stalk-skyscraper results. Source `rg` searches
   found the graph and stalk constructions and the abelian inverse-image germ
   theorem, but no existing module-valued reverse-unit normalization. Verdict: pass.
4. Read the proof from the trace counit down through the two triangle identities,
   projection-inclusion sum, and germ normalization. Existing upstream adjunctions
   and stalk formulas provide the short route; the abelian germ theorem cannot be
   applied directly to ModuleCat. Imports distinguish signature needs from proof
   needs. Every removed old proof dependency is reported; inverse-image restriction
   remains used through the new node. Read `dag/units/sk-thm-p1.json`, including its
   `realized` fields: trace splitting in the locally constant reduction remains,
   and no realized unit step is bypassed. Verdict: pass.
5. Read both delivered node records against the Lean and upstream declarations.
   The existing node's steps and dependency union describe the counit, triangles,
   stalk decomposition, degree and conservative stalk test. The new node's fields,
   verbatim Lean signature, source, search records and complete proof describe the
   graph-germ normalization. No existing mathematical statement changed.
   Verdict: pass.

Second reading changed only this report: added the omitted direct removal of
`Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`, replaced the earlier axiom caveat
with the verified axiom output, and recorded this independent review. No Lean or
DAG repair was necessary.
