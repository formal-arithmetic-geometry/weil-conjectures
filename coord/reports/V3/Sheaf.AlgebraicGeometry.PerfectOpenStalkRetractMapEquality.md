## What changed

Proved `AlgebraicGeometry.Scheme.exists_open_stalk_retract_map_eq` in
`Sheaf.AlgebraicGeometry.PerfectOpenStalkRetractMapEquality`, preserving its signature
and visibility. Added a proof-only `import all Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality`
to reuse its proved private finite-generator shrinking and restriction-transport helpers.
Restricted the given splitting to Z, transported it to the open subscheme, compared
images of finitely many free generators, and recovered the original maps using the
splitting identity. Updated the existing node's proof, proof_deps and proof_origin.
No definitions, statements, other modules, or public imports changed.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.exists_open_stalk_retract_map_eq`
(node `lem-sc-perfect-open-stalk-retract-map-equality`).
No holes remain in the item, and no holes or modules were added. This is a proof,
not a decomposition. The reused finite-free germ and transport helpers are proved.
The empty free basis, equal successive opens, and arbitrary structure rings require
no additional hypotheses; the finite coproduct/intersection argument covers them.

## No longer needed

The planned proof dependency `lem-weil-pbc-stalk-internal-hom-finite-presentation`
(module `Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation`) is unnecessary:
finite generator images suffice, without internal Hom or finite presentation.
`def-pc-perfect-complex` is no longer a proof dependency; the explicit finite-retract
hypothesis suffices, while its statement dependency is retained. Its module
`Sheaf.AlgebraicGeometry.PerfectComplex` is not imported for the proof.
Neither planned dependency was an original explicit import in the item's module.
The two original public imports remain required by the statement.
These dependencies are pruned from this node's proof route; no claim is made that
other targets cease to need them.

## Where the brief, the DAG or earlier work was wrong

The DAG suggested a finite-presentation internal-Hom comparison, but the source's
finite-type injectivity argument only needs finitely many generator germs. The
already proved finite-free calculation supplies that step directly. No mathematical
statement error or interface change was needed. The unit realization record is
empty, and this proof changes only the argument below the unit level.

## Second reading by V3

1. PASS. Compared the entire delivered module with the repository version and
   checked the existing theorem signature byte for byte. The signature, visibility,
   definitions, and public imports are unchanged. The only added import is the
   proof-only `import all` of `FiniteFreeStalkMapEquality`; its private helpers are
   used explicitly. There are no adapted modules or interface change records.
2. PASS. Compiled the delivered file cleanly with `lcompile.py` (14.7 seconds).
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.exists_open_stalk_retract_map_eq`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered module
   has no remaining `sorry`, forbidden declaration, or hollow definition.
   Read the three reused private helpers: finite germ shrinking, equality transport
   along a functor isomorphism, and faithfulness of restriction along an isomorphism.
3. PASS. No statements or nodes were split off, and no arbitrary witness was
   chosen from an unproved existence theorem. The finite-retract data comes from
   the theorem's explicit hypothesis. Checked the empty finite basis, repeated
   equal opens, and unrestricted target sheaf/ring: finite intersection and
   coproduct extensionality cover these cases without extra hypotheses.
4. PASS. The finite-generator route agrees with the injectivity argument of
   [Stacks Tag 01CP](https://stacks.math.columbia.edu/tag/01CP).
   Independently searched with LeanFinder for maps from a finitely generated
   sheaf with identical stalk maps, and searched the library and Mathlib module
   sheaf APIs with `rg`. The hits provide germ/extensionality components, not a
   shorter theorem establishing this neighbourhood conclusion. Reusing the
   proved finite-free germ helper avoids introducing any lower holes. Both old
   dependencies dropped from `proof_deps` are listed in `## No longer needed`.
   Both public imports are needed for the statement; the added private import is
   needed for the proof. Read `dag/units/sk-prop-av-cube.json`: its realization
   lists are empty, and this below-unit tool argument does not replace the unit's
   cube-theorem step or alter its route.
5. PASS. Compared the node with the repository version: only `proof`,
   `proof_deps`, and `proof_origin` changed. Its four steps match the splitting,
   generator germs, finite shrinking, and restriction transport in Lean, and
   `proof_deps` is exactly the union of their `uses`. No new node fields require
   validation because there are no new nodes.

Changes by the second reader: appended this review and recorded an independent
search. No Lean, signature, import, or node repair was needed. Closed holes: the
one declaration listed above. Added holes: none.
