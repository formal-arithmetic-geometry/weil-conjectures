## What changed

Proved `AlgebraicGeometry.Scheme.closed_subset_proper_over_base_properties` without
changing its signature. The reduced induced structure factors into every chosen closed
structure by the proven source-library kernel criterion and Mathlib closed-immersion
lifting. The factor is a surjective closed immersion. Properness descends using the
existing separatedness-descent declaration and Mathlib universal-closedness descent.
Closed-subset inheritance uses the same factorization. The image clause uses the
already proved `isProper_imageι_comp` and `Hom.ker_eq_vanishingIdeal`.
Updated the node proof, dependencies and origin, and the proof docstring.
Added proof-only imports of the source-library IdealSheaf Basic and Subscheme modules.
No public imports, definitions, statements, or unit realization steps changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.closed_subset_proper_over_base_properties`
(node `lem-weil-pbc-closed-subset-proper-over-base-properties`).
No sorry remains in the delivered module; no holes added or split off.
This proof still depends on the existing sorry
`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed`
(node `lem-weil-pbc-surjective-universally-closed-separated`). It does not establish
sorry-free axioms for the full target closure.
The reduced factorization is proved directly with source-library lemmas; the holed
`Sheaf.Paper.ReducedSourceFactors` module is not imported.

## No longer needed

Removed imports:
- `Sheaf.AlgebraicGeometry.SchemeTheoreticUnion`:
  `lem-weil-pbc-scheme-theoretic-union` is no longer needed by this proof.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`: redundant explicit import;
  its statement-level dependency remains through ClosedSubsetProperOverBase.

The old union construction, `lem-weil-pbc-closed-immersion-comp`, and
`lem-weil-pbc-closed-subset-closed-subscheme` proof dependencies are unnecessary
for this route. The reduced-source factor is itself a closed immersion
by `IsClosedImmersion.of_comp_isClosedImmersion`.
No assertion is made that these modules become globally unreachable: other targets
may still import them. All nodes realizing unit sk-thm-p1 remain untouched.

## Where the brief, the DAG or earlier work was wrong

The six-step plan is valid but its scheme-theoretic union is unnecessary: reduced
source factorization gives a surjective closed immersion directly into every structure.
The existing source-library kernel/range criterion, kernel of a reduced-source map,
and proper-image theorem supply the requisite shorter route. No mathematical statement
was found false. The local clone does not contain the Stacks .tex files; source locators
and proof ingredients were read from the existing node records and Lean docstrings.
Compilation covers empty closed subsets, equal subsets and nonreduced chosen structures
without extra hypotheses or case exclusions. No new statements require edge-case tests.


## Second reading by M2

1. Visible changes: compared the sole delivered module with the repository version;
   the existing theorem signature is byte for byte identical. There are no changed
   definitions, added hypotheses, weakened conclusions, or new declarations. Public
   imports are unchanged; all added imports are proof-only.
2. Proof and trust: the module compiles cleanly through `lcompile.py`. A scratch
   `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is the reported existing separatedness-descent hole. The kernel criterion,
   reduced-source kernel equality, and proper-image theorem each have only standard
   axioms. No prohibited declaration, local sorry, or hollow definition occurs.
3. Split-offs: none. All local intermediate claims are proved. Checked the argument
   for empty subsets, equal subsets, and nonreduced chosen structures: reducedness is
   required only of the canonical sources, not of the arbitrary chosen structure.
   Range equality and injectivity establish surjectivity without nonemptiness.
   Independent source search also found `existsUnique_fac_of_range_subset_range`;
   importing its larger module would merely package the same short kernel/lift argument.
4. Route and pruning: the reduced-source argument is valid and below the unit level.
   Read `dag/units/sk-thm-p1.json`; none of the three removed proof dependencies
   realizes a unit statement or step. The reduced structure stays publicly imported
   through the definition. Verified import necessity: deleting the proof-only Subscheme
   import fails synthesis of the reduced-source instances. Basic supplies the kernel
   lemmas, Proper the image theorem, and the separatedness module the descent theorem.
   Completed the pruning report with the omitted closed-subset construction dependency.
5. Nodes: the only changed JSON fields are `proof`, `proof_deps`, and `proof_origin`.
   The proof dependencies equal the union of the step dependencies. The steps accurately
   describe the kernel factorization, surjectivity, properness descent, subset inclusion,
   and reduced proper image. No new nodes or change records are required.

Second reading changed only the report: completed the list of removed dependencies
and recorded these checks. The Lean proof and node records needed no repair.
