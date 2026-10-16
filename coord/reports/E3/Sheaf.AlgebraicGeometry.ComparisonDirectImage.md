## What changed

Proved all three holes in `Sheaf.AlgebraicGeometry.ComparisonDirectImage` without
changing any existing declaration's signature, visibility or definition. Invertibility
uses the existing underived canonical mate isomorphism and the source library's
right-acyclic derived base-change criterion. Identity and composition are proved by
private, fully proved helpers: sectionwise restriction coherence, adjunction mates,
and the universal property of derived functors. The helpers abstract the categorical
calculations so compilation avoids unfolding large concrete sheaf functors.

Updated `prop-weil-pbc-comparison-direct-image`'s proof, proof dependencies and proof
origin to this shorter route. No unit statement or realized unit proof step is bypassed;
the item is a supporting proposition below its recorded unit. The current main snapshot
has the same canonical-mate/coherence argument, which the updated proof origin cites.

Removed unused imports, including one public import. The interface change record is
`coord/changes/E3-comparison-direct-image-import-pruning.md`. The original source of the
sole direct importer, `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData` (held by E1),
compiled against the revised module without any adaptation in 11.6 seconds. The item
compiled in 12.0 seconds before packaging. No other module is changed.

## Proved and sorry left

Closed 3 of 3 original holes, all attached to node
`prop-weil-pbc-comparison-direct-image`:

- `AlgebraicGeometry.ProEtale.isIso_comparisonDirectImagePlus`.
- `AlgebraicGeometry.ProEtale.comparisonDirectImagePlus_id`.
- `AlgebraicGeometry.ProEtale.comparisonDirectImagePlus_comp`.

Added 0 holes; 0 split-offs; 0 holes remain in the delivered module. Every private
helper is proved. The two existing data definitions are unchanged. This is proof
reuse from existing library declarations, not a claim that every transitive dependency
is free of pre-existing holes.

## No longer needed

Removed these direct imports:

- `public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `import Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`.
- `import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`.
- `import Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity`.
- `import Sheaf.RingTheory.IndEtaleStability`.
- `import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`.
- `import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`.
- `import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections`.
- `import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`.

Removed the following explicit dependencies from this node's planned proof:

- `lem-weil-pbc-comparison-pullback`.
- `lem-weil-pbc-site-pullback-abelian-exact`.
- `lem-weil-pbc-dplus-injective-representative`.
- `lem-weil-pbc-right-derived-plus-injective`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `lem-sp-grothendieck-enough-injectives`.
- `lem-weil-pbc-comparison-global-cohomology`.
- `lem-weil-pbc-etale-restriction-injectives`.
- `lem-weil-pbc-proetale-restriction-injectives`.
- `lem-weil-pbc-ind-etale-basis`.
- `lem-pc-quasi-compact-base-change`.
- `lem-weil-pbc-affine-morphism-permanence`.
- `lem-weil-pbc-derived-cohomology-continuity`.
- `lem-weil-pbc-ind-etale-stability`.
- `lem-weil-pbc-comparison-sections`.
- `lem-weil-pbc-leray-acyclicity-quasi-iso`.
- `lem-weil-pbc-ring-modules-grothendieck-abelian`.
- `lem-weil-pbc-basis-derived-detection`.

In particular the Sheaf modules `DerivedCohomologyContinuity`, `IndEtaleStability`,
`ComparisonPullbackCoherence`, `ProEtaleComparisonSections`, `SitePullbackAbelianExact`
and `ProEtaleSiteComparison` are not needed as additional imports or new proof work
for this item. The acyclicity node is retained. Source-library modules such as
`Comparison.LowerStarAcyclic` and `RightDerived.Acyclic` remain transitively imported
through `Comparison`; removing their redundant direct imports does not prune their
underlying mathematical results. The removed DAG dependencies are no longer explicit
obligations of this node; this report makes no claim that they are unused elsewhere
in the targets' closure. No module is withdrawn and no tool approval is removed.

## Where the brief, the DAG or earlier work was wrong

The planned seven-step proof did not account for the already implemented underived
comparison isomorphism and its direct-image acyclicity consequence, which immediately
supply the invertibility criterion for the very canonical derived transformation in
the statement. Repeating the full derived-section continuity argument is unnecessary.
The original extra proof imports were also redundant. No statement was found false,
and no definition or target statement is repaired or weakened. No new nodes are needed:
all added helpers are private proved calculations and the substantive comparison and
acyclicity results already exist in the library.

## Second reading by E3

1. **Existing interface: PASS.** Compared the delivered module with the shared
   repository using `diff`, then compared all five existing declaration headers
   byte for byte. All signatures and visibility agree. Both composition-isomorphism
   definitions also agree byte for byte. The removed public import is explicitly
   declared in `coord/changes/E3-comparison-direct-image-import-pruning.md`;
   its Users table agrees with a fresh `tools/downstream.py` listing of all eleven
   downstream modules. No target, definition or other module is modified.

2. **Proofs and compilation: PASS, with existing dependency holes identified.**
   Independently compiled the delivered module successfully in 12.0 seconds.
   A scratch copy with `#print axioms` for all sixteen declarations compiled in
   12.5 seconds. Both data definitions, all eleven private helpers, and the public
   identity and composition theorems use only `propext`, `Classical.choice` and
   `Quot.sound`. `isIso_comparisonDirectImagePlus` additionally uses `sorryAx`
   through existing imported comparison/acyclicity results; its local hole is
   closed, but its full dependency closure is not yet proved. Read the actual
   underived comparison and derived acyclicity criterion: the proof applies the
   criterion to the specified mate, rather than choosing a different isomorphism.
   Source scanning found no `sorry`, forbidden declaration or kernel-check bypass
   in the delivered module. No data witness or construction is added.

3. **Split-off statements: PASS (none).** There are no new public statements,
   split-offs, new nodes or remaining local holes. Read all eleven private helpers:
   restriction coherence is checked on presheaf sections, mate coherence follows
   by the adjunction hom-equivalence, and derived coherence follows by the unit
   factorization and `rightDerived_ext`. These are fully proved categorical
   calculations, including identities and arbitrary composite morphisms; no
   nonempty-scheme, nonzero-ring or nonzero-complex assumption is introduced.

4. **Reuse, imports and route: PASS.** Independently searched the library and
   Mathlib, including Loogle's `"mateEquiv"` query and the source of
   `mateEquiv_vcomp`/`mateEquiv_hcomp`. Those general pasting results do not directly
   include the two specified composition isomorphisms; the existing short
   componentwise helper is sound. The derived cube theorem concerns exact
   transverse edges, rather than composition of two possibly nonexact direct
   images, and does not replace `derived_comp`. The invertibility proof already
   takes the short existing-library route. The two retained public imports are
   required by the public statements and data definitions. The original source
   of the sole direct importer, `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData`,
   compiled against the scratch module in 17.4 seconds without adaptation.
   Checked all twelve removed direct imports and all eighteen removed old
   `proof_deps` against `## No longer needed`; every removal is recorded.
   Read `dag/units/sk-thm-properbasechange.json` and its source `_section.md`:
   this supporting node realizes none of the unit's fixed statement or steps,
   and their projective-line, reduction and torsion-assembly route is preserved.
   Redundant direct imports removed here do not establish global module pruning.

5. **DAG and proof record: PASS.** The existing node changes only `proof`,
   `proof_deps` and `proof_origin`. The dependency list is exactly the union of
   the proof steps' `uses`. Read the retained acyclicity node and its recorded
   source declaration: the direct-image acyclicity lemma used here is its
   immediate consequence in the same module. The site-comparison node records
   the same underlying comparison construction. The four rewritten steps
   correctly describe underived invertibility, acyclicity, restriction/mate
   coherence and derived unit-factorization coherence. The cited current
   blueprint coherence paragraph exists and agrees with those calculations.

Second-reading changes: added this independent review and the precise axiom
qualification. No Lean proof, signature, definition, import or node needed repair.
The delivery closes the three named original local holes and adds zero holes;
the two coherence theorems are also closed throughout their axiom dependencies.
