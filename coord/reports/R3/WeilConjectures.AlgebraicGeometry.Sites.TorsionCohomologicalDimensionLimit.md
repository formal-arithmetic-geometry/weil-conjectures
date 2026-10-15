## What changed

Changed only the proof of
`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit` in
`WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit`.
Added two proof-only imports:
`Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit` and
`Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`.
All existing signatures, universes, visibility, public imports, definitions and docstrings stay
unchanged.

The existing declaration
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit` already states
the affine-limit result with precisely the same indexing category, limit cone, compactness,
quasi-separatedness and affine-transition assumptions. Its bound uses derived global sections;
the source bound uses Ext-based `Sheaf.H`. The proved natural isomorphism
`AlgebraicGeometry.Scheme.nonempty_sheafH_extDerivedIso` identifies these groups in every degree.
The proof transports the bound at every stage through the inverse component equivalence,
applies the existing affine-limit theorem, then transports the resulting bound through the
forward component equivalence. This is reuse of an existing statement, with explicit Lean
conversion between the two cohomology definitions.

Both added imports passed `tools/import_direction.py may`. The single-file compile through
`lcompile.py` passed cleanly (9.0 seconds). The comparison holds for every scheme, sheaf and
nonnegative degree; it adds no assumptions for empty schemes, zero sheaves, degree zero or a
zero dimension bound. Cofilteredness already supplies nonemptiness of the indexing category.

The required LeanFinder search returned only affine-transition-limit geometry lemmas.
Loogle did not know the project-specific bound name, so that query is inconclusive.
The wrapper grep returned no matches; direct `rg` on both library roots found the existing
affine-limit statement and the proved Ext-to-derived comparison. Exact queries and responses
are also recorded by `msearch.py` in the sandbox's `searches.jsonl`.

## Proved and sorry left

Closed the one direct hole in the assigned module:
`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`.
No direct `sorry` remains in that module. Added zero holes and split off zero statements.

The proof uses the existing open theorem
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit`
in `Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit`
(node `lem-sc-cd-affine-limit`). Its existing `sorry` is not changed by this delivery.
Thus the geometric affine-limit argument remains an obligation of that existing module;
this delivery consolidates the two formulations rather than claiming to discharge that
argument. The comparison theorem `nonempty_sheafH_extDerivedIso` is already proved.

## No longer needed

None. No existing import is removed. Both new proof imports are used. The existing
affine-limit module retains the original node's finite-data descent, continuity,
filtered-colimit and torsion-union proof dependencies; none is claimed pruned.
There are no new nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The assigned source module has no direct `lean.module` attachment in `dag/nodes/`.
Its docstring points to `lem-sc-cd-affine-limit`, whose Lean attachment is instead the
existing theorem in `Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit`.
The two statements have different cohomology definitions, but the library already proves
the required comparison. The node and its proof route remain unchanged: that existing
attached theorem still carries the original three-step affine-limit argument. No node is
made to cite itself, and no duplicate statement or replacement hole is introduced.

The blueprint source path named by the node is absent from this machine's repository.
The node's complete statement, proof steps, unit record and the relevant Lean declarations
were read; this delivery uses the existing stated theorem rather than inventing a new
geometric argument or changing the unit route.


## Second reading by R3

1. **Existing interface: PASS.** Read the complete repository and delivered modules and
   their unified diff. The sole existing theorem's signature, including its universes,
   category size, cofilteredness, compactness, quasi-separatedness, affine transitions,
   cone, limit witness and uniform bound, is byte-for-byte unchanged (also checked by
   extracting the text before `:=`). The two existing public imports, visibility,
   definitions and docstrings are unchanged. The only Lean changes are two plain
   proof-only imports and the replacement of the theorem's proof. No change record is
   needed and no module held by another group is adapted.

2. **Proof and axioms: PASS, with the reported existing dependency still open.**
   Independently compiled the delivered module through `lcompile.py`: exit 0,
   no warnings or errors, 9.2 seconds. Read both cohomological-dimension definitions,
   the comparison theorem and the existing affine-limit theorem. The first injection
   is from derived cohomology into Ext cohomology, so the stage hypotheses give the
   required derived bounds; the final injection is from Ext cohomology into derived
   cohomology, so the derived limit bound gives the original conclusion. Both bounds
   quantify over the same sheaves, torsion predicate and natural degrees. No assumption
   is lost in either direction. No forbidden declaration, new definition, or direct
   `sorry` occurs. A scratch copy compiled in 8.1 seconds with `#print axioms` for all
   three declarations: the comparison uses exactly `propext`, `Classical.choice`,
   `Quot.sound`; the delivered theorem and the existing affine-limit theorem use these
   plus `sorryAx`. This is the disclosed open dependency, not a complete geometric
   affine-limit proof. No data is chosen in a definition from an unproved existence
   theorem: the component isomorphisms are eliminated locally in a proof of a proposition.

3. **Split-off statements: PASS (none).** No new statement, module or node is delivered,
   and no hole is added. Read the already existing affine-limit theorem and its full
   docstring proof. Its indexing category and geometric hypotheses match exactly.
   The comparison is valid for empty schemes, zero sheaves and degree zero; transport
   imposes no new condition at bound zero. A cofiltered indexing category is nonempty,
   so the proof does not silently discard an allowed empty diagram. Independent
   LeanFinder search for the Ext/global-sections comparison found generic Ext and
   sheaf-cohomology tools, not a shorter scheme-specific bound theorem; Loogle
   confirmed `Function.Injective.subsingleton`. Direct `rg` searches in both library
   roots found no existing equivalence of the two bound predicates that would remove
   the explicit transport. Queries and results are recorded in `searches.jsonl`.

4. **Route and pruning: PASS.** This uses the already stated theorem carrying the
   affine-limit node, without creating a restatement under a new name. Both plain
   imports are used by name; the public imports provide signature-level notions.
   Independently reran both import-direction checks successfully. Read unit
   `sk-prop-sf-cbc`, including `realized`, and the node's complete three-step argument.
   The existing attached theorem still carries the finite-data descent, continuity,
   filtered-colimit and torsion-union argument. No unit statement or step is replaced.
   `## No longer needed` is complete: no old import or proof-dependency node is removed,
   and no pruning is claimed.

5. **DAG agreement: PASS.** Searched all nodes for the assigned module and declaration:
   neither is a `lean` attachment. The docstring's `lem-sc-cd-affine-limit` is attached
   instead to the existing derived-cohomology theorem that this proof applies. Read its
   `lean`, `proof`, `proof_deps`, `proof_origin`, chapter and unit fields, and the existing
   comparison's change record. Those records still describe their attached declarations
   accurately; changing the affine-limit node to cite itself would be wrong. No node
   metadata needs changing for this proof-only conversion of the unassigned duplicate.

**Changes made by the second reader:** added this independent review and additional
search evidence only. The Lean proof needed no repair. Closed holes remain exactly one,
`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`; added holes zero;
split off zero; pruned none. These are direct-hole counts, not a claim that the existing
open affine-limit dependency is proved or that the targets' import closure is sorry-free.
