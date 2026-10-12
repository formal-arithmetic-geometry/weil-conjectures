## What changed

Proved `TopCat.shortExact_iff_stalkFunctor_map_shortExact` in
`Sheaf.Topology.AbelianSheafShortExactStalkwise`, with its signature unchanged.
The forward direction is `ShortComplex.ShortExact.map_of_exact` for each stalk
functor. The reverse direction applies Mathlib's
`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` to S and to the two endpoint
complexes `(0, S.f)` and `(S.g, 0)`. `ShortComplex.exact_iff_mono` and
`ShortComplex.exact_iff_epi` turn their exactness into the endpoint conditions;
`ShortComplex.ShortExact.mk'` assembles the three conditions.

Removed the unused public import of
`Sheaf.Topology.PresheafModuleStalkFunctor`: the statement uses Mathlib's
abelian-group stalk functor directly, and no declaration of that project
module is needed. Updated the item's DAG proof, proof dependencies, and proof
origin to describe the compiling route. No definition or statement changed. The public import removal is recorded in
`coord/changes/abelian-sheaf-short-exact-stalkwise-imports.md`; it lists all
transitive users and the inspection of the five direct importers.
The unit record `sk-thm-curveestimate` realizes its statement at
`thm-sc-proper-cohomology` and has no realized proof steps here; this is a
change below the unit level.
The second reader additionally removed the redundant direct public import
of `Mathlib.Algebra.Homology.ShortComplex.ShortExact`, whose declarations
remain re-exported by the retained Mathlib sheaf module. The same import
change record documents this removal.

## Proved and sorry left

Proved `TopCat.shortExact_iff_stalkFunctor_map_shortExact`
(node `lem-sc-abelian-sheaf-short-exact-stalkwise`), the module's only sorry.
No sorry remains in the delivered module; none is added elsewhere.
Local compilation succeeds. The delivery dry run performs the axiom probe,
server compilation, and preflight.

## No longer needed

Removed import/module: `Sheaf.Topology.PresheafModuleStalkFunctor`.
The second reading also removed the redundant direct public import
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`, already re-exported by
`Mathlib.Topology.Sheaves.Abelian` through `Grp.AB` and `ShortComplex.Ab`.
No imports were added.

Proof dependencies pruned:
`lem-sc-abelian-sheaf-mono-iff-stalk-mono` and
`lem-sc-abelian-sheaf-epi-iff-stalk-epi` (both endpoint conditions now follow
from the existing middle-exactness criterion applied to zero-map complexes);
`def-sc-topological-abelian-cohomology` (no cohomology construction is used);
`def-weil-pbc-module-stalk` (no module-over-a-ring stalk construction is used).
The last two remain statement dependencies, whose records and meanings are
unchanged. These prunings are of this proof's edges; other items may still need
the nodes/modules. Kept `def-weil-pbc-exact-sequence` and
`lem-sc-abelian-sheaf-exact-iff-stalk-exact` as the two actual proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The earlier search assessment said Mathlib's middle-exactness criterion needs
separate stalk mono/epi criteria for the endpoints. It already suffices when
applied to complexes with a zero first or second arrow. The existing
`def-weil-pbc-exact-sequence` Mathlib record explicitly includes the needed
`exact_iff_mono` and `exact_iff_epi` clauses. No new statements are necessary.

The Stacks TeX files are not present in this read-only clone. The complete
proof uses the Mathlib sources read locally, and its DAG proof origin records
the exact declarations. Search via LeanFinder, Loogle and grep found the
exactness and zero-map endpoint APIs; the source library has no packaged
short-exact stalkwise theorem. The argument works for an empty space as well:
the stalkwise exactness theorem handles the vacuous point quantifier. Zero
arrows and zero sheaves require no extra hypotheses.

## Second reading by U1

1. **Unchanged interface: pass.** Compared the complete delivered module
   against the read-only repository using `diff`; independently asserted
   that the existing theorem signature, including its whitespace, is byte
   for byte unchanged. There is one existing declaration and no definition
   change. The public import removals have the declared change record.
   Inspected all five direct importers: none relies on declarations from
   the removed presheaf-module stalk module, and `ConstantSubsheafPeelLayer`
   imports it separately. The redundant ShortExact import remains available
   by a public import chain from the retained Mathlib module.
2. **Proof and trust: pass.** Local compilation succeeded without warnings.
   Read the forward preservation proof and both zero-map endpoint reductions
   against Mathlib's actual definitions and lemmas. No `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern` occurs in the module.
   A scratch copy with `#print axioms
   TopCat.shortExact_iff_stalkFunctor_map_shortExact` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`.
3. **Split-off statements: pass, none.** No new statement, helper theorem,
   node, or postponed obligation was introduced. Reviewed the empty-space
   case: the exactness criterion applies to S and both endpoint complexes
   even when the point quantifier is vacuous. Zero complexes also require
   no additional condition. Independent LeanFinder and grep searches for
   stalkwise short exactness and reflection of short exactness found no
   shorter packaged theorem; Loogle's unqualified ShortExact query was not
   recognized, so no conclusion is drawn from that query. Searched the
   project and upstream declarations as well.
4. **Route and pruning: pass after import cleanup.** The proof goes directly
   through the proved Mathlib criterion, with no project lemma still using
   `sorry`. The report lists all four old proof dependencies that are absent
   from the new proof. Checked `dag/units/sk-thm-curveestimate.json`: its
   realized statement is `thm-sc-proper-cohomology` and its realized steps
   are empty. This node is below the unit level; no unit route is bypassed.
   Removed only the redundant direct ShortExact import discovered during
   this reading, then verified that the proof and signature still compile.
5. **DAG agreement: pass.** Only `proof`, `proof_deps`, and `proof_origin`
   differ from the repository node. Their steps describe the finite-limit
   and finite-colimit preservation argument and the two zero-map endpoint
   reductions exactly as written in Lean. Asserted that the dependency list
   equals the union of the steps' `uses`. The retained Mathlib node records
   cover the exactness criterion, ShortExact, and exact_iff_mono/epi.

Changes made by this reading: removed the redundant direct public import
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`; updated the import change
record and report. The Lean proof and DAG proof metadata needed no repair.
