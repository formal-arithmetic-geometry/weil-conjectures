## What changed
Replaced the hole in `standard_resolution_formula` by a two-factor calculation.
The module-to-abelian-sections half is proved in `standard_sections_factorization`.
The Ext-to-sections half is isolated as `ext_sections_factorization`; the final
proof applies the inverse Ext-to-sections map to the first equality and uses the
defining equation for b. All existing signatures and public imports are preserved. Compiler-option
changes are recorded in `coord/changes/C1-standard-resolution-elaboration.md`.

## Proved and sorry left
Closed: `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.standard_resolution_formula`.
Added and proved:
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.standard_sections_factorization`.
Added hole:
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.ext_sections_factorization`.
The original single hole is reduced to one strictly smaller hole: this is a
decomposition, not a net reduction in the number of holes. No other sorry remains
in the delivered sources, and no data is chosen from an unproved existence theorem.

## No longer needed
None of the original dependency modules or public imports is removed. No additional
DAG branches are imported. The previous sandbox-only Core attempt was discarded;
it was never part of the repository and is not counted as pruning.

## Where the brief, the DAG or earlier work was wrong
The earlier Core lemma repackaged the full standard-resolution conclusion and did
not constitute a reduction. This delivery separates module-derived sections from
Ext source-change, and proves the module half. Large implicit comparisons between
derived-functor objects made untyped intermediate isomorphisms expensive to
elaborate; explicit endpoint types and pointwise factorization avoid that route.
The mathematical statement and the unit route are unchanged. The local build
and all axiom probes passed; the initial preflight requested the compiler-option
change record. The first-reader dry-run path explicitly permits the second
reading to remain unwritten until the second reader checks this delivery.

Change record: `coord/changes/C1-standard-resolution-elaboration.md`.

## New nodes
`new-module-cohomology-standard-sections-factorization`: proved module-to-sections
factorization, including its evaluation on a cohomology class.
`new-module-cohomology-ext-sections-factorization`: the Ext-to-sections evaluation
of the defining composite. Its single named hole has a full proof in words and
its source in the docstring and node. The parent node records the actual two-part
proof and its dependencies.

## Second reading by C1

1. **Interface: pass.** Compared every delivered source with the repository. The
   only existing delivered module is ModuleCohomologyExtStandardResolutionFormula;
   its complete theorem signature is byte-for-byte identical to the original.
   Its public import and visibility are unchanged. The two new factorization
   imports are plain proof imports. Compiler options are recorded in the change
   record; no definition or target statement changes and no forced adaptation.
2. **Proof: pass, conditional on the listed open theorem.** Compiled all three
   modules in import order with lcompile.py. No errors or non-sorry warnings.
   The only delivered sorry is ext_sections_factorization, exactly `by sorry`
   in a named public theorem with a source, complete word proof and node.
   No forbidden declarations, hollow definitions or arbitrary witness choices.
   Independent scratch #print axioms checks give only propext, Classical.choice,
   Quot.sound for standard_sections_factorization and these plus sorryAx for
   ext_sections_factorization and standard_resolution_formula. The final theorem
   really performs two congruence steps and composite-inverse simplification.
3. **Split statements: pass.** Read the naturality module's definitions of the
   natural isomorphism, moduleComparisonEquiv, siteSectionsObjIso, the identity
   siteExtNatIso/siteHNatIso, and extSourceNatIso. The open lemma evaluates only
   their Ext-to-sections factors; it does not assert the original comparison
   with a supplied resolution or a/b, and is strictly a part of the argument.
   The other part is independently proved without sorryAx. Neither formula
   assumes positive degree, nonzero coefficients or nonempty schemes: identity
   and isomorphism evaluations also hold in degree zero and on zero groups.
   Independent searches used leanfinder (abelian-group natural-isomorphism map
   evaluation), loogle (NatIso.trans_app), and grep (isoWhiskerLeft_hom,
   addCommGroupIsoToAddEquiv_apply, trans_hom), plus rg of both library roots.
   They found generic evaluation tools, not a duplicate project formula.
   A bounded direct proof attempt of the open factor hit expensive definitional
   comparisons; no experimental proof or extra hole is included in delivery.
4. **Route and pruning: pass.** The reduction uses the constructed comparison
   and its fixed standard injective resolution, without change of resolution.
   Read sk-thm-p1.realized: neither new factorization bypasses a unit statement
   or step. The old proof dependency new-module-cohomology-ext-resolution-
   naturality is still used by both factors and by the existing signature;
   its module cannot be pruned. All three modules need their imports, and no
   old dependency is no longer needed. This remains a decomposition, net zero
   holes, not an unconditional closure of the theorem's import closure.
5. **DAG: pass.** Parent proof/proof_deps/proof_origin describe the two-factor
   calculation; both new nodes match their Lean statements, sources, word
   proofs, searches, creation records, blueprint origin, chapter and unit.
   Checked proof_deps equals the union of step uses in all three nodes. Existing
   node fields outside the allowed proof fields and lean record are unchanged.

Second-reading changes: restored the single space before the existing theorem's
`:= by` so its signature is literally identical; added the change record heading
and the required Users table; documented this independent review. No mathematical
statement, definition or proof was rewritten.
