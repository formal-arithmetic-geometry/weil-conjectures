## What changed
Proved `CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift_exact_source`
without changing its signature. Added three proved private helpers for augmentation vanishing,
exact-source defect factorization, and the recursive signed primitive. Reused the existing
private row factorization theorem via a proof-only `import all` of
`Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization`.
The defect and primitive arguments adapt the already proved injective-source arguments in
`HorseshoeDefectFactorization` and `HorseshoeHomotopyCorrection`. Added the proof-only import
`Mathlib.Tactic.Abel`. The second reader replaced the unused public horseshoe proof import
with the two Mathlib modules needed for the statement: Preadditive.Injective.Resolution
and ShortComplex.ShortExact. Updated the theorem docstring to describe the actual recursion.

The source degreewise rows need not split: extend each prescribed left map along the source
monomorphism into the injective target term, and use only the target splitting. The quasi-isomorphism
of the source C augmentation supplies its monicity, degree-zero exactness and positive-degree
exactness. These suffice for the recursive correction. The final chain map is constructed
explicitly by `CochainComplex.ofHom`; its augmentation and both outer squares are checked in Lean.

## Proved and sorry left
Closed the only hole: `CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift_exact_source`
(node `lem-weil-pbc-horseshoe-morphism-lift-exact-source`). No holes added; no `sorry` remains
in the delivered module. This is a full proof, not a decomposition.
Single-file compilation passes without warnings; deliver3 checks the axioms of all declarations.
Repair validation: local compilation and the rebased dry run pass. Explicitly enabling the
server compile was attempted, but its build mirror lacks
`Sheaf/CategoryTheory/Abelian/HorseshoeDefectFactorization.olean`. Thus server compilation
could not complete; the standard delivery check uses the successful local compile and
axiom probe, with the global build verifying the landing. Nothing was pushed.

## No longer needed
`lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` is no longer a proof dependency: the
specialized successive-extension argument is proved directly, so no integer-indexed augmented
complex or K-injective null-homotopy module is needed. Its general theorem remains useful elsewhere.
Removed `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift`: the exact-source proof
uses no declaration from that module. Its injective-source theorem and the proof modules
HorseshoeDegreewiseMap and HorseshoeHomotopyCorrection
are not needed on this import edge; HorseshoeDefectFactorization is now imported only
for its existing proved row-factorization helper; other importers may still reach them. The original
proof dependencies besides the null-homotopy node are all retained, and the existing
defect-factorization node is added for its reused helper: the target splitting
uses the splitting node's Mathlib match, and the remaining inputs are abelian exactness
and the defining injective extension property. No new modules or nodes are delivered.

## Where the brief, the DAG or earlier work was wrong
Repair of reviewer X-c2414: removed the duplicate private `factor_through_rows`
declaration and reused the existing theorem at both call sites. A scratch compilation
confirmed that Lean supports accessing this private theorem with `import all`; an ordinary
import would not expose it. No dependency interface or visibility changes are needed.
The earlier second reading below describes the pre-repair version and is retained as history;
the repaired file has three private helpers, not four. The delivery dry run rebases onto
the current server branch.

No false statement was found. The original Step 3 is sound, but its integer-indexed complex
construction is unnecessary below the unit level. The equivalent recursive proof uses only the
exact augmented C-row and injectivity of the A-target terms. The unit realization is untouched.

## Earlier second reading (a previous round; superseded)

1. Compared the complete delivered module with the repository file using diff and checked
   the existing theorem signature byte for byte with Python. All binders, typeclass
   assumptions, conclusions and visibility are unchanged. Four fully proved private
   helpers are the only new declarations. No definition or target statement is changed,
   and there is no forced adaptation. The public import pruning is documented in
   coord/changes/HorseshoeMorphismLiftExactSource-imports.md. Verdict: pass.
2. Independently compiled the delivered file through lcompile.py without errors or warnings.
   Inspected every helper and the main proof: degreewise injective extension and target
   splitting produce the preliminary map; exact rows factor both defects; cancelling
   epic source projections and monic target inclusions proves the signed cocycle identity;
   the degree-zero augmentation gives the starting compatibility. Positive exactness and
   injectivity then construct successive primitives by recursion on consecutive pairs.
   The explicit corrected cochain map satisfies its augmentation and both outer squares.
   No sorry, axiom, unsafe, opaque, implemented_by or extern appears. A scratch copy checks
   #print axioms for all five declarations: only propext, Classical.choice and Quot.sound.
   The choices used in the proof come from proved factorization and extension results,
   never from an unproved existence theorem. Verdict: pass.
3. There are no split-off statements, new modules, new nodes or remaining holes. Checked
   that the private helpers are actual strictly smaller parts of the argument, not renamed
   copies of the item. At degree zero monicity of the augmentation is obtained from its
   quasi-isomorphism, rather than assumed; at every successor the exact short complex is
   precisely the one used by descToInjective. Zero objects and zero endpoint maps require
   no extra hypothesis. Verdict: pass.
4. Searched the existing horseshoe modules and Mathlib under factorization, injective
   descent, augmented exactness and compatible middle lifts (also an msearch grep query).
   Mathlib provides the exactness transport, splitting and injective extension operations
   already used, but no complete compatible exact-source lift. Existing horseshoe defect
   and correction theorems require injective source resolutions, unlike this statement;
   their private helpers cannot be imported. The direct recursion is the specialized
   shortest route found. Pruned the unused horseshoe proof import and documented it under
   No longer needed. The original dependency omitted from proof_deps is fully listed there.
   Inspected dag/units/sk-prop-h2.json: realized remains unchanged, and this item's
   subordinate comparison construction bypasses no realized unit statement or step.
   Verdict: pass after import pruning.
5. Compared both node records as parsed JSON: only proof, proof_deps and proof_origin
   differ. Read the new third step against signed_primitive and the final correction;
   it accurately describes the successive-extension proof. proof_deps is the union of
   the steps' uses; the splitting node is used through its exact Mathlib match.
   The statement, statement dependencies, Lean record, chapter and unit are untouched.
   Verdict: pass.

Second reading changed only the unused import and the stale theorem proof docstring,
plus this report and the required import change record. The mathematical proof and
the first worker's node edits were retained. The dry run required the import record;
its Users section checks the sole direct importer, which imports this module privately.

## Second reading by N1

1. Compared the delivered module with the repository version. The target theorem
   signature is byte for byte unchanged; only proof code, proof-only/public imports,
   and its explanatory docstring differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The file has
   no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof
   uses only the permitted construction and existing proved helpers. Verdict: pass.
3. Checked the three private helpers: each is a strictly smaller factorization or
   recursion step, and no statement was split off. The exact-source hypotheses are
   used at degree zero and in every successor, including zero-object edge cases.
   Verdict: pass.
4. Reviewed the imports and proof route. The former horseshoe proof import and the
   null-homotopy dependency are unnecessary; the existing row-factorization helper
   is reused through a proof-only `import all`. The realized unit route is unchanged.
   Verdict: pass.
5. Compared the node JSON with the Lean proof. Only proof, proof dependencies, and
   proof origin changed, and the added dependency is exactly the reused helper.
   Verdict: pass.

Changed only the report section above; no proof or statement edits were needed in
this second reading.
