## What changed

The module `Sheaf.RingTheory.ProjectiveResolutionExtDegree` contains the complete proof of
`ModuleCat.projective_resolution_ext_degree`. The forward implication uses
`ProjectiveResolution.extMk_surjective`, the support bound, and
`HasProjectiveDimensionLT.mk`; the reverse implication inducts on the bound and uses
`hasProjectiveResolutionLE_of_shortExact_projective_middle` on the kernel short exact
sequence of `Projective.π`. No declarations or imports were changed.

## Proved and sorry left

`ModuleCat.projective_resolution_ext_degree` is proved. No `sorry` remains in the
item or is added by this delivery.

## No longer needed

None. All existing imports are used by the proof or by its public statement, and the
DAG proof dependencies remain applicable.

## Where the brief, the DAG or earlier work was wrong

None found. The checked-in module already had the intended complete proof, which
compiles in the D3 sandbox.

## Earlier second reading (a previous round; superseded)

The theorem statement is unchanged and the complete proof compiles. No new nodes or
statement changes require review.

## Second reading by D3

1. **Signatures and visibility.** Compared the delivered module with the repository
   version. The theorem signature and all existing declarations are byte-for-byte
   unchanged; the only difference is the proof-local spelling `let _ :=`.
   No target statement, definition, or public interface changed. Verdict: pass.
2. **Compilation and axioms.** Compiled the delivered module with `lcompile.py` and
   checked a scratch import with `#print axioms ModuleCat.projective_resolution_ext_degree`.
   Compilation succeeds, and the declaration depends only on `propext`,
   `Classical.choice`, and `Quot.sound`. The module has no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by`, and no hollow definitions. Verdict: pass.
3. **Statements and proof route.** The forward direction uses the support bound,
   `ProjectiveResolution.extMk_surjective`, and `HasProjectiveDimensionLT.mk`; the
   reverse direction uses the zero case and the kernel short exact sequence with the
   existing successor-splicing theorem. These steps prove exactly the unchanged
   module-specific equivalence. No statements were split off or added, and no
   duplicate declaration was introduced. Verdict: pass.
4. **Pruning and unit route.** Both public imports are required by the theorem's
   statement. The proof-only imports provide `HasExt.standard`, Ext representatives,
   and the successor splice used in the body. No import or DAG dependency can be
   removed safely, and the unit's projective-resolution route is retained. Verdict:
   pass.
5. **DAG agreement.** The node's declaration, statement, proof steps, proof
   dependencies, and proof origin agree with the delivered Lean proof. The unit and
   chapter metadata are unchanged; no new nodes or change records are needed.
   Verdict: pass.

I changed only this report section during second reading; no Lean declaration or DAG
statement required repair.
