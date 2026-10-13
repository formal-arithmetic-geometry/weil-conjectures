## What changed

Proved `FormalGlueing.canonical_functor_maps` in
`Sheaf.RingTheory.FormalGlueingCanonicalFunctorMaps`, preserving its signature and visibility.
Private proved helpers establish the restricted-chart module equality, naturality of comparison
and swap, equality transport of linear maps, and componentwise equality of glueing morphisms.
The construction explicitly transports the tensor and localization maps, proves their two
compatibility equations, and verifies identity, composition, and the prescribed components.
Added a module docstring and updated the declaration proof description and node proof steps.
Both existing imports are used; no imports, public definitions, or statements changed.

## Proved and sorry left

Closed one hole: `FormalGlueing.canonical_functor_maps`
(node `lem-weil-pbc-formal-glueing-canonical-functor-maps`).
No holes remain in this module, and no holes or modules were added.
This is a proof, not a decomposition. All private helpers are proved.
Single-file compilation succeeded without warnings. The delivery dry run checks all
local declarations for forbidden axioms.

## No longer needed

None. Both `Sheaf.RingTheory.FormalGlueingData` and
`Sheaf.Paper.FormalGlueingCanonicalMaps` are needed. The node keeps both proof dependencies.
No nodes or modules are pruned. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The local Stacks TeX files named by the node
are absent on this machine; read the primary sources online:
[Remark 05EL](https://stacks.math.columbia.edu/tag/05EL) and
[Lemma 07K0](https://stacks.math.columbia.edu/tag/07K0). Prime naturality can be proved more directly by
localization extensionality and the defining denominator-one comparison equation, instead of
calculating the comparison on every fraction. The node and docstring now describe that proof.
Edge cases need no exclusions: fraction induction works for zero generators and zero modules;
the chart quantifiers also cover the empty family. Unequal ring universes are retained.

Searches: LeanFinder for localization/tensor comparison naturality returned general localization
and tensor tools, not this glueing construction; Loogle found `IsLocalizedModule.map_comp`;
grep found base-change and localization formulas, and a private proved swap naturality helper
in `Sheaf.RingTheory.FormalGlueingReplacePrime`. The present proof uses the same double-fraction
argument locally, avoiding an import of that unrelated theorem module.


## Second reading by S3

1. Compared the delivered module with the repository version. The public theorem signature and visibility are byte-for-byte unchanged; only the proof, private helpers, and documentation differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the construction has no hollow definitions. Verdict: pass.
3. Checked the canonical morphism statement against the existing FormalGlueing data and canonical-map declarations, including empty chart families and zero localizations. No hypothesis was added and no conclusion weakened; no new split-off statement was introduced. Verdict: pass.
4. Checked the proof route and imports. It uses the declared canonical-map and data dependencies, with explicit localization and tensor naturality; both imports are needed and no old proof dependency is bypassed. Verdict: pass.
5. Checked the DAG node and unit route against the Lean proof. The node proof steps and dependencies agree with the implementation, and the unit remains realized by this node. Verdict: pass.

Changed only the report by adding this second-reading record; no Lean declarations, statements, definitions, imports, or DAG nodes were changed.
