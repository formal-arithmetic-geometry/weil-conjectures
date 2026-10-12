## What changed

Filled `AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen_reverse` in
`Sheaf.AlgebraicGeometry.SectionRingProjPreimageReverse` with a complete Lean proof.
The existing signature and docstring are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` and six proved private helpers.

The power calculation uses `DirectSum.of_mul_of`: tensor products of local free generators
remain free generators, so induction proves nonvanishing of positive section-ring powers.
Choose a positive-degree chart through `f x`, specialize the fraction identity to `s^e/t^d`,
and show its pullback germ is a unit because its product with the denominator section is
nonvanishing. Reflect units along the local stalk map, use the Proj stalk equivalence and
the localization-at-prime unit criterion, then use `Proj.basicOpen_pow`.
The node copy now records these steps and the nonvanishing/generation dependency.

Local compilation passed. The import-direction check confirms the added import is acyclic.
Searches through LeanFinder, Loogle, the search wrapper's grep, and repository/Mathlib `rg`
found the generic chart/localization API but no duplicate section-ring reverse implication.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen_reverse`
(node `lem-sc-ample-proj-canonical-map-preimage-reverse`).
All six private helpers are proved. No `sorry` remains in the delivered module; no holes
were added or split off. This is a proof, not a decomposition.

The locally compiled baseline of the imported section-ring construction still depends on its ring-law holes
`sectionRing_one_mul`, `sectionRing_mul_one`, `sectionRing_mul_assoc`, and
`sectionRing_mul_comm` (node `def-sc-invertible-section-ring`). This delivery does not
change those declarations. The proof uses the existing section-ring structure as instructed.

## No longer needed

None: no imports or planned dependency modules were removed. Each original public import
is used by the statement; the sole added import is used to convert nonvanishing to local
generation. No new residue-field, fibre-comparison, or tensor-power compatibility modules
are needed: the multiplication and positive-power compatibility are proved privately here.
The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original node cited only definition
nodes for its long chart calculation. Its route is now fully implemented using existing
proved local-generator and localization APIs. The auxiliary existence hypothesis `hx` and
the positivity hypothesis `hd` are unused for this direction; they are preserved verbatim.
The proof also covers nonreduced schemes: the scalar-unit argument uses the maximal-ideal
submodule, without treating a nonzero stalk element as a unit.

## Second reading by R2

1. Compared the complete delivered module against the repository with `diff`, and
   compared the existing theorem signature byte for byte: identical. Its docstring,
   visibility, hypotheses, and conclusion are unchanged. No definitions or other
   modules changed; no change record is needed. Verdict: pass.
2. Independently compiled the delivered module (2.7 seconds, no errors or warnings).
   Compiled a scratch copy with `#print axioms` for the public theorem and all six
   private helpers. Only `propext`, `Classical.choice`, `Quot.sound`, and the existing
   imported `sorryAx` occur; the scalar-unit and fraction-numerator helpers have no
   `sorryAx`. No delivered declaration contains `sorry`, a new axiom, an unsafe
   implementation, or data selected from an unproved existence theorem. The source
   repository now has proofs of the ring laws; the compiled baseline still carries
   their old holes. Verdict: pass relative to the compiled baseline.
3. No statements were split off, no holes were added, and no new public statements
   were introduced. Read all six private helpers: the positive-power induction
   handles exponent one separately and excludes exponent zero; the multiplication
   helper allows degree zero; the scalar argument works for any module using
   maximal-ideal times module, including nilpotents; the fraction criterion permits
   exponent zero; chart existence follows from exclusion of the irrelevant ideal.
   Verdict: pass; no decomposition or restatement of the target.
4. Searched repository sections and the Mathlib Proj/localization APIs with different
   terms, plus fresh Loogle and LeanFinder searches. Existing tensor-power locus
   results use morphism representations and would require additional compatibility
   proofs; no shorter applicable section-ring result was found. All imports are
   used: the three public imports provide statement vocabulary, and the added
   nonvanishing/generation import is proof-only. Every old proof dependency remains
   used, so `No longer needed` correctly lists none. Read the unit record
   `sk-thm-curveestimate`: its realized statement `thm-sc-proper-cohomology` and
   unit route are preserved. Verdict: pass.
5. Compared both node JSON files: only `proof`, `proof_deps`, and `proof_origin`
   changed. Read the four new proof steps against the Lean; they accurately record
   multiplication/generation, chart choice, local-unit reflection, and localization.
   Checked that `proof_deps` is exactly the union of step `uses`, with all original
   dependencies retained. The Lean record still contains the unchanged signature;
   there are no new nodes to validate. Verdict: pass.

Second reading changed only this report: added the independent review and clarified
that the imported ring-law holes belong to the compiled baseline, while their current
repository sources have already been proved. No Lean repair was needed.
