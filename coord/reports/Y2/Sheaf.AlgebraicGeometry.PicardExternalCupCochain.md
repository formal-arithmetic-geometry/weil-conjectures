## What changed

Repaired both returned points in the sandbox. Changed picardExternalTotal from
noncomputable abbrev to noncomputable def, preserving its complete signature and
mapBifunctor body. This keeps the bicomplex totalization folded during type inference.
The main proof explicitly identifies the Kunneth cycle formula's right-hand side
with T.homologyπ before rewriting. Every target and existing theorem signature,
visibility and mathematical construction is preserved. Second reading removes four
redundant direct imports; see the import audit below.

Profiling identified expensive kernel conversions in the concrete Ext linear-map
construction: cupLinear_exists 29.7 s, pullbackLinear_exists 14.2 s, and
cohomologyExtLinear_exists 4.1 s. Added fully proved private helpers
linear_chain_exists, bilinear_chain_exists and extCupLinear_exists. They compose
linear maps and construct the tensor Ext pairing in abstract modules/categories,
then provide evaluation formulas for specialization to scalar sheaves. This keeps
concrete scalar actions folded. The proof still uses Mathlib's bilinearCompOfLinear
and mapExtLinearMap, with their evaluation lemmas. No separate module was introduced.

Compiled the full repaired module in 19.3 s, and its actual module artifact in
25.1 s. All seven direct importers compiled unchanged against that artifact:
PicardExternalCupAcyclic (7.6 s), PicardExternalCupLeftHomologyLadder (4.8 s),
PicardExternalCupQuasiIso (5.7 s), PicardExternalCupRightExactLadder (4.9 s),
PicardExternalCupRightShortExact (5.1 s), PicardExternalCupShiftLeft (8.1 s), and
PicardExternalCupShiftRight (10.1 s). The additional textual user
PicardKunnethCechModels compiled unchanged in 5.3 s. No forced adaptation is needed.
The return's self-importer failure is repaired in the item's own normalization proof.

Updated the existing node's proof and proof_origin; proof_deps is unchanged.
Definition-change record: coord/changes/picardExternalTotalFolded.md.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_exists
(node lem-sc-picard-external-cup-cochain).
All private helpers are fully proved. Holes closed: 1. Holes added: 0.
Sorries left in the delivered module: none. Split off: 0.
Existing imported open results remain dependencies; this is a proof from those
recorded declarations, not a claim that their sorries have been closed.

## No longer needed

Removed redundant direct imports:
Mathlib.Algebra.Category.ModuleCat.Colimits,
Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic,
Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex, and
Mathlib.Algebra.Homology.ShortComplex.ModuleCat.
The first three remain publicly available through the retained imports; the last
is available to the proof through the plain TensorKunnethNat import. This removes
no module from the target closure.

No module or DAG dependency is pruned from the target import closure. All three recorded proof
nodes remain needed: def-sc-field-linear-module-cohomology-operations,
lem-sc-picard-kunneth-resolution-model, lem-sc-qcoh-cech-total-tensor-nat-iso.
The repair adds the proof-only import
WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor to the repository baseline.
The existing public adjunction linearity theorem and Mathlib composition are used;
no duplicate inverseImage_linear or extCompose helper is introduced.

## Where the brief, the DAG or earlier work was wrong

The earlier 46–55 s local measurements did not provide enough margin for the
server's 60 s per-file check, which reported a 134 s global compile. Profiling
showed expensive concrete Ext instance conversions; proved abstract evaluation
formulas now avoid those conversions. The reducible tensor-total abbreviation
also exposed the entire bicomplex during rewrite matching. The replacement keeps
identical data folded and explicitly repairs the one local rewrite. All downstream
textual users and direct importers compile without edits, addressing the second
return without unnecessary adaptations. No mathematical statement or unit route
was wrong or changed. The definition change reopens affected target interpretation
checks under AGENTS.md §4; its identical data is checked in this reading.
Zero sheaves, empty schemes, degree zero and negative degrees
retain the original handling and require no additional assumptions.


## Second reading by Y2

1. Interface audit: read the complete repository/sandbox diff and compared the
   existing declarations with stage3_delivery's parser. The theorem
   picardExternalCupCochain_exists and the definition IsPicardExternalCupCochain
   retain byte-identical statement text; the latter also retains its exact body.
   picardExternalTotal has the identical arguments, result type and mapBifunctor
   body, with only the declared abbrev-to-def change. The change is recorded in
   coord/changes/picardExternalTotalFolded.md. No hypothesis is added or conclusion
   weakened. Verdict: pass, with the definition-change review obligation recorded.

2. Proof audit: compiled the delivered module with lcompile.py --all in 20.6 s,
   without errors or warnings. Scanned for sorry and forbidden declarations/attributes;
   none occurs in delivered Lean. A scratch copy prints axioms for the two public
   definitions, the existence theorem, lift_graded_homology and externalCup_bilinear.
   Only propext, Classical.choice, Quot.sound and existing imported sorryAx occur;
   picardExternalTotal and lift_graded_homology have no sorryAx. The graded lifting
   proof extends the source cycle projection and splits the target homology quotient;
   its components annihilate boundaries and land in cycles. Naturality and epi/mono
   cancellation give exactly the prescribed homology map. Choice of splittings is
   justified by fully proved field-linear inverse lemmas. The cup witnesses have
   pointwise evaluation formulas; the tensor Kunneth equivalence is fixed on
   generators, since cycle projections are surjective and pure tensors span.
   No public definition chooses an arbitrary witness from an unproved existence
   theorem. Verdict: pass; imported open results remain open.

3. Split-off audit: no split-off theorem, new module, new node or new sorry is
   delivered. Every private helper is proved, including abstract linear composition,
   bilinear composition and tensor Ext cup. Ext cup uses exact tensor functors and
   Mathlib bilinearCompOfLinear, with the recorded coefficient morphism. The field
   assumption is essential to the splitting step and is present. Zero complexes,
   zero coefficients and empty schemes impose no new restriction; degree zero has
   the sole (0,0) summand, and negative degrees are assigned zero in the graded map.
   A fresh Loogle search for HomologicalComplex.homologyMap and an rg search for
   graded homology lifting across Mathlib, upstream and Sheaf found no direct
   replacement for this construction. Existing Adjunction.left_adjoint_linear is
   reused rather than copied. Verdict: pass.

4. Route and import audit: read PicardKunnethResolutionModel, tensor_kunneth_nat,
   all three proof-dependency node statements, and dag/units/sk-prop-av-cube.json.
   The proof follows the recorded external-cup bilinearity, tensor Kunneth and
   vector-space lifting route; no unit step is bypassed or changed. All three old
   proof_deps are still used, so none belongs in the no-longer-needed node list.
   Removed direct public imports of ModuleCat.Colimits, ModuleCat.Monoidal.Basic
   and ShortComplex.HomologicalComplex: their public closure is already provided
   by PicardKunnethResolutionModel/Coherent. Removed ShortComplex.ModuleCat, whose
   proof-only availability is supplied by the existing plain TensorKunnethNat
   import; no declaration in this file's public statement or definition requires
   that module's additional declarations. Both remaining proof-only imports are
   plain imports. All seven direct importers plus PicardKunnethCechModels compiled
   from unchanged current repository sources against the revised sandbox artifact
   (4.5–10.3 s each), so no forced adaptations are necessary. Verdict: pass.

5. DAG audit: JSON comparison shows only proof and proof_origin changed; proof_deps,
   statement, stmt_deps and lean statement record are unchanged. The proof steps
   accurately describe the abstract Ext operations, DirectSum.toModule of the
   degree-cast tensor pairing, graded lifting and normalization via monicity of
   iCycles. No new-node fields are needed. The existing unit realized record is
   unchanged. Verdict: pass.

Second reading changed only import cleanup and reporting: removed four redundant
imports, corrected the baseline import/pruning account, and recorded the required
reopening of affected target interpretation checks for the definition change.
The proved Lean argument was retained. One original hole closed, zero added,
zero split off; no module pruned from the target closure.
