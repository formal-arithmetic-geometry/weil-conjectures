## What changed

The target module now proves `AlgebraicGeometry.Scheme.trace_discriminant_zeroLocus_iff_nonEtale_fibre`
with its signature unchanged. It converts zero-locus membership to zero residue-field evaluation,
then combines a discriminant/fibre criterion with a fibre/neighbourhood criterion and proves both
logical implications. Two proof-only imports provide these criteria.

Added `Sheaf.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods`. Its theorem
`AlgebraicGeometry.Scheme.etale_fibre_iff_forall_etale_neighbourhood` is proved: the forward
implication uses upstream `fiberι_mem_smoothLocus`, the relative-dimension-zero local dimension
formula, and the existing proved `exists_etale_open_of_smooth_of_fibre_dimension_zero`. The reverse
implication pastes restriction pullback squares and checks etaleness on an open cover of the fibre.
The existing neighbourhood theorem is a generic tool from the proper-base-change unit; its use
does not replace the spreading unit route. The spreading unit's realized lists are empty, and its
statements and steps are unchanged.

Added `Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantEvaluationEtaleFibre`, containing the
remaining algebraic fibre argument as a named theorem. It requires only an affine morphism and
a finite section basis; no flatness or Noetherian hypothesis. Both new nodes record actual search
results (LeanSearch returned HTTP 500, recorded as unavailable). Searches of Mathlib, both library
roots, DAG nodes and blueprint references found pieces but no direct criterion.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.trace_discriminant_zeroLocus_iff_nonEtale_fibre`
(node `lem-sbc-trace-discriminant-fibre-etale-criterion`).

Proved the new
`AlgebraicGeometry.Scheme.etale_fibre_iff_forall_etale_neighbourhood`
(node `lem-sbc-flat-fibre-etale-neighbourhoods`) without adding a hole for the geometric
fibre/neighbourhood argument.

Added one remaining hole:
`AlgebraicGeometry.Scheme.trace_discriminant_evaluation_ne_zero_iff_etale_fibre`
(node `lem-sbc-trace-discriminant-evaluation-etale-fibre`). This is a decomposition, not an
unconditional proof or a net hole reduction: one original hole closed and one strictly smaller
algebraic hole added. There is no sorry in the original module or the neighbourhood module.

All three modules compile together without warnings through lcompile.py. Edge cases checked
against the statements and source argument: zero rank gives the empty fibre and determinant one;
a nonreduced finite fibre has degenerate trace form; finite inseparable field factors have
degenerate trace form; a product of separable factors has nondegenerate pairing. The neighbourhood
criterion handles the empty fibre by source locality on the empty cover. No excluded characteristic,
extra nonempty assumption, arbitrary choice of algebra data, or changed original signature.

## No longer needed

None. The original module had no proof imports or stated proof dependencies to prune. All four
original public imports are retained for its statement. The two new proof imports are used.
The evaluation helper uses its three public imports for its statement; the neighbourhood helper
uses its two public imports and all three proof imports. No node or module of the old route has
been bypassed. The differential-module/Nakayama alternative in the original informal proof is
unneeded for the neighbourhood implication: existing smoothness and zero-dimension results suffice.

## Where the brief, the DAG or earlier work was wrong

The item's DAG proof bundled trace base change, the field-algebra criterion, and local geometric
lifting into one step with no proof dependencies. It now records the actual two intermediate
criteria and the proved evaluation/negation glue.

Tag 0BVH is the section containing the source lemma; the lemma's own tag is 0BJF
(`discriminant-lemma-discriminant`). Tag 02GM's label is `lemma-etale-flat-etale-fibres`.
The new files cite these precise sources. The existing target docstring is preserved.

## New nodes

`lem-sbc-trace-discriminant-evaluation-etale-fibre`: the algebraic part, identifying the evaluated
trace determinant with the determinant of the fibre trace pairing and characterizing finite etale
field algebras. Its module has the only newly added sorry and a full natural-language argument.

`lem-sbc-flat-fibre-etale-neighbourhoods`: the geometric lifting/base-change part, proved from
existing smooth-fibre and zero-dimensional smooth-neighbourhood results and source locality.
No change record is needed: existing signatures, definitions, and public imports are unchanged.

## Second reading by U2

1. Interface preservation: passed. Diffed the existing module against the repository. Its
   declaration signature and docstrings are byte for byte unchanged; only two plain proof
   imports and the proof body were added. The other two modules are new. Diffed the existing
   node: only proof, proof_deps and proof_origin changed. No definition or statement change,
   and no change record is required.
2. Proof and trust: passed. Recompiled all three files in import order with lcompile.py,
   without errors or warnings. Independently compiled scratch copies with #print axioms for
   all three declarations. The neighbourhood theorem uses only propext, Classical.choice
   and Quot.sound. The evaluation helper and original theorem additionally use sorryAx,
   accounted for by the single named algebraic helper. The delivered sources contain no
   forbidden declarations or attributes, no definitions and exactly one sorry. In particular
   there is no data chosen from an unproved mere existence statement. Read both implications
   of the original proof and the geometric helper's smooth-locus, dimension and pullback-cover
   arguments; they prove precisely their stated conclusions.
3. Split statements: passed. The algebraic helper is strictly the trace/base-change and
   finite field-algebra part, while the geometric neighbourhood equivalence is actually
   proved. This is a genuine reduction rather than a renamed original statement. Verified
   the algebraic argument against Stacks https://stacks.math.columbia.edu/tag/0BJF and the
   geometric input against https://stacks.math.columbia.edu/tag/02GM. The sole remaining
   hole has a source, a complete docstring argument and its node. Checked zero rank/empty
   fibre (determinant one), dual numbers (nilpotents annihilate the trace pairing), finite
   purely inseparable extensions (degenerate trace), and products of separable extensions
   (orthogonal nondegenerate summands), without characteristic restrictions. Independently
   ran msearch leanfinder with “trace pairing nondegenerate separable finite algebra residue
   field discriminant base change”, loogle with “Algebra.traceForm”, and grep with
   “traceForm.*[Nn]ondegenerate|discr.*[Bb]ase[Cc]hange|[Ee]tale.*[Ff]iber|[Ff]iber.*[Ee]tale”.
   Also searched both repository library roots. Found traceForm_nondegenerate_tfae and
   det_traceForm_ne_zero for fields and the proved upstream
   Algebra.Etale.exists_trace_mul_ne_zero for finite etale algebras. These supply pieces,
   not the affine fibre identification, base-change determinant and converse required by
   the remaining helper; no direct duplicate or quick complete proof was found.
4. Route and pruning: passed. The original node has no old proof_deps and its original
   module has no proof imports to prune. Each delivered import supplies statement vocabulary
   or declarations used in its proof. Read dag/units/sk-prop-input-spreading.json: its
   statement, steps and realized fields are preserved. The already proved
   exists_etale_open_of_smooth_of_fibre_dimension_zero is a generic local tool, not a
   replacement for a spreading step. No formerly required node is bypassed. The correct
   accounting remains one original hole closed, one smaller algebraic hole added: net zero
   and a decomposition, with an independently axiom-clean geometric theorem.
5. Nodes: passed. Checked the new nodes' self-contained statements, statement dependencies,
   sources, search records, creation provenance, blueprint ancestry, chapter/unit and Lean
   records against the files. The original proof steps and proof_deps name precisely the
   two helpers used. The geometric node records the upstream pointwise smooth-fibre and
   local-dimension declarations in its proof, plus the Sheaf neighbourhood node and etale
   locality/base-change input; the algebraic node records the remaining sourced argument.

Second reading changed only this report, adding the independent checks and their results.
No mathematical, proof, import or node repair was needed.
