## What changed

Proved `Algebra.exists_flat_regular_fibre_parameter_selection` in
`Sheaf.RingTheory.FlatRegularFibreParameterSelection` without changing its statement,
universes, visibility, or existing docstring. A proved private helper
`Algebra.parameters_from_generators` selects an inclusion-minimal subset of the given
finite set of generator values. The existing proved characterization
`IsRegularLocalRing.minimal_generators_iff_card_eq_dimension` makes its enumeration a
regular system of parameters. The existing regular-sequence theorem supplies its
regularity. The main proof also proves the ideal equality by mapping to the quotient
and pulling the equality back, using `Ideal.comap_map_quotientMk`.

Added `Sheaf.RingTheory.FlatPolynomialAppendOfFibreRegularSequence`, with the proved
`Algebra.flat_polynomial_append_of_fibre_regular_sequence`. Its proof constructs the
canonical local maps from first-variable renaming, proves their composition using the
localization universal property, sets up the scalar tower, and applies the existing
`Module.flat_and_flat_of_flat_fibre_noetherian` with the finite target module equal to
its ring. This is a complete Lean application of Tag 00MP.

Added `Sheaf.RingTheory.FlatPolynomialAppendTensorFibre`, stating the remaining
closed-fibre flatness step separately. Its hypothesis is regularity of the specified
coordinate sequence on the original fibre; it has no initial-flatness hypothesis,
no choice of subset, no generator-span hypothesis, no regular-local fibre hypothesis,
and no ideal-equality conclusion. Its conclusion is flatness over the source closed
fibre, not flatness of the appended localization map. Its docstring and node give the
polynomial-origin comparison, the application of Tag 07DY, and the tensor-quotient
comparison. Thus this is strictly part of the argument, not the original theorem
under another name.

The three modules compile together through `lcompile.py --all`, without warnings.
The original node's proof and dependencies were updated to follow the Lean argument.
Source passages read: Stacks smoothing.tex, lemma-solution-modulo (07FH), and
algebra.tex, lemma-flat-over-regular (07DY) and
lemma-criterion-flatness-fibre-Noetherian (00MP). Copies obtained for reading are
in the sandbox scratchpad; they are not delivery files.

## Proved and sorry left

Original holes closed: one, `Algebra.exists_flat_regular_fibre_parameter_selection`
(node `lem-weil-pbc-flat-regular-fibre-parameter-selection`).

New proved declaration: `Algebra.flat_polynomial_append_of_fibre_regular_sequence`
(node `lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence`). The private
`Algebra.parameters_from_generators` is also completely proved.

The item's module has no remaining sorry. One new sorry is left:
`Algebra.flat_tensor_fibre_polynomial_append_of_regular_sequence`
(node `lem-weil-pbc-flat-polynomial-append-tensor-fibre`), in its own new module.
Its entire body is `by sorry`; its source and complete natural-language proof are
in both its docstring and node. This delivery is a decomposition: one original
hole closed, one strictly smaller hole added, net zero, not a claim of an
axiom-free proof of the original result.

Edge cases checked mathematically against the new statement and the actual selection:
for `e = 0`, the source closed fibre is the residue field of the first polynomial
localization, so its tensor fibre is flat over a field. For `t = 0`, the first
base is the field k and the source closed fibre is the polynomial-origin localization
on the appended variables. The regular-sequence hypothesis gives flatness by 07DY.
For `r = 0`, the original span hypothesis makes the localized maximal ideal zero;
the finite minimal subset and its enumeration are empty. For a field closed fibre,
the minimal subset is likewise empty. Repeated input generators do not create repeated
parameters: the helper minimizes a finite set of their values and selects one input
preimage per enumerated value. A zero appended coordinate cannot satisfy regularity
on a nonzero fibre, so it supplies no spurious flatness case. No data definition is
chosen from a sorried existence theorem; there are no new definitions.

## No longer needed

Removed the item's direct proof imports:
`Sheaf.RingTheory.PolynomialOriginRegularLocal`,
`Sheaf.RingTheory.FlatOverRegular`, and
`Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`.
The criterion is now imported and actually applied in the proved append module.
The origin and flat-over-regular declarations remain necessary for the proof plan
of the unfinished tensor-fibre node, so they are not claimed as mathematically pruned.
Its module retains the two proof-plan imports for the polynomial-origin theorem
and the flat-over-regular theorem, in addition to its statement imports.

The parent node no longer directly uses
`lem-weil-pbc-nakayama-local-generators`: the already proved minimal-generator
characterization encapsulates that argument.
It also no longer directly uses `lem-weil-pbc-finite-type-algebra-noetherian`,
`lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-polynomial-ring-origin-regular-local`,
`lem-weil-pbc-flat-over-regular`, and
`lem-weil-pbc-criterion-flatness-fibre-noetherian`; these occur in the new nodes
where needed. Removed the redundant direct Mathlib polynomial Rename import from
the proved append module after recompiling without it.

No dependency module is certified globally unreached or no longer mathematically
necessary by this delivery; pruning: none. The unit's statement and all realized
steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The initial imports did not directly provide the
polynomial closed-fibre comparison or its tensor formulation. The source's assertion
that the additional parameters give property (1) leaves these identifications
implicit. The new tensor-fibre node records that missing bridge explicitly.

The shortcut is to choose an inclusion-minimal finite subset and apply the already
proved minimal-generator characterization, rather than reproduce the cotangent-basis
and Nakayama proof in the parent module. All changes are below the unit level.
No interface was changed and no forced adaptation was needed.

## New nodes

`lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence` records the proved
localization/scalar-tower and Noetherian fibre-criterion step. Its new module is
`lean/Sheaf/RingTheory/FlatPolynomialAppendOfFibreRegularSequence.lean`.

`lem-weil-pbc-flat-polynomial-append-tensor-fibre` records the remaining strictly
smaller closed-fibre comparison and flatness step. Its new module is
`lean/Sheaf/RingTheory/FlatPolynomialAppendTensorFibre.lean`.

Both inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`, have complete
proof steps, source references, statements, matching Lean records, and recorded
real searches (LeanSearch unavailable; LeanFinder and source grep found no exact
match). There are no change records because no existing interface changed.


## Second reading by J2

1. **Existing interfaces: PASS.** Compared the delivered item with the repository
   using `diff -u`. The original declaration signature, universe variables, public
   imports, visibility and docstring are byte for byte unchanged. Changes are the
   completed proof, proved private helper, and private proof imports. The other two
   delivered modules are new. No definition or existing statement changed, so no
   change record or forced adaptation is required.

2. **Proofs and axioms: PASS as a decomposition.** Read all three modules, including
   minimal-subset extraction, enumeration/preimage choice, quotient ideal pullback,
   localization composition and scalar-tower construction, and the exact application
   of the Noetherian fibre criterion. Compiled all three together without warnings.
   Scratch copies with `#print axioms` show only `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx` for the three public declarations. The sole literal
   hole is the named tensor-fibre theorem reported above. There is no axiom, unsafe,
   opaque, extern, implemented_by, holed definition, or data chosen from an
   unproved existence theorem. The selected indices are chosen from a proved
   finite-preimage statement.

3. **New statements: PASS.** The remaining tensor-fibre statement is strictly a part
   of the original argument: it contains neither selection nor ideal generation
   nor initial flatness, and concerns only the closed fibre. Verified the origin
   identification by the stronger equality p₁=p₀P₁+(Y_i), obtained by evaluating
   modulo q; the quotient-tensor comparison identifies the target with L/p₀L.
   The Noetherian local regular-source criterion applies to precisely the given
   regular sequence. Checked e=0, t=0, a field fibre, r=0 in the parent selection,
   duplicate generators, and an attempted zero coordinate in a nonzero fibre.
   Fresh searches used a residue-fibre/localized-indeterminate formulation, Loogle
   for `TensorProduct.quotTensorEquivQuotSMul`, and source grep for residue-field
   polynomial and regular/flat results. Inspected the quotient-tensor equivalence,
   polynomial fibre spectrum results, and upstream/project declarations: they
   provide ingredients, not the full statement. Closing the remaining bridge needs
   substantial localization/quotient equivalences, not a short overlooked lemma.

4. **Route and pruning: PASS after repair.** Minimal generators reuse the proved
   library characterization instead of reproducing Nakayama. The append module
   performs the actual localization/scalar-tower and fibre-criterion reduction.
   All omitted old direct dependencies are listed under No longer needed. Restored
   PolynomialOriginRegularLocal and FlatOverRegular as private proof-plan imports
   of the unfinished module, so their necessary argument stays in the import
   closure. Read sk-thm-p1's realized statement and steps: these are unchanged;
   all reductions are below the unit level. No module is claimed pruned.

5. **DAG/Lean agreement: PASS after repair.** Checked all three nodes, their step
   uses/proof_deps unions, source, provenance, chapter/unit, creation and Lean
   records. Parent steps match finite minimal selection, regularity, append-flatness
   and quotient pullback. The new proved node matches the localization composition
   and fibre-criterion application; the remaining node describes the unformalized
   closed-fibre comparison. Replaced flattened new-node Lean signatures with the
   verbatim multiline signatures from their modules.

Second-reading changes: restored the two private proof-plan imports in the
unfinished tensor-fibre module; made its docstring and node explicitly prove the
contracted-prime equality before the origin localization; corrected both new-node
Lean signature records; updated this report. No proof or statement needed repair,
and no additional hole was closed or added by this reading. The result remains
one original hole closed and one strictly smaller hole added (net zero).
