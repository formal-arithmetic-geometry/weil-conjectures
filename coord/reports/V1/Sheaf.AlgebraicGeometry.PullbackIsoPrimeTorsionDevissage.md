## What changed
Repair B9 corrects only blueprint provenance in both new node files: the nearest
blueprint ancestor is `prop-weil-pbc-p1-strict-henselian-comparison`, with
`lem-weil-pbc-pullback-iso-prime-torsion-devissage` in `via`. The places now name
step 3 of that ancestor's split and the respective bounded-torsion and filtered-colimit
reductions. Both `same_as` fields are searched empty lists. Lean files are unchanged
by this repair.

The target module adds two plain proof imports and replaces its sole sorry with the
composition of bounded-torsion dévissage and the filtered-colimit passage. Its signature,
docstring, public imports, and definitions are unchanged. New modules state the two strict
intermediate results. The second reader proved the bounded-torsion result from the existing
prime-factor induction, the stated pullback long exact ladder, and Mathlib's five/four lemmas.
The colimit module imports only TorsionEtaleSheaf and TopologicalInvariance, which its
statement needs; it does not import the bounded-torsion theorem.

## Proved and sorry left
- `AlgebraicGeometry.Etale.pullback_cohomology_bijective_of_prime_torsion_devissage`:
  proof body complete, by composition of the two reductions.
- `AlgebraicGeometry.Etale.pullback_cohomology_bijective_of_nsmul`:
  proof body complete, using `ObjectProperty.prop_of_nsmul_id_eq_zero`,
  `pullbackCohomology_longExact_ladder`, and Mathlib's five/four lemmas.
- The only sorry in this delivery is
  `AlgebraicGeometry.Etale.pullback_cohomology_bijective_of_torsion_colimit`, node
  `lem-weil-pbc-pullback-iso-torsion-colimit`. Its whole proof is `by sorry`.
Both completed proof bodies still depend on open statements; they are not axiom-free
completed targets. In particular the bounded-torsion proof uses the existing sorried ladder.

## No longer needed
No imports were removed from the repository's target module. The unnecessary public import
of PullbackIsoNsmulDevissage in the new colimit module was removed, replacing it with the
TopologicalInvariance module needed by the colimit statement. No old node or module is
claimed pruned. The target's old direct proof dependencies are retained transitively through
the two intermediate nodes or through its statement conventions:
- `lem-weil-pbc-cohomology-pullback-functorial`
- `def-weil-pbc-torsion-etale-sheaf`
- `def-pur-abelian-sheaf-kernel`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-prime-factor-devissage`
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
- `lem-weil-pbc-five-lemma`
- `lem-weil-pbc-cohomology-filtered-colimit`
- `lem-weil-pbc-inverse-image-preserves-colimits`
- `def-weil-directed-colimit-abelian-groups`
- `def-weil-pbc-scheme-conventions`

The bounded-torsion node retains prime-factor dévissage, the pullback ladder, and the five
lemma. The colimit node retains torsion, kernels, colimits, filtered cohomology, inverse-image
colimits, and naturality; it also names the existing Ext-to-derived comparison needed to
apply the cohomology-colimit theorem to the `Sheaf.H` encoding.

## Where the brief, the DAG or earlier work was wrong
The first worker's two reductions are mathematically strict parts of the argument, not
restatements of the item. However, their nodes incorrectly marked the substantial proofs
as elementary and dependency-free, their docstrings did not contain complete proofs, and
the report overstated pruning. The library already proves the prime-factor induction, so
it must be reused rather than left as part of a new unresolved theorem. All these faults
were repaired. The source `.tex` is absent on this machine; the reader checked the official
[Stacks 0A4B](https://stacks.math.columbia.edu/tag/0A4B) and
[Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ) pages. The reductions transpose the
source argument to global cohomology; the colimit result uses its fixed-scheme specialization.


Repair B9: the previous provenance incorrectly used the immediate created item as a
blueprint ancestor, omitted that item from `via`, and left `same_as` unsearched.
The read-only command
`python3 tools/blueprint_refs.py ancestor lem-weil-pbc-pullback-iso-prime-torsion-devissage`
confirmed `prop-weil-pbc-p1-strict-henselian-comparison`. Its current split step 3
explicitly applies prime-torsion devissage, confirming both requested source places.

Blueprint equivalence searches for B9 covered all 2,321 imported blueprint nodes across
all 16 chapters, including nodes outside the targets' reach. The raw
`literature/blueprint/` directory is absent here; the search used the imported statements
in `dag/nodes/`, as prescribed by `stages/1-dag.md`. Ran
`python3 tools/blueprint_refs.py search` with `prime induction` (1 hit),
`torsion colimit` (14), `pullback torsion` (33), `cohomology annihilated` (4),
and `devissage` (7), also broad searches for `torsion`, `colimit`, `prime`, and
`annihilated`. A Python scan of every blueprint node's full statement and title
cross-checked prime induction/devissage, torsion colimits/filtered unions, and
torsion pullback comparisons. Read the full statements of the closest candidates:
`lemma-weil-pbc-prime-factor-induction`, `lem-weil-pbc-prime-factor-devissage`,
`lemma-weil-pbc-prime-torsion-devissage`, `lemma-weil-pbc-torsion-filtered-union`,
`lem-weil-pbc-cohomology-filtered-colimit`, and the strictly henselian ancestor.
The prime-factor results give abstract extension induction or kernel/image sequences;
they do not state extension closure of pullback cohomology or its bounded-torsion result.
The filtered-union and cohomology-colimit results provide separate ingredients; neither
states the passage from bounded-torsion pullback bijectivity to torsion pullback bijectivity.
The ancestor is a comparison for one particular closed fibre, whereas these reductions
are conditional statements for an arbitrary morphism of qcqs schemes. No equivalent
blueprint statement was found for either new node, so both now have `same_as: []`.

## New nodes
`lem-weil-pbc-pullback-iso-nsmul-devissage` records the positive-integer-annihilated case,
now with a complete Lean proof relative to the existing ladder. Its plan names the exact
library induction and Mathlib diagram argument used.

`lem-weil-pbc-pullback-iso-torsion-colimit` records only the filtered-colimit passage from
uniformly annihilated sheaves to torsion sheaves. It has a complete natural-language proof,
precise source references, statement dependencies, and non-elementary proof dependencies.
No change records are needed: no existing signature, definition, or public import changed.

## Earlier second reading (a previous round; superseded)
1. **Interfaces:** diffed the target against the repository. Its existing declaration
   signature is byte for byte unchanged; the only differences are two plain proof imports
   and the proof body. Both other modules are new. No definition or target statement changed.
2. **Proof integrity:** compiled all three modules locally in import order. Checked the
   named declarations with `#print axioms` in a scratch copy; only standard axioms and
   `sorryAx` from the explicitly reported open results occur. No axiom/unsafe/opaque/extern/
   implemented_by declaration or hollow definition occurs. Exactly one new named theorem
   has a whole-proof sorry.
3. **New statements:** checked n=1 (identity zero gives the prime-2 hypothesis), n prime,
   composite n (kernel/image induction), F=0, and q=0 (initial injection and four lemma).
   PositiveNat is nonempty and filtered by products. Both statements are true strict stages
   of the source proof and neither repeats the target. Independent leanfinder, loogle, and
   rg searches found the existing induction and five lemma, which the new proof reuses;
   no duplicate result was found. The colimit theorem retains its source and full proof.
4. **Route and pruning:** read `dag/units/sk-thm-p1.json` and its realized steps. These
   reductions occur below the strictly henselian comparison step and do not bypass any
   realized unit node. Imports are minimal for the written proofs and statements. All old
   proof dependencies are accounted for above; no infrastructure is claimed globally pruned.
5. **DAG agreement:** checked Lean names and exact signatures against all three node records.
   The target plan composes the two reductions. The bounded-torsion node names the ladder,
   five lemma, and proved induction; the colimit node names the required existing
   infrastructure. Repaired source places, blueprint provenance, statement dependencies,
   proof origins, dependency unions, elementary flags, and independent search evidence.

Changes made by this second reading: proved the bounded-torsion intermediate, expanded
both new docstrings, removed the unused public proof import, corrected both new nodes and
the target's elementary flags, and rewrote the report to describe the remaining axiom
obligations and the absence of pruning accurately.


## Second reading by V1

This is an independent reading of the B9-repaired delivery, including the earlier
reader's bounded-torsion proof. Verdict: passes, with one new open colimit theorem.

1. **Interfaces:** diffed the delivered target module against the repository version.
   Its complete existing signature and docstring are byte for byte unchanged. The diff
   consists only of two plain proof imports and the replacement proof. The other two
   modules are new; no existing definition, target, or public import changed. No matching
   open change record names this module or its declaration.
2. **Proof integrity:** compiled all three files with lcompile.py --all, in import order,
   without errors or warnings. Independently ran #print axioms on all three declarations
   in a temporary scratch copy, removed before delivery. Each reports exactly propext,
   Classical.choice, Quot.sound and sorryAx. The bounded result uses the reported open
   long-exact ladder; the composite additionally uses the one new open colimit result.
   Inspected every proof: no forbidden declaration, hollow definition, or embedded sorry.
   The sole new sorry is the entire public theorem of the torsion-colimit node.
3. **Split statements:** checked the n=1 and prime/composite cases of the bounded
   argument, its degree-zero injection and four-lemma arguments, and the positive-degree
   five-term ladder. Checked the zero sheaf, degree zero, and the nonempty directed
   divisibility index (1 is an object; nm bounds n and m) for the colimit argument.
   The source [Stacks 0A4B](https://stacks.math.columbia.edu/tag/0A4B) supplies both
   reductions; [Stacks 03Q5](https://stacks.math.columbia.edu/tag/03Q5) supplies filtered
   cohomology on the fixed qcqs schemes. Both intermediates are true strict parts of the
   proof, not renamed copies of the target. Independent msearch leanfinder query about
   natural cohomology comparisons on bounded exponent objects and filtered unions found
   only derived-category ingredients. Loogle query `CategoryTheory.Limits.IsColimit,
   "iso"` found IsColimit.coconePointsIsoOfNatIso and standard colimit transport facts,
   not either intermediate. An initial NatIso identifier query was invalid and was
   replaced by this valid query. Independent rg searches for cohomology with torsion,
   nsmul and colimits found the proved prime induction and H_map_isColimit_of_isFiltered,
   which is an ingredient, not a duplicate. Read that theorem's proof and the existing
   Ext-to-derived and filtered-cohomology statements. Closing the colimit intermediate
   still requires constructing the torsion cocone and its natural cohomology comparison;
   it is correctly left as the named sourced obligation rather than a partial proof.
4. **Route and pruning:** checked sk-thm-p1.json and its realized statement and all four
   step lists. These reductions sit below its strictly henselian comparison and bypass
   no realized unit node. All new proof-only imports are plain imports. The public imports
   provide the statement notation and torsion predicate. All eleven old direct proof
   dependencies are replaced directly by the two intermediate nodes, and remain needed
   transitively in their plans or as statement conventions, as enumerated above under
   No longer needed. No node or module can be claimed globally pruned by this delivery.
5. **DAG agreement:** checked all three recorded Lean signatures against whitespace-
   normalized source signatures and each proof_deps against the exact union of step uses.
   The target composes the two reductions; the bounded proof uses the ladder, Mathlib
   five/four lemmas, and the existing prime induction. The colimit plan names its actual
   pending infrastructure, including the Ext-to-derived comparison. The new nodes have
   source, origin, searches, creation and Lean records, matching chapter/unit, and the
   repaired nearest blueprint ancestor with the item in via and searched same_as: [].
   The new theorem docstrings give complete natural-language arguments.

Changes in this reading: appended this review and independent search/axiom evidence.
No Lean proof or node repair was needed after B9; the earlier repaired proof is retained.
