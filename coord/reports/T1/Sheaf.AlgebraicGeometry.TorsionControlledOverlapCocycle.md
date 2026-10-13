## What changed

Closed `AlgebraicGeometry.torsionControlled_overlap_cocycle` without changing its
signature or public imports. Added two private-to-importers proof imports:
`Sheaf.AlgebraicGeometry.TorsionCommonOpenComparisonMap` and
`Sheaf.AlgebraicGeometry.TorsionLocalSectionSeparation`.
The parent now constructs isomorphisms from compatible maps in both directions,
proves both inverse identities, and proves the triple cocycle sectionwise.
Its DAG proof and dependencies follow this Lean assembly.

The separation module proves that the supplied b and q maps jointly separate
sections on every contained open. The proof uses the existing
`coherentMap_torsion_completion_ext_zero`, transfers its finite-level kernel
monomorphism through overEquiv, proves that the biproduct map (b,q_n) is monic,
and cancels its evaluation on sections. No completion faithfulness is assumed.

The comparison-map module isolates restriction, normalization of the formal
quotients, and lifting on a common open. The second reader added plain proof
imports for all modules of its planned dependencies (the colimit-restriction
interface is already publicly available through CoherentFormalModule). It concludes only existence of a map
respecting b and q, with no invertibility or cocycle assumption.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.torsionControlled_overlap_cocycle`
(node `new-stage3-torsion-controlled-overlap-cocycle`), 1 of 1 original holes.

New proved theorem: `AlgebraicGeometry.torsion_local_section_separation`
(node `lem-weil-pbc-torsion-local-section-separation`); it contains no sorry.

Hole added and the only sorry left in this delivery:
`AlgebraicGeometry.torsion_common_open_comparison_map`
(node `lem-weil-pbc-torsion-common-open-comparison-map`). Its proof is exactly
`:= by sorry`; its docstring and node give the restriction-and-lifting argument.
This is a decomposition, not a net hole reduction: one original hole closed,
one strictly smaller existence-of-map hole added. Inverse identities and the
cocycle are fully proved in the parent, using the separately proved separation
lemma. Existing imported Artin--Rees/lifting dependencies retain their own status.

All three modules compile together using lcompile.py. The unit sk-thm-p1's
realized statements and steps are untouched. Edge cases checked in the argument:
zero ideal (the quotient detects sections), unit ideal (the torsion kernel is
zero and b detects sections), empty opens, empty index type, and common opens
which are not affine. No definition, existing statement, or visibility changed;
no forced adaptations and no arbitrary data selected in a definition.

## No longer needed

No pre-existing import was removed: the original file only publicly imported
CoherentFormalModule, which its statement needs.

The parent no longer directly needs
`lem-weil-pbc-coherent-map-torsion-completion-ext` or its module
`Sheaf.AlgebraicGeometry.CoherentMapTorsionCompletionExt`: finite-level separation
uses the more specific already-proved
`lem-weil-pbc-coherent-map-torsion-completion-ext-zero` instead.

The other six original planned dependencies now belong to the common-open map
subargument, and are retained in that new node's proof_deps:
`lem-weil-pbc-coherent-module-local-on-open-cover`,
`lem-weil-pbc-formal-systems-pullback`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`,
`lem-weil-pbc-module-restriction-open-immersion-limits`, and
`lem-weil-pbc-torsion-controlled-completion-hom-lift-exists`.
They are not claimed globally unnecessary. No additional module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof bundled map existence, inverse identities and all
cocycle equations. Its declaration interfaces did not directly state the
normalized common-open comparison needed by the over-site conclusion. The new
map statement isolates that transfer; separation and the algebraic assembly are
proved. The six original restriction/lifting dependencies remain the plan for
that transfer, not assumptions silently used to prove the parent.

The local Stacks source file is absent on this machine. The exact source was
read at https://stacks.math.columbia.edu/tag/0889: its proof says Zariski locality
follows from uniqueness and omits verification of uniqueness. The new statements
make precisely that omitted argument's map-existence and separation parts explicit.
Mathlib searches ran through msearch.py and are recorded in searches.jsonl;
LeanSearch returned Internal Server Error and is recorded as unavailable.
The blueprint searches for torsion completion, 0889, overlap, and sections
completion found no existing node stating either new specialized interface.

## New nodes

`lem-weil-pbc-torsion-local-section-separation`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-torsion-local-section-separation.json`,
records the proved section-separation theorem in
`Sheaf.AlgebraicGeometry.TorsionLocalSectionSeparation`. It does not require delta
or any overlap map and uses only the finite-level Artin--Rees monomorphism.

`lem-weil-pbc-torsion-common-open-comparison-map`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-torsion-common-open-comparison-map.json`,
records the one remaining theorem in
`Sheaf.AlgebraicGeometry.TorsionCommonOpenComparisonMap`. Its conclusion is a map
on one common open with b and q compatibility. It makes no inverse or cocycle
claim. No change record is necessary because all existing signatures stay identical.

## Second reading by T1

1. Compared the delivered parent with the repository using diff and checked its
   theorem signature byte for byte. It is identical, including every hypothesis
   and all three conclusion clauses. Only its proof, docstring and two plain
   proof imports changed. The other two modules are new; no existing definition
   or visibility changed, and no change record or forced adaptation is needed.
   Verdict: pass.
2. Read all three proofs and compiled the set in import order through lcompile.py.
   The only textual sorry is the reported named common-open comparison theorem;
   there are no definitions or forbidden declarations in the delivery. Separate
   scratch copies printed axioms: separation uses only propext, Classical.choice
   and Quot.sound; the other two additionally use sorryAx. The parent legitimately
   retains sorryAx through the comparison lemma; separation uses the existing
   finite-level kernel monomorphism, with no completion-faithfulness assumption.
   The choices of maps are local to a theorem proof, not arbitrary witnesses in
   a definition. Verdict: pass, as a decomposition with one remaining hole.
3. Checked the common-open conclusion is only existence and compatibility of a
   morphism, and the parent genuinely proves invertibility and the cocycle from
   it and separation. The docstring explains restriction of actual kernels,
   cokernels and ideal-power bounds, normalized quotient comparisons, lifting,
   and transfer back to the over-site. On zero ideals the quotient is the source;
   on unit ideals the arrows to H are isomorphisms; empty opens have the unique
   zero-module map, and an empty index set is vacuous. No affine-intersection
   assumption is hidden. Checked Stacks Tag 0889 online, which uses uniqueness
   for Zariski locality. Independent Lean Finder searches used morphism detection
   by reductions and restriction of coherent sheaves; Loogle searched monic
   biproduct lifts; rg searched both Lean roots, and msearch grep searched
   Mathlib. The monic-biproduct lemmas require one leg monic, which is not
   assumed here. Existing GrothendieckExistenceEasyTorsionTriple is global and
   does not supply this normalized over-site interface; FormalSystemsPullback
   does not expose the projection normalization needed here. No duplicate or
   immediate proof of the remaining restriction-and-transfer argument was found.
   Verdict: pass; the split is strictly the map-existence part of the argument.
4. Checked the parent uses only the two new arguments, and separation uses the
   more specific CoherentMapTorsionCompletionExtZero. The report accounts for
   all seven old proof dependencies: six move to the map argument and the
   general completion-extensionality dependency is replaced by finite-level
   separation. No original import was removable. The unit sk-thm-p1 realized
   statements and steps do not name these nodes and remain unchanged. All
   imports added by this delivery solely for proofs are plain imports.
   Verdict: pass.
5. Checked all three node Lean statements against their declarations verbatim.
   The existing node changes only proof, proof_deps and proof_origin; its
   steps match map choice, inverse identities and triple-section comparison.
   The new nodes contain the required sources, searches, creation records,
   blueprint provenance, chapter, unit and Lean records. Their proof_deps
   equal the union of step uses. Verdict: pass after the import repair below.

Changed only the common-open module's proof imports, bringing its stated proof
dependencies into scope, and this report. Retained the working separation and
parent proofs. No additional hole was added or closed during second reading.
