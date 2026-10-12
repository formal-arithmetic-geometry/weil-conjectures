## What changed

Replaced the entire proof of `AlgebraicGeometry.directedEtaleLimitSections` without
changing its signature or docstring. The proof follows the existing route: apply
`etaleSetSectionContinuity` at a chosen stage and its terminal étale object, identify
the section diagram and cocone, and transport the colimit along the final upper-tail
inclusion. The proof explicitly transfers qcqs and affine-transition instances,
constructs and proves naturality of the diagram isomorphism, proves the cocone
isomorphism, converts the bijective comparison to a colimit, and applies cofinality.

Added `Sheaf.AlgebraicGeometry.DirectedEtaleSectionIdentifications`, containing the
strictly smaller comparison step, `AlgebraicGeometry.directedEtaleSectionIdentifications`.
Unlike the original theorem it has no limit, directedness, nonemptiness, qcqs, or
affine-transition hypotheses, and asserts no colimit. It identifies stage section
sets and the vertex by isomorphisms and gives their transition/component equations.
This step was not already stated by either composition units or étale restriction.
The new module publicly imports the standalone section-comparison module for its
public `etaleSetSectionComparison` definition, and imports étale restriction for
the planned proof. The second reader removed the broader continuity import.
No existing public import changes.

Updated the original DAG proof and dependencies to match the actual Lean argument.
Added the comparison node with its statement, source, proof in words, searches,
blueprint ancestry, and Lean record. No existing definition or statement changed;
no change record is needed. Local compilation of both delivered modules is clean.

## Proved and sorry left

`AlgebraicGeometry.directedEtaleLimitSections` is proved from the existing
`AlgebraicGeometry.etaleSetSectionContinuity` and the new identification theorem;
its module contains no `sorry`. This is a reduction, not a claim that its transitive
axioms are already sorry-free.

The only `sorry` added or left in delivered Lean is
`AlgebraicGeometry.directedEtaleSectionIdentifications`, node
`lem-weil-pbc-directed-etale-section-identifications`, in
`lean/Sheaf/AlgebraicGeometry/DirectedEtaleSectionIdentifications.lean`.
Its proof is exactly `:= by sorry`. Its docstring and node describe the inverse-image
composition, terminal-object pullback, restriction, and unit calculations needed.

Edge cases checked mathematically: the new lemma accepts arbitrary preorders and
arbitrary cones; a chosen `i₀` already rules out an empty indexing type. A singleton
identity diagram gives the ordinary restriction/composition isomorphisms. If a stage
is empty, any cone mapping to it is empty; the terminal section sets of the empty
scheme are singletons by the empty-cover sheaf axiom. The construction never assumes
that `p` or a cone leg is étale. Neither directedness nor limitingness is smuggled
into the comparison step. The original theorem retains all its hypotheses.

## No longer needed

Removed the original module's direct proof import of
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`; it belongs to the new
comparison module's proof instead. The new comparison module also no longer imports the broader continuity module;
it publicly imports only the standalone section-comparison interface instead.
The original module's direct proof dependencies
on `lem-weil-pbc-sets-etale-inverse-image-composition-units`,
`lem-weil-pbc-sets-etale-inverse-image-restriction`, and `def-pc-fibre-product` are
now carried by the comparison node. These are **not globally pruned**: the comparison
still needs them, and composition/fibre products also occur in the original signature.
The public composition-units import is retained for that signature. Continuity and
its lower-level steps remain needed. No node or module in the original route has
been proved unnecessary globally; no unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's comparison step contained a sizeable
unformalized calculation not stated by its dependencies. The delivery isolates that
calculation rather than duplicating the continuity theorem or assuming its conclusion.
The upper-tail cofinality step is already supplied by Mathlib's
`Over.initial_forget` and the Final/Initial opposite instances; no new cofinality
lemma was needed. The continuity theorem itself already uses the upper-tail indexing,
so the original scheme cone can be passed to it directly.

The local compiled library initially lacked the recently relocated standalone
`EtaleSetSectionComparison` module. The first worker used the public continuity interface exposing
the same comparison declaration. By the second reading the standalone module
was compiled and available, so the new statement imports it directly. No existing
module was copied or redeclared to bypass the publication process. The cited Stacks
source texts are absent locally; Tags 03S2, 09YQ, 03CB, and 03CC were read on the
Stacks website. The concrete calculation is marked as agent-written in `proof_origin`.
LeanSearch returned an Internal Server Error; semantic search and source grep found
no exact existing comparison statement.

## New nodes

`lem-weil-pbc-directed-etale-section-identifications` is the stage/vertex
identification and its two compatibility equations, namely step 3 of the original
DAG proof. Its new module is
`Sheaf.AlgebraicGeometry.DirectedEtaleSectionIdentifications` and its public theorem
is `AlgebraicGeometry.directedEtaleSectionIdentifications`. It inherits chapter
`sec-proper-base-change` and unit `sk-thm-iff`; the original unit route is unchanged.
There are no change records.


## Second reading by W2

1. **Visible declarations unchanged: pass.** Read the diff of the existing module
   against the repository and compared the complete theorem signature byte for byte
   in Python: identical. Its docstring is unchanged. Only its proof, scoped elaboration
   option, and plain proof imports change. There are no changed definitions, target
   statements, adapted modules, or change records. The new module introduces one
   theorem, with no new data definition.

2. **Proof and trust: pass as a reduction.** Compiled both modules in import order
   with `lcompile.py`, again after the import repair; both compile without warnings.
   Read the naturality cancellation, the bijective comparison-to-colimit conversion,
   the cocone isomorphism, and the final upper-tail transport. In scratch copies,
   `#print axioms AlgebraicGeometry.directedEtaleLimitSections` and
   `#print axioms AlgebraicGeometry.directedEtaleSectionIdentifications` both return
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The sole
   delivered sorry is the named identification theorem reported above. No forbidden
   declaration, kernel-check bypass, or hollow definition occurs. This does not
   assert transitive sorry-freedom.

3. **Split statement: pass.** Opened the definition of `etaleSetSectionComparison`,
   composition-with-units theorem, and étale restriction theorem. The chosen
   composition isomorphism satisfies the needed unit equation; restriction identifies
   global sections along each étale structure map. Pullback of the identity object
   is terminal. Inverting these identifications gives precisely the orientations of
   `a` and `l`; unit naturality and uniqueness of maps with the prescribed pullback
   projections give the two displayed equations. Cone legs and `p` need not be
   étale. A chosen index excludes an empty indexing type; no directedness is needed
   even for a disconnected preorder. Singleton identity diagrams reduce to étale
   restriction, and an empty stage forces the cone point empty, giving singleton
   section sets. The result supplies no continuity, bijectivity of a colimit
   comparison, or colimit conclusion, so it is strictly part of the argument.
   Its source and full proof in words are in its docstring and matching node.
   Independently searched with `msearch.py` LeanFinder for
   "inverse image sheaf evaluated at terminal object localization restriction natural
   unit comparison", and grep for "leftAdjointUniq|unit_leftAdjointUniq|pullbackComp";
   also searched the project's Sites, SixFunctors/Etale, and EtaleSet modules with
   `rg`. Results provide adjunction uniqueness, cover-dense restriction, or the
   constituents already used, not this combined identification statement. The
   upstream SectionContinuity theorem has abelian coefficients and an extra
   quasi-separated-base hypothesis, so cannot replace it. Read Stacks
   [03S2](https://stacks.math.columbia.edu/tag/03S2), paragraph after Definition 03S3,
   [03CB](https://stacks.math.columbia.edu/tag/03CB), and
   [03CC](https://stacks.math.columbia.edu/tag/03CC): they supply restriction and
   inverse-image composition; the concrete compatibility calculation is correctly
   recorded as agent-written. Closing that whole calculation is not a short repair.

4. **Route and pruning: pass after import repair.** Continuity supplies the actual
   colimit argument; the new lemma supplies only its section identifications.
   Mathlib `Over.initial_forget` supplies cofinality without a new lemma. Read
   `dag/units/sk-thm-iff.json`, including `realized`: the degree-zero route and
   statement/step realizations are retained. All three old direct dependencies
   replaced by the new comparison node are listed in `No longer needed`; they
   remain transitively needed, and no node is globally pruned. Replaced the new
   module's public continuity import with the now-available standalone
   `EtaleSetSectionComparison` import, removing an unnecessarily broad interface
   dependency. Existing public imports and the parent proof are unchanged.

5. **Nodes agree: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its four steps match the Lean's continuity input, natural diagram
   identification, cocone transport, and finality transport. Both dependency lists
   equal the unions of their step citations. The new node has the required source,
   full statement and Lean record, proof steps, search records, creation data,
   blueprint ancestry, chapter, and unit. Its statement includes both equations
   exactly as needed by the parent proof; no limitingness or finiteness hypothesis
   was added to it. There is no dependency cycle through continuity now that the
   identification module imports the standalone comparison definition directly.

Changed in this second reading: narrowed the new module's public import to
`EtaleSetSectionComparison`, updated the corresponding report descriptions, and
added this review. No mathematical statement or proof body needed repair.
