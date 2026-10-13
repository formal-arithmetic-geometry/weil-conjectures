## What changed

Proved `AlgebraicGeometry.qcqsProjectionMate_affineLocus_closed` in
`Sheaf.AlgebraicGeometry.QCqsProjectionMateAffineLocus` without changing its signature,
universes, hypotheses, or existing docstring. Added proof-only imports for the existing
coproduct and quasi-coherence preservation lemmas, upstream K-flat tensor exactness,
and Mathlib's Yoneda, five-lemma, adjunction, colimit, and retract tools.

The private helpers construct the supplied mate and prove generic all-shifts closure.
The five-term sequence uses the distinguished triangle and its rotations, so no
compatibility of the supplied tensorator with a chosen shift comparison is needed.
Tensor exactness is transported from a K-flat representative, preserving independence
of the scheme and localization universes. No arbitrary witness is chosen as definition data.
The DAG proof text now describes the actual Lean argument; its geometric proof dependencies
are retained and used. The unit route is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.qcqsProjectionMate_affineLocus_closed`
(node `lem-pc-qcqs-projection-mate-affine-locus`).

No `sorry` remains in the delivered module, and no new hole or module was added.
All private helpers are proved. This is a proof from existing recorded dependencies,
not a decomposition into new holes. The existing public signature is preserved,
including compactness and quasi-separatedness binders which the more general categorical
proof does not directly use. The corresponding unused-section-variable lint is locally
disabled solely to retain those binders.

## No longer needed

None. No original import is removed, and every recorded geometric proof dependency is used.
The redundant candidate proof imports of Mathlib MorphismProperty.Retract,
Abelian.DiagramLemmas.Four and Limits.FullSubcategory were omitted after compilation
confirmed their needed declarations were already available through retained imports.
No planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The geometric exactness step needs care with universes:
the upstream bundled `DerivedCategory.commShiftTensorRight` requires a Grothendieck instance
in the localization universe, which the statement does not supply. The proved K-flat-object
shift and exactness lemmas avoid this extra requirement, and transporting along a K-flat
representative gives precisely the needed exact structure. The proof retains the DAG's
all-shifts five-lemma route and does not impose shift compatibility on the supplied mate.

## Second reading by N2

1. **Signatures and accidental changes.** Compared the delivered module with the repository
version. The public theorem and all existing declarations are byte-for-byte unchanged in
signature, universes, hypotheses, and conclusion. Only proof-only imports, private helpers,
and the theorem proof differ.

2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds with no errors or
warnings. Searched the delivered module for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
`implemented_by`, and `debug.skipKernelTC`; none occur. The proof uses only existing declarations
and contains no hollow definition.

3. **Statements and dependencies.** No statement was split off and no new node was added. The
existing node's statement remains unchanged and its proof steps agree with the supplied-mate,
exactness, coproduct, five-lemma, and retract argument. The DAG proof dependencies are retained
and are all used by the proof.

4. **Shortest route and pruning.** Checked the imported declarations and Mathlib alternatives.
The private five-lemma/Yoneda route is the direct available categorical proof; K-flat transport
is required to avoid an unavailable localization-universe Grothendieck instance. No original
import or proof dependency can be removed, so the `No longer needed` list is complete.

5. **Unit route.** The unit's realized route is preserved: the supplied mate is constructed,
exactness and coproduct preservation are established, then closure under coproducts, distinguished
triangles, and retracts is proved. No unit step is bypassed.

I changed only this report by adding this second-reading record; the Lean proof and DAG node
needed no repair.
