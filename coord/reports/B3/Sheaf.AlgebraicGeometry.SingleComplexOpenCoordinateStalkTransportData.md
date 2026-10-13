## What changed

Replaced the hole in `AlgebraicGeometry.exists_singleComplexOpen_normalized_transport`
with a proof that reduces to the literal termwise restriction of P. Its original
signature and public imports are unchanged. Added a proof import of
`Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison`.

Constructed `AlgebraicGeometry.openDerivedAdditiveStalkIso` in the new module
`Sheaf.AlgebraicGeometry.OpenDerivedAdditiveStalkIso`, from
`Scheme.Modules.restrictStalkNatIso`, `overFunctorEquiv`, exact localization
composition, and exact functors commuting with homology. This is a concrete
natural isomorphism, with no existence-witness choice and no hole in its data.

The canonical termwise lemma supplies K-flatness and invertibility of the
pinned counit on the actual restricted complex, together with its square.
The parent composes the six component naturality squares of the
restriction/pullback comparison and proves naturality of the restricted
identity coefficient.
The resumption adds the proved private categorical lemma `map_comp_square`
and uses it for transport through e, avoiding expensive rewriting inside
nested derived definitions. Local transparency options also avoid unnecessary
unfolding; no file was split to meet the compile limit.
It then transports the canonical square through e, constructs
E = restriction's localization factor followed by restriction(e), and compares
Q to the restricted P by b = a followed by E inverse. The already proved
`exists_comparisonSourceIso` and `comparisonIntoPullback_naturality` give a
source isomorphism d and the required comparison square. Composing d with the
canonical termwise source isomorphism finishes the original statement.

## Proved and sorry left

Closed original hole:

- `AlgebraicGeometry.exists_singleComplexOpen_normalized_transport`
  (`lem-pc-single-complex-open-normalized-transport`).

Added hole:

- `AlgebraicGeometry.exists_singleComplexOpen_termwise_comparison`
  (`lem-pc-single-complex-open-termwise-comparison`) in
  `Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison`.

The added theorem concerns only P, its literal termwise restriction P0,
K = Q(P), the canonical localization factor, its K-flat and counit properties,
and the concretely constructed additive derived-stalk comparison.
It has no arbitrary Q, K, e, or a.
The change from this canonical case to the original arbitrary representatives
is proved, not assumed. This is a decomposition: one original hole closed,
one strictly smaller hole added, net zero direct holes. The new additive
stalk-isomorphism construction and all private helper lemmas contain no sorry.

## No longer needed

No original import was removed and no globally unnecessary node or module is
claimed. The following old direct proof dependencies were removed from the parent
node and moved to the canonical termwise node: `def-pc-base-derived-tensor-cohomology-model`,
`def-pc-single-complex-base-change-stalk-condition`, `lem-pc-kflat-stalk-criterion`,
and `lem-pc-open-restriction-stalk-extension-iso`. They are still used by the lower
calculation and are not globally pruned. The trial proof import of `Sheaf.Algebra.Homology.KFlatPullback` was
removed from the parent when the restricted complex properties were kept
inside the canonical termwise lemma. The original lower ring/tensor dependencies
remain needed by the canonical termwise calculation. Their use is now in the
new lower node rather
than being part of the parent node's unimplemented plan. The parent directly
uses the two existing representative-transport lemmas and the new canonical
termwise-comparison lemma.

## Where the brief, the DAG or earlier work was wrong

No statement was changed and no mathematical dispute was found. The DAG's
original transport step concealed two distinct jobs: actual open stalk-ring
transport and passage between arbitrary derived representatives. They are now
separated, and the latter passage is implemented in Lean. The unit record
`sk-thm-picard-semicon` has no realized statement or step attached to this node;
its route and all unit/chapter records are unchanged.

The referenced Stacks TeX files are not present in this read-only clone. I read
the corresponding authoritative pages at
[Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
[Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8), and
[Tag 08HY](https://stacks.math.columbia.edu/tag/08HY),
[Tag 0098](https://stacks.math.columbia.edu/tag/0098),
[Tag 08DW](https://stacks.math.columbia.edu/tag/08DW),
[Tag 06YC](https://stacks.math.columbia.edu/tag/06YC), and
[Tag 08FE](https://stacks.math.columbia.edu/tag/08FE).
LeanFinder returned the open stalk-ring and underived restriction-stalk tools;
Loogle returned restrictStalkNatIso and its germ formulas; Mathlib grep confirmed
those underived tools. LeanSearch returned Internal Server Error, recorded as
unavailable. Repository and blueprint searches found no theorem giving the
canonical termwise square. No inference of invertibility of either horizontal
comparison is used. Empty opens have no z, and the constructions also cover
top opens, zero complexes and zero rings.

The previous attempt timed out in the delivery compile. On resumption, the
first dry run reproduced the timeout. A profiler check showed substantial
elaboration and linting of the nested comparison definitions. The parent and naturality helper's
local transparency settings were changed to avoid unnecessary unfolding;
no dependency definition, statement, or visibility changed, and the file and
proof were not split for performance. An ordinary compile of all three
sandbox modules then passed cleanly (6.8 s, 20.2 s, and 58.6 s).
A second dry run still timed out, so the naturality transport of e was
rewritten using the proved private categorical helper `map_comp_square`,
avoiding rewrite search inside the nested derived definitions. The final
source passed a clean standalone compile in 39.6 s.
The final `deliver3.py --no-push` printed OK: commit `b76fc910e5` compiles
and passes the preflight except for the second reading, which the second
reader writes. The worker intentionally leaves that section to the reader.
Nothing is pushed by this worker.

## New nodes

`def-pc-open-derived-additive-stalk-iso` records the concrete natural isomorphism
`AlgebraicGeometry.openDerivedAdditiveStalkIso` in
`Sheaf.AlgebraicGeometry.OpenDerivedAdditiveStalkIso`. It carries no hole and
is used in the new comparison statement and in the original proof.

`lem-pc-single-complex-open-termwise-comparison` records only the canonical
termwise-restriction comparison square with that specific natural isomorphism.
It is the only new sorry and is strictly a part of the original argument.
Its docstring supplies the K-flat, ring-transport, tensor/cohomology and counit proof.

No change record or forced adaptation is needed: no existing interface changed.

## Second reading by B3

1. **Interface and accidental changes.** I compared the delivered target module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only a plain proof import and proof text were added. The two added modules and their declarations are the ones recorded by the two new DAG nodes.

2. **Compilation and proof hygiene.** I compiled all three sandbox modules with `lcompile.py --all`; they passed cleanly. The target proof has no `sorry`, axiom, unsafe, opaque, extern, or implemented-by declaration. The sole remaining `sorry` is the named canonical termwise theorem `exists_singleComplexOpen_termwise_comparison`, with its docstring and matching node. The concrete additive stalk isomorphism is a definition with no hole.

3. **Statements and decomposition.** The original target statement is unchanged. The added termwise theorem is a strict canonical special case: it fixes the literal restricted complex and has no arbitrary Q, e, or a, so it is strictly smaller than the target and is used to close the representative-transport proof. The additive stalk isomorphism is a concrete construction, not an arbitrary witness. No duplicate library theorem was found in the repository or recorded search results.

4. **Proof route and pruning.** The proof uses the existing representative-transport and pullback-naturality declarations, the new canonical termwise theorem, and the new explicit stalk-isomorphism definition. Imports needed by the proof are retained; the trial `KFlatPullback` import was removed and is documented under “No longer needed”. The unit route and unit records are unchanged.

5. **DAG agreement and risks.** The target node’s proof and `proof_deps` match the imports and declarations used in the delivered proof. The two new nodes contain their statements, sources, proof origins, Lean records, and search records. I found no statement dispute, forced adaptation, changed definition, or unresolved compiler warning.

What I changed in this second reading: this report section and the explicit list of four former direct dependencies under “No longer needed”; no Lean source, statement, node, or import was altered. Independent searches used Loogle for `"isKFlat_restrict"`, LeanFinder for exact localization/stalk cohomology and derived tensor open restriction, and grep for exact homology comparison and K-flat restriction. They returned no complete canonical comparison theorem; the underived restriction-stalk tools were already used. Repository searches also found only constituent stalk transports. The empty-open case has no z; in the top-open case the constructions are functorial isomorphisms; zero complexes and zero stalk rings leave the same square of zero maps. No flatness over the base or boundedness was silently assumed.

The independent `#print axioms` scratch import passed: `openDerivedAdditiveStalkIso`
uses only `propext`, `Classical.choice`, and `Quot.sound`; the parent theorem and
canonical termwise theorem additionally use `sorryAx`, consistently with the
reported open lower theorem/dependencies. The scratch import was not delivered.
The dry run printed OK (review class CODEX because it adds modules and nodes).
