## What changed

Replaced the sorry in AlgebraicGeometry.flat_precompose_pus by a compiling reduction.
The statement and all existing public imports remain unchanged. A proved private
mate_counit helper derives the counit equation for the canonical right-adjoint
base-change map from Mathlib's conjugateEquiv_counit, naturality, inverse cancellation,
and the pullback adjunction triangle identity. Unfolding the actual definition of
c and extracting its local data specializes that calculation without replacing
any canonical choices.

The proof then applies the new general global Hom counit-square transport lemma
and cancels scalar restriction of the final global Hom adjunction isomorphism.
The new proof import is Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport.
The item node's proof, proof_deps and proof_origin now describe this route.

## Proved and sorry left

Closed: AlgebraicGeometry.flat_precompose_pus (lem-sc-flat-precompose-pus).
Its module now has no sorry. The private mate_counit helper is completely proved.

Added and left: AlgebraicGeometry.schemeGlobalHom_baseChange_counit_transport
(lem-sc-global-hom-base-change-counit-transport), in the new module
Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport. Its entire proof is
`by sorry`; its docstring and node contain the source and the three-step proof.

This is a decomposition: one existing hole closed, one strictly lower comparison
hole added, net zero holes. The new statement is about arbitrary derived objects,
a map t, and two maps e/e' satisfying a counit square. It has no right adjoints a/a',
no canonical duality base-change map c, and only assumes beta_M invertible.
The substantial remaining comparison calculation is isolated; the canonical mate
counit calculation and the combination into the original equality are proved.

Edge cases checked mathematically before stating the lemma: identity base change
reduces to naturality of the direct-image Hom comparison in its second entry;
M=0 gives the equality of zero morphisms; if t=0 the counit-square condition says
Lg*(e)=0, and naturality makes the right composite zero as required. No flatness,
properness, affine, or quasi-coherence assumption is needed for this formal
comparison identity on the unbounded sheaf-derived categories.

## No longer needed

Removed proof import: Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction.
Removed proof dependency: lem-pc-global-hom-pullback-adjunction, whose module and
existential global pullback-Hom isomorphism are not used on the new route.
No other imports or nodes are pruned by this delivery. Whether this module remains
reachable through other target branches is a queue computation, not asserted here.
The unit record sk-thm-picard-duality has no realized statement or proof-step node
that this change bypasses.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan described the mate and Hom
comparison calculations as formal glue but did not supply a Lean theorem for
the global comparison exchange/counit-square step. The existing pullback-Hom
adjunction theorem is an existential isomorphism statement; it does not itself
state that exchange identity for the fixed comparisons in this module.
The reduction separates this missing part from the now-proved mate algebra.

The local literature/stacks-project/duality.tex file was absent. Read the actual
source at https://stacks.math.columbia.edu/tag/0AA8, especially its final diagrams
and the definitions of the comparison maps. LeanSearch returned Internal Server
Error, recorded as unavailable; LeanFinder, Loogle and the library/Mathlib grep
searches ran and found only generic conjugate-mate calculus and underived maps.

## New nodes

lem-sc-global-hom-base-change-counit-transport records the global Hom comparison
transport across a commuting counit square. It isolates the evaluation-mate,
tensor, and Leray compatibility from the canonical right-adjoint mate algebra.
Its module is lean/Sheaf/AlgebraicGeometry/GlobalHomBaseChangeCounitTransport.lean.
The source is Tag 0AA8's final diagrams, with the canonical evaluation-mate
comparisons of Tags 08I3 and 0B6I. No interface change or forced adaptation occurs.

## Second reading by K2

1. Interface: PASS. Read both delivered modules and diffed FlatPrecomposePus
against the repository version. The entire existing flat_precompose_pus signature
is byte-for-byte identical, as is its docstring. There are no definition changes,
change records, or forced adaptations. The only import replacement is a plain
proof import. The new module's public import supplies its statement's definitions.

2. Proof and trust: PASS as a decomposition. Compiled both modules with
lcompile.py --all: 3.2 seconds for GlobalHomBaseChangeCounitTransport and 12.3
seconds for FlatPrecomposePus, with no errors or warnings. A scratch copy with
#print axioms compiled in 10.7 seconds: mate_counit uses only propext,
Classical.choice and Quot.sound; flat_precompose_pus and the new transport theorem
also use sorryAx, as expected from the open comparison lemma and imported open
statements. There is exactly one delivered sorry, the named public transport
theorem. No axiom, unsafe, opaque, implemented_by, extern, hollow definition,
or arbitrary data chosen from an unproved existence statement was introduced.
The scratch source was removed before delivery.

3. Split statement: PASS. Independently read Stacks Tags
[0AA8](https://stacks.math.columbia.edu/tag/0AA8),
[08I3](https://stacks.math.columbia.edu/tag/08I3), and
[0B6I](https://stacks.math.columbia.edu/tag/0B6I), and the actual pinned comparison
definitions in GlobalHomPullbackComparison and GlobalHomAdjunctionIso. The new
statement is the general evaluation-mate exchange identity with a commuting
counit square, not a renamed right-adjoint base-change theorem. Its proof has
no need for properness, flatness, perfectness, or affine bases: these are needed
in the source to establish invertibility, whereas here only beta_M is assumed
invertible. No invertibility of beta_N is used.

For clarity, suppress scalar restriction and its canonical square identification,
write H for global Hom, p for pullback comparison, and d for direct-image
comparison. The exchange identity before cancelling beta_M is
  p_gX ; d_f' ; H(beta_M,1) = d_f ; p_g ; H(1,beta_N).
Its target is H(Lg*Rf*M,Rf'*LgX*N), so neither beta is assumed invertible
at this step. To verify it, transpose the internal-Hom maps under tensor-Hom
and pullback adjunctions. Both composites evaluate after the counit of f'
(or equivalently the pulled-back counit of f); the equality of these counits
is the defining mate equation for beta. The tensor identifications agree by
canonical pullback composition, and the global-sections identifications agree
by the canonical Leray composition. Postcompose with H(1,Rf'(t);e'), use
naturality of d_f' to move t, and use h to replace beta_N;Rf'(t);e' by Lg*(e).
Naturality of p_g moves e to d_f's output. This gives the claimed left composite
postcomposed with H(beta_M,1) equal to the right composite without its last
inverse factor. Postcompose with H(beta_M inverse,1) and use functoriality and
inverse cancellation to obtain exactly the displayed statement.

Tested identity base change (naturality of the direct-image comparison), M=0
(zero source), t=0 (h forces Lg*(e)=0, hence the other path is zero), and f=id
(the direct-image comparisons reduce to the identity and the statement reduces
to pullback-comparison naturality). None requires extra assumptions. Repeated
searches with different words: LeanFinder on evaluation mates and Beck-Chevalley
exchange returned only generic exponentiable-morphism identities; Loogle on
Adjunction/NatTrans/MonoidalCategory returned no hits; msearch grep on tensor
base-change found unrelated algebraic results. Direct rg of the project found
internalHomMate_exists and lerayNaturality, both private helpers in
GlobalHomAdjunctionIso, but neither states the exchange identity. Also searched
the upstream AlgebraicGeometry and CategoryTheory source: underived Hom and
generic derived base-change declarations, no matching global Hom theorem.
Closing the remaining exchange/coherence calculation is not a few-minute use
of an existing lemma, so the one explicitly documented hole remains.

4. Route and pruning: PASS. Read the target downward. The proved mate_counit
helper uses conjugateEquiv_counit, beta naturality, inverse cancellation,
counit naturality, and the pullback triangle identity. Unfolding the canonical
base-change map specializes that calculation without changing its data.
The main proof then specializes the general transport statement and cancels
the scalar-restricted final adjunction isomorphism. The original proof_deps
were exactly def-sc-duality-equation-base-change-map,
lem-pc-global-hom-adjunction, and lem-pc-global-hom-pullback-adjunction.
Only the last is absent from the new proof and it is fully listed under
No longer needed, together with its removed module import. Public imports
name definitions used in the existing signature. The unit
sk-thm-picard-duality has realized.statement=[] and realized.steps=[[]];
no realized unit node or step is bypassed.

5. Records: PASS after repair. The existing node changes only proof,
proof_deps, and proof_origin; its three steps match the mate equation,
transport specialization, and cancellation in Lean. The new node supplies
source, complete proof steps, their dependency union, the actual Lean signature,
creation provenance, blueprint ancestry, chapter/unit, and recorded searches.
The new theorem's module and docstring identify that same node and source.
Corrected doubled TeX backslashes in the new node's natural-language statement
so the JSON decodes to ordinary TeX commands. No mathematical statement changed.

Second reading changed: new-node TeX escaping and this independent review record;
no Lean proof repair was necessary. One existing hole is closed by a genuine
reduction, one smaller hole is added, and the net hole count remains zero.
