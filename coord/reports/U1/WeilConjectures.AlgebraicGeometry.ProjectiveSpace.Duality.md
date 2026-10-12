## What changed

Replaced the sole sorry in
`AlgebraicGeometry.ProjectiveLine.exists_exact_sigma_twist` by a complete Lean proof
from the existing graded-representation and graded-syzygy theorems and two new,
independent intermediate theorems. The original declaration's signature and
existing docstring are unchanged. All other proofs and declarations of Duality
are unchanged, including both already-proved duality isomorphisms.

The proof chooses a chart-compatible Proj/projective-line comparison using
`Proj.proj_shifted_free_is_twist k 0`. It establishes local Noetherianness of
both models, uses ordinary module pullback's existing quasi-coherence and
finite-presentation instances, and converts to `RingedSpace.IsCoherent` using
`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`. It then applies
`Proj.coherent_exists_graded_representation` and
`MvPolynomial.exists_graded_free_resolution_two`.

`Proj.sheafify_graded_chain` gives an exact chain of associated sheaves, retaining
their chart data, independently of freeness or finiteness. For each of its three
terms, `Proj.homogeneous_basis_sheaf_twists` uses the syzygy theorem's actual
homogeneous basis and degrees to give the required finite sum of twists. Neither
new theorem supplies a graded representation or a graded resolution of a
coherent sheaf: those two substantive existence steps are applications of the
existing declarations in the target proof.

Finally the target proof constructs the last-term isomorphism using pullback of
the representation isomorphism, `pullbackComp`, `pullbackCongr` of
`C.iso.inv_hom_id`, and `pullbackId`. It explicitly conjugates all three arrows
through the four object isomorphisms. Monicity and epicity follow by composition
with isomorphisms; `ComposableArrows.isoMk₃` checks all three commuting squares,
and `ComposableArrows.exact_of_iso` transports exactness.

The seven added imports of Duality are non-public proof imports. The two new
modules have public imports for their signatures and non-public imports of the
existing planned proof dependencies. The resolution node's proof, proof_deps
and proof_origin now describe this Lean proof. No statement, definition, target,
unit or chapter route changed.

All three delivered modules compile together, without warnings, through
`lcompile.py --all`. The required `deliver3.py --no-push` printed OK: compilation and preflight passed,
with only the second reading left for the second worker. Nothing was pushed.

## Proved and sorry left

Reduced/proved from named intermediate statements:
`AlgebraicGeometry.ProjectiveLine.exists_exact_sigma_twist`
(node `lem-sc-p1-graded-resolution`). There are no direct sorries left in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality`.

The only direct sorries in the delivery are the whole proofs of these public
named theorems, each in its own new module with source and proof docstring:

- `AlgebraicGeometry.Proj.sheafify_graded_chain`, node
  `lem-sc-p1-sheafify-graded-chain`, module
  `Sheaf.AlgebraicGeometry.ProjectiveSpace.SheafifyGradedChain`.
- `AlgebraicGeometry.Proj.homogeneous_basis_sheaf_twists`, node
  `lem-sc-p1-homogeneous-basis-sheaf-twists`, module
  `Sheaf.AlgebraicGeometry.ProjectiveSpace.HomogeneousBasisSheafTwists`.

This is a reduction, not a claim of transitive sorry-freedom. Existing
representation, syzygy, coherent-criterion and shifted-free dependencies also
remain as their library declarations. No private or anonymous sorry, hollow
definition, axiom or change to a public signature was introduced.

Edge cases were checked mathematically before stating the intermediates.
The exact-chain theorem has no finite-generation assumption: associated
sheafification is exact for arbitrary graded modules. All-zero modules and
zero endpoint ranks give zero associated sheaves and valid monic/epic zero
maps between zero objects. The basis theorem includes rank zero, positive,
zero and negative shifts. Its basis degree is `-d`, so a coefficient of degree
`n` contributes degree `n-d`, and the degree-j coordinate has degree `d+j`;
negative polynomial degrees are zero. This agrees with `S(d)_j = S_(d+j)`.
The two-chart transition is `x₀^d = t^(-d)x₁^d`, including negative d.
Transport uses a scheme isomorphism, so needs no separate flatness assumption.
No algebraic-closedness or characteristic restriction is added to the field.

## No longer needed

None. No original import or proof dependency is pruned. An import-removal compile
confirmed that the new direct FiniteDescent import is needed to obtain the
finite-presentation/finite-type instance for the ordinary pullback. The original four
resolution dependencies remain needed: coherent representation and graded
syzygy are applied directly, exact associated sheafification is the main
planned tool of the new exact-chain theorem, and shifted-free identification
is used both to obtain the chart comparison and in the new basis theorem.
Their modules remain reachable through the non-public proof imports. The new
nodes do not bypass the unit's graded-resolution route.

## Where the brief, the DAG or earlier work was wrong

There is one direct sorry in this module; both duality isomorphisms already
have complete proofs, and the current proofs do not call the graded-resolution
theorem. This delivery addresses the requested remaining declaration without
rewriting those completed proofs or their DAG node.

The planned declarations are mathematically useful but are not directly
composable into the target: coherent representation and sheafification use
polynomial Proj and explicit degree-zero fraction charts; the source theorem
uses the glued projective line and actual finite coproducts of its twists.
The syzygy theorem gives arbitrary free modules with homogeneous bases, while
the shifted-free theorem's coproduct chart data are for canonical coordinate
modules. The two new statements isolate those interfaces without changing
any definition or weakening any existing statement.

Primary source checks: [Stacks 01M7](https://stacks.math.columbia.edu/tag/01M7)
explicitly supplies functorial exact associated sheafification;
[Stacks 01M6](https://stacks.math.columbia.edu/tag/01M6) supplies the associated
sheaf construction, and [Stacks 01MN](https://stacks.math.columbia.edu/tag/01MN)
identifies the twist with the sheaf of the graded shift. The detailed new
proofs follow the corresponding clauses of the original resolution node.
The literature files themselves are not present in this remote clone; these
primary-source pages were read online. The EGA/Hartshorne references of the
original node are retained as provenance, not claimed to have been read here.

Searches used LeanFinder, Loogle and direct ripgrep of Mathlib and both library
roots. They found ordinary-localization exactness, generic projective
resolutions and canonical shifted-free chart interfaces, but no direct
matching theorem. LeanSearch was attempted for both new interfaces and
returned HTTP 500; this is recorded as unavailable, not evidence of absence.

The generic locally-Noetherian coherence criterion
`pqf-lem-coherent-ft-locnoeth` is used as a tool to reconcile the two existing
coherence encodings. The generic module-pullback adjunction
`lem-pc-module-pullback-adjunction` is a planned tool for comparing ordinary
and tensor-formula pullback in the basis theorem. These do not replace a step
of the unit's route. No tool_uses field was edited; the maintainer can record
these tools at review.

## New nodes

`lem-sc-p1-sheafify-graded-chain` states construction and exactness of the
associated sheaf chain for an already-given exact graded chain, with chart
data retained and inverse scheme-isomorphism pullback applied. It does not
assert existence of a resolution or identify its terms as twists. Its file is
`dag/nodes/sec-picard-framework/lem-sc-p1-sheafify-graded-chain.json`.

`lem-sc-p1-homogeneous-basis-sheaf-twists` identifies the associated sheaf of
one already-given graded module with a finite homogeneous basis as the sum
of the prescribed twists. It has no exactness, coherence or resolution
hypothesis. Its file is
`dag/nodes/sec-picard-framework/lem-sc-p1-homogeneous-basis-sheaf-twists.json`.

Both inherit chapter `sec-picard-framework` and unit `sk-thm-picard-duality`,
with blueprint ancestor `lem-sc-p1-graded-resolution`. No change record is
needed: existing signatures, definitions and public import visibility are
unchanged.

## Second reading by U1

1. **Statements unchanged.** Compared the delivered Duality module with the repository version; the existing declaration signatures and definitions are byte-for-byte unchanged. The two new declarations are separate split-off lemmas with independent statements and documented sources.

2. **Proof validity.** Compiled all three delivered modules with `lcompile.py --all`; compilation is clean. The only remaining `sorry`s are the two named split-off theorems listed above, with no hollow definitions, axioms, unsafe declarations, or forbidden primitives. A scratch copy with `#print axioms` for the target and both new lemmas compiled: each lists only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected for this reduction.

3. **Split-off statements.** Checked the edge cases recorded in the report (zero rank, zero modules, and negative twists). The split statements are strictly intermediate interfaces rather than restatements of the resolution target, and their DAG nodes, docstrings, and declarations agree. Independent LeanFinder searches for exact graded linear-map chains and for finite homogeneous-basis sheaf isomorphisms returned ordinary-localization exactness, generic projective resolutions, `GradedModule.linearEquiv`, and Proj chart isomorphisms, without a matching interface. Loogle found `Module.Basis.equivFun`, which provides the coordinate equivalence but not its graded/sheaf comparison. Direct searches of both library roots confirmed the planned short-exact and canonical shifted-free interfaces are distinct. Re-read [Stacks 01M7](https://stacks.math.columbia.edu/tag/01M7) and [01MN](https://stacks.math.columbia.edu/tag/01MN): they support exact associated sheafification and the stated shift convention.

4. **Pruning and route.** The proof follows the unit route through coherent graded representation, graded syzygy, exact sheafification, and shifted-free/twist identification. Imports and proof dependencies are all used; no pruning is justified.

5. **DAG agreement.** Checked that the delivered `lem-sc-p1-graded-resolution` proof steps, dependencies, and origin match the Lean proof. The two new node records contain the required source, proof, Lean declaration, chapter, and unit fields. The unit route and `realized` data are preserved.

I changed only this second-reading report section; no Lean source or statement required repair.
