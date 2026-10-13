## What changed

Proved `affineOpen_representing_cover_descent` in
`lean/Sheaf/Paper/AffineOpenRepresentingCoverDescent.lean` without changing its signature
or either original public import. Added proof-only imports of
`Mathlib.CategoryTheory.Presentable.Directed`,
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`, and
`Sheaf.AlgebraicGeometry.EtaleFiniteCoverFactorizationDescent`.

The proof first constructs a finite affine refinement of the original covering sieve.
Its arrows factor through selected original covering objects, retaining the representing
maps. A proved private helper reindexes the affine-open diagram by a directed initial
functor, applies the existing finite-cover factorization descent theorem with the fixed
stage terminal object, and converts its output to étale X-objects. Explicit pullback
isomorphisms use the stage open immersion's monomorphism property. Their projection
identities and the common source comparison prove the representing equation. The final
proof transfers joint surjectivity through the source isomorphisms and uses ULift to match
the specified universe of the finite index type. No nonempty-cover assumption is added;
all point arguments also work for the empty finite family.

Updated the original node's proof, proof dependencies and proof origin to describe the
compiled argument. All helper definitions are explicit pullback constructions. No data
is defined by choosing a witness of an unproved existence theorem.

## Proved and sorry left

Closed the single original hole in `affineOpen_representing_cover_descent`, node
`lem-weil-pbc-affine-open-representing-cover-descent`. Added zero holes. There is no `sorry`
left in the item or in any added module (no modules are added). The private helpers
`localizedPullbackIso`, `localizedPullbackIso_fst`, `pullbackComp_fst`,
`pullbackComp_inv_fst`, and `affineOpen_finite_representing_models` are fully implemented
or proved. The geometric input is the existing declaration
`AlgebraicGeometry.etale_finiteCoverFactorizationDescent`. Independent axiom checks of the
assembled theorem and every private helper show only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

Validation: the finite-model conversion and the final refinement/transfer proof were
compiled separately during development. The assembled delivery is checked by lcompile
and the deliver3 dry run. Statements and visibility of existing declarations are
unchanged. This is a proof from existing declarations, not a decomposition into new holes.

## No longer needed

Removed the proof edge to `lem-weil-pbc-cartesian-square-pasting`. The proof constructs the
needed source comparison directly using pullback lifts and the monomorphism of the stage
open immersion, verifies its inverse identities by pullback extensionality, and checks
representing equations by the two projections. The particular Mathlib declaration
`CategoryTheory.IsPullback.paste_vert_iff` in that node is not needed. This is pruning of
this item's route; it does not assert that other target branches stop using that node.
No original import was removed. The second reader removed the redundant newly added
proof-only import `Mathlib.AlgebraicGeometry.Limits`; its declarations are already available
through the remaining imports. The directed-reindex, affine-cover-refinement and
finite-cover-factorization-descent nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface correction was needed. The plan's order can be
implemented by reindexing the whole diagram first and then choosing the fixed directed
stage; finite-cover factorization descent performs the tail restriction internally.
The unit statement and its realized steps are unchanged.


## Second reading by Q4

1. **Interface: pass.** Read the repository and sandbox module in full and compared them
   with `diff -u`. The original theorem signature, docstring, visibility, and both public
   imports are byte-for-byte unchanged. No existing definition changes and no adaptation
   or change record is needed. The node's structural map equation, arbitrary index type,
   affine/open stage hypotheses, finite possibly empty refinement, both covering clauses,
   and representing equation all match the original Lean statement.
2. **Proof and data: pass.** `lcompile.py --all` compiled the assembled module without
   warnings. A scratch copy with `#print axioms` for the public theorem and each of
   `localizedPullbackIso`, `localizedPullbackIso_fst`, `pullbackComp_fst`,
   `pullbackComp_inv_fst`, and `affineOpen_finite_representing_models` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned for forbidden
   declarations and holes; none occur. `localizedPullbackIso` explicitly builds both
   pullback lifts and proves their inverse identities. Existential elimination of the
   already proved descent theorem occurs inside a proof, not inside a data definition.
3. **Split statements: pass, none added.** All helpers are proved. Checked the finite
   helper's input against `etale_finiteCoverFactorizationDescent`: affine stages supply
   qcqs and affine transitions, the fixed terminal object is affine, and the targets
   `g.Etale.obj (U q)` may be arbitrary etale objects. The common source comparisons give
   exactly the representing equation used. Checked `n = 0`: neither the helper nor the
   final proof chooses a finite-family element without a point and a covering witness;
   the existing descent theorem allows an empty family. The nonempty directed stage is
   supplied by cofilteredness, independently of the cover.
4. **Route and pruning: pass after import cleanup.** Read the three dependency nodes,
   their recorded declarations, and `dag/units/sk-thm-p1.json`'s `realized` fields.
   Finite affine refinement and directed reindexing are the existing proved results;
   finite-cover descent is used as the existing geometric tool (filed in sk-thm-iff),
   not as a replacement for a unit step. No realized step is bypassed. Read Stacks
   [0EYL](https://stacks.math.columbia.edu/tag/0EYL) (lemma-colimit-affine-sites) and
   [01ZC(3)](https://stacks.math.columbia.edu/tag/01ZC) for the qcqs-source/arbitrary-target
   distinction. A fresh Lean Finder search for inverse-limit affine-open descent with
   prescribed morphisms found only supporting affine-transition-limit results, no
   shorter packaged theorem. `rg` also found the existing finite affine refinement
   declarations and the Mathlib pullback-composition projection lemma already used.
   The only removed old proof dependency is cartesian-square-pasting, fully listed in
   No longer needed; its source comparison is instead constructed directly. Tested
   removal of each new proof import in separate scratch copies: Limits is redundant;
   removing CohomologyColimit, Directed, or EtaleFiniteCoverFactorizationDescent loses
   the refinement, reindexing, or descent declaration respectively.
5. **DAG: pass.** Compared the old and delivered node. Only `proof`, `proof_deps`, and
   `proof_origin` differ. Step 1 records finite affine refinement and its sieve
   factorizations; step 2 records the actual directed reindexing and common-stage
   descent; steps 3 and 4 record the explicit projection calculations, covering
   transport, and ULift reindexing. The dependency union is precisely the three retained
   nodes. No new node or changed statement requires additional metadata.

Second reading changed only the redundant proof-only Limits import and this report
(including correction of the axiom-validation description). The mathematical proof,
original interface, and delivered DAG argument needed no repair. Closed one original
hole, added zero holes; no decomposition is being counted as a proof.
