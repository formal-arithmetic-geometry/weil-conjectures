## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.finite_coproduct_sheaf_core` in
`Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections` directly from Mathlib.
The signature and existing docstring are unchanged. The summand maps form an open
cover, hence a pro-etale cover. Mathlib's sheaf gluing criterion gives the bijection:
monicity handles equal indices; disjoint coproduct geometry makes any common source
for distinct indices empty, where the empty-cover sheaf condition gives unique sections.
The empty-family clause follows from joint surjectivity and that same empty-cover argument.
Added only the proved private helper `sections_unique_of_isEmpty`, now a direct
application of Mathlib’s `Sheaf.isTerminalOfBotCover` and
`Types.isTerminalEquivUnique`.

The qcqs hypotheses are not needed for the section argument and are explicitly cleared,
while preserved in the signature. A declaration-scoped unused-variable linter
option suppresses the resulting warnings without renaming or removing the binders. The finite-index hypothesis supplies the smallness
instance required by the existing coproduct. Updated the node's proof route and proof
metadata to match the completed Lean proof.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.ProEt.finite_coproduct_sheaf_core`
(node `lem-weil-pbc-proetale-finite-coproduct-sections`).
The private helper `sections_unique_of_isEmpty` is also fully proved.
No holes added, no split-offs, and no `sorry` remains in the delivered module.
Compilation succeeds with the original signature. The delivery dry run checks the
axioms of all declarations; only the project's three permitted axioms are used.

Edge cases: the proof explicitly treats empty index types, arbitrary empty summands,
and empty common source schemes; no nonemptiness is assumed. For a singleton index,
compatibility uses only monicity, just as for the diagonal of any family.

## No longer needed

Removed the unused proof-only import `Sheaf.CategoryTheory.SiteCoveringAxioms`.
Removed `def-weil-pbc-sites-and-cohomology` from this node's proof dependencies:
its custom `Precoverage.IsSiteForCoverings` predicate is not needed, because Mathlib
already provides the actual sheaf axiom and pro-etale covering API. Its statement
dependency record is retained, and this is no claim that other users can prune it.

No other original imports, nodes, or modules are bypassed. The scheme coproduct
and pro-etale site dependencies remain used. No blueprint unit statement or proof
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The planned finite qcqs covering
verification can be shortened: every jointly surjective family of open immersions is
already a pro-etale cover, by Mathlib's Zariski-to-pro-etale precoverage inclusion.
This makes the existing qcqs hypotheses unnecessary for this theorem's proof.

## Second reading by F2

1. **Interface: pass.** Compared the complete delivered module with the repository
   using `diff -u`: the existing theorem signature and docstring are byte for byte
   unchanged, including all universes, `Finite I`, the qcqs assumptions, the
   coproduct identification, the coprojection equations, and both conclusion clauses.
   The only added declaration is a private proved helper. The public import is
   still needed for `X.ProEt` and `topology X` in the statement; the removed
   `SiteCoveringAxioms` import was proof-only. No definition or target changed.
2. **Proof: pass.** Independently compiled the original delivery, then the revised
   module and a scratch copy with `#print axioms` for the theorem and private helper.
   Both declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
   No `sorry`, axiom, unsafe/opaque declaration, external implementation, or data
   construction from an unproved existence theorem occurs in this module.
3. **Split statements: pass, none.** There are no split-offs or new open statements.
   The helper concerns the actual sections of an arbitrary sheaf on an empty object,
   and is an instance of Mathlib's empty-cover theorem. Checked empty index types,
   empty summands, the singleton family, and empty common sources. In the equal-index
   branch the same open immersion cancels; in the unequal-index branch the
   commuting square into distinct coprojections forces the source empty. No
   nonemptiness or quasi-compactness is silently used.
4. **Route and pruning: pass.** Read Mathlib's `sigmaOpenCover`,
   `isEmpty_of_commSq_sigmaι_of_ne`, `zariskiPrecoverage_le_propQCPrecoverage`,
   `ProEt.bot_mem_topology`, and `Presieve.isSheafFor_arrows_iff`. A fresh LeanFinder
   search for empty-cover unique sections and disjoint-cover restriction found
   `Sheaf.isTerminalOfBotCover`; searched the local Sheaf/WeilConjectures sources
   as well. The existing affine-pro-etale gluing lemmas and etale disjoint-cover
   theorem use different sites and do not replace this proof. The unused custom
   site-axiom dependency is the only old proof dependency removed, as already
   listed above. Read `dag/units/sk-thm-properbasechange.json`: none of its realized
   statement or step nodes is bypassed or changed. No globally unreachable module
   is claimed here; `SiteCoveringAxioms` is pruned from this module's imports.
5. **DAG: pass.** Compared the old and delivered node records. Only `proof`,
   `proof_deps`, and `proof_origin` change. The two steps match the actual cover
   construction and unique gluing proof; their dependency union is the two retained
   nodes (the pro-etale site and the Mathlib scheme-coproduct family). There are
   no new nodes to validate. Updated the second step to name the Mathlib terminal
   object and unique-type lemmas now used by the helper.

Second reading changed only the helper's proof to reuse Mathlib's empty-cover
terminality theorem, the corresponding DAG explanation, and this report. The main
proof, signatures, docstrings, and imports needed no further repair. One original
hole closed, zero holes added; this is a proof, not a decomposition.
