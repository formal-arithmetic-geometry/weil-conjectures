## What changed

Replaced the proof of `CategoryTheory.Functor.essentiallyConstant_splitting` in
`lean/Sheaf/CategoryTheory/EssentiallyConstantSplitting.lean` with a complete proof.
The existing signature, visibility, imports, and four-step DAG route are unchanged.

`NatTrans.ofOpSequence` turns the adjacent compatibility hypothesis into a natural
transformation from the constant functor; its naturality gives compatibility at
arbitrary indices. The retraction then splits each tail term: the explicit pair
is `(p j hj c, c - π j (p j hj c))`. Applying the retraction proves the first
coordinate is forced, and subtraction proves uniqueness of the kernel coordinate.
Functoriality gives compatibility of the projections and preservation of kernels.
Finally, the supplied factorization witness makes a sufficiently late transition
vanish on the kernel.

A declaration-scoped `linter.unusedVariables.funArgs false` handles the existing
lambda index `j` in the statement's definition of `p`, used only implicitly.
This keeps the original statement text unchanged; other unused-variable checks
remain enabled.

Searches: LeanFinder found only generic group-extension splittings; Loogle found
`CategoryTheory.NatTrans.ofOpSequence`, which is used. Searches of both library
roots found no existing proof of this statement. No additional theory is needed.

Validation: the module compiles through `lcompile.py` with no warnings. The
`deliver3.py --no-push` dry run checks compilation, allowed axioms, unchanged
signatures, and delivery preflight. No new module or declaration is introduced.

## Proved and sorry left

Closed one hole: `CategoryTheory.Functor.essentiallyConstant_splitting`, node
`lem-weil-pbc-essentially-constant-splitting`.

No `sorry` remains in the item's module. No holes were added or split off.
This is a complete proof, not a decomposition into unproved intermediate results.

## No longer needed

None. Both existing imports remain necessary: `EssentiallyConstantSystem` supplies
the abelian-group category and inverse-system/natural-transformation infrastructure;
`Mathlib.Algebra.Group.Subgroup.Ker` supplies the kernels appearing in the statement.
No proof-only imports were added. The two existing definition dependencies remain
appropriate: the inverse-system functor infrastructure is used directly, and the
explicit hypotheses are the witnesses of essential constancy. No unit route or
planned proof dependency is bypassed, and no module is claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The four elementary steps recorded in the DAG
suffice without additional lemmas. The existing statement's implicit-only lambda
index produces a lint warning after replacing `sorry`; the narrowly scoped lint
option described above resolves it without changing the signature.

## Second reading by C4

1. **Unchanged interface — pass.** Read the complete repository and sandbox modules
   and their `diff -u`. Extracted the existing theorem signature and compared it
   byte for byte: identical. Imports, public visibility, universes, definitions,
   and docstring are unchanged. The only edits are the proof and the scoped lint
   option; no change record is required.
2. **Proof and axioms — pass.** Independently compiled the delivered module through
   `lcompile.py` without errors or warnings. Compiled a scratch copy with
   `#print axioms CategoryTheory.Functor.essentiallyConstant_splitting`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Inspected
   all local constructions and scanned the delivered Lean for forbidden
   declarations and holes: none. In particular, `z` is the explicitly constructed
   difference, and the eventual index comes from the supplied hypothesis, not
   from an unproved existence theorem.
3. **Split-off statements — pass (none).** No new statement, declaration, module,
   or hole is introduced. Checked the argument at `j = i₀`, `k = j`, and zero
   groups: identity transitions and the zero kernel behave as claimed. The
   arbitrary-index compatibility really follows from the adjacent hypothesis
   by `NatTrans.ofOpSequence`, not an extra assumption.
4. **Route and pruning — pass.** Reviewed the retraction, explicit decomposition
   and uniqueness, transition compatibility, and eventual vanishing, top down.
   An independent Loogle query `AddMonoidHom, Function.LeftInverse` finds
   range equivalences and inverse constructions, which do not replace this
   system-level proof. Searched both library roots for essential constancy and
   kernel splittings; found no existing replacement theorem. The existing
   imports supply the statement's category/functor infrastructure and kernel
   definitions; no proof-only public import was added. Both old dependency
   nodes remain relevant, so `No longer needed` is complete. Read
   `dag/units/sk-thm-p1.json`: this auxiliary node is below the unit's realized
   statements and steps, and the unit route is unchanged.
5. **DAG agreement — pass.** Read the item's node and both dependency nodes.
   The four recorded proof steps are precisely realized by `hcone`/`hsplit`,
   `first` and the explicit `z`, `hp` and kernel preservation, and the final
   use of `hfactor`. The existing `proof`, `proof_deps`, and document-based
   `proof_origin` remain accurate; no node edit or new node is needed.

Second reading changed only this report by adding the independent review and
validation evidence. No Lean or DAG repair was necessary. Holes closed: one,
`CategoryTheory.Functor.essentiallyConstant_splitting`; holes added: zero.
