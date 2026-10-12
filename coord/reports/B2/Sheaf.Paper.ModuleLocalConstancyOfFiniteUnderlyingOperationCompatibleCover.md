## What changed

Marked `AlgebraicGeometry.Scheme.module_operationCompatibleCover` as
`STATEMENT-DISPUTED` in its own module, with a counterexample at the declaration.
Its signature, visibility, proof, and imports are unchanged. No other module is
adapted. This is a disputed-statement delivery, not a proof or a decomposition.

The short-route search used the prescribed `msearch.py` services: LeanFinder for
"A sheaf of modules whose underlying sheaf of sets is locally constant is locally
constant", Loogle for `CategoryTheory.Sheaf.IsConstant`, and grep for
`IsConstant|operationCompatibleCover`. The Loogle result
`CategoryTheory.Sheaf.isConstant_of_forget` was read in
`Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`; it requires full and faithful
constant-sheaf functors and does not apply on this arbitrary scheme. Searches in
both library roots found no unconditional lifting result.

The cited local Stacks source files are absent from this machine. The exact source
statements were read at https://stacks.math.columbia.edu/tag/093S and
https://stacks.math.columbia.edu/tag/0DV5. They explicitly retain the missing
finiteness condition.

## Proved and sorry left

Closed 0 of 1 holes; added 0 holes; split off 0 statements.

The sole hole remains
`AlgebraicGeometry.Scheme.module_operationCompatibleCover`, node
`lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover`.
It must not be proved from an invented false intermediate theorem.

As a separate scratch check, `scratchpad/TailProjection.lean` proves, without
`sorry`, `tail_eventually_zero`, `tail_ne_zero`, and `tail_not_uniform` for
`V = ℕ →₀ ZMod 2` and `tail n v = v.filter (n ≤ ·)`. These are not delivered
library declarations or new DAG nodes. They check the elementary obstruction
used below, not the entire scheme/sheaf counterexample in Lean.

## No longer needed

None. No import, node, or module was pruned: the theorem is disputed, and no valid
replacement route has been installed. No blueprint unit was bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the theorem has no assumption of finite underlying stalks or
finite constant models. A finite coefficient ring gives finitely many scalar
maps; it does not give finite sources for those maps or for addition. The
single supposedly elementary DAG proof step cannot apply Tag 093S (1), which
requires its source sheaf to be finite locally constant. The theorem's docstring
incorrectly says underlying-stalk finiteness is needed only to obtain the cover.

Here is a counterexample on a scheme, including why an etale refinement cannot
repair it. Put k = F₂ and let A be the Boolean ring of eventually constant
sequences (a_n) in k. Its spectrum K is the one-point compactification of the
discrete natural numbers: evaluation at each n gives an isolated point and
passage to the eventual value gives the limit point ∞. The idempotents of A
have finite or cofinite support. Consequently the prime ideals are precisely
these evaluations, and the neighborhoods of ∞ contain all sufficiently large
n. Let Y = Spec A and let Λ = k × k, a finite unital commutative ring.

Put V = ⊕_{j∈ℕ} k and let G be the constant sheaf of sets with value V on the
small etale site of Y. First construct a sheaf of Λ-modules on the Zariski site
with this underlying constant set sheaf. Addition is the usual addition on V.
At the point n let P_n be projection onto the coordinates j ≥ n, and at ∞
let P_∞ = 0. Define the scalar action by

    (a,b) ·_x v = a P_x(v) + b (v - P_x(v)).

Each P_x is an idempotent k-linear endomorphism, so this formula satisfies the
Λ-module axioms. For a fixed v its support is finite, hence P_n(v) = 0 for all
sufficiently large n. Thus x ↦ P_x(v) is locally constant, including at ∞.
The same holds for each fixed scalar and vector. These formulas therefore define
operations on locally constant V-valued sections and make the constant underlying
set sheaf into a Zariski sheaf of Λ-modules. Pull it back to the etale topos.
Inverse image preserves constant objects and finite products, hence preserves
these operations and the module identities; denote the resulting module sheaf
by F. Its underlying set sheaf is G. The identity covering of Y supplies the
hypothesis h𝒰, because G itself is constant.

Let e = (1,0). On the geometric stalk at ∞, e acts as zero on all of V. At each
isolated n it acts nontrivially, since P_n sends the basis vector v_n to itself.
Thus those Λ-module stalks are not isomorphic to the stalk at ∞: the property
that e annihilates the whole module is invariant under a Λ-linear isomorphism.
For any etale neighborhood U containing a point above ∞, its image in Y is an
open neighborhood of ∞ (etale maps are open). This image contains isolated n,
and a geometric point above such an n has the nonzero e-action. If F restricted
to U were a constant module sheaf, every geometric stalk on U would be isomorphic
to the same module. The two stalks just described forbid this. An etale
trivializing cover would have a member containing a point above ∞, so no such
cover exists. This disproves the theorem with all its current hypotheses.

Edge checks: the zero ring and finite-dimensional constant models do not exhibit
this obstruction; the example uses a nonzero finite ring with four elements and
an infinite direct sum with finite-support vectors. At n = 0, P_n is the identity;
at every finite n it remains nonzero, and at ∞ it is zero. Pointwise eventual
vanishing is exactly what ensures continuity, while failure of uniform eventual
vanishing prevents local constancy.

The parent `Sheaf.Paper.ModuleLocalConstancyOfFiniteUnderlying` actually has the
needed finite-stalk assumption in `hF.2`, but its current proof discards it and
calls this stronger, false theorem. A subsequent statement repair should retain
that assumption in the operation-lifting interface and pass `hF.2` from the
parent. This delivery does not silently change either statement or adapt the
parent. The target statements and definitions remain untouched.

## Second reading by B2

1. **Interfaces unchanged — pass.** Compared the only delivered module with
   the repository using `diff -u`: the sole change is the eight-line
   `STATEMENT-DISPUTED` comment. The existing theorem signature, visibility,
   docstring, proof and all imports are byte-for-byte unchanged. No definitions,
   target statements, other modules or change records are delivered.
2. **Compilation and axioms — pass as a dispute, not as a proof.** Compiled the
   module through `lcompile.py` with exit code 0 and no warnings. Scanned the
   delivered source: its only hole is the existing named theorem
   `AlgebraicGeometry.Scheme.module_operationCompatibleCover`; no forbidden
   declarations or hollow definitions occur. A scratch copy with `#print axioms`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Separately recompiled the tail-projection scratch file and checked all three
   scratch theorems' axioms: only the three permitted axioms, no `sorryAx`.
3. **Split statements and truth — no split statements; dispute confirmed.**
   Independently read Tags 093S and 0DV5: the former's set-map assertion requires
   a finite locally constant source; the latter retains finite objects. Checked
   the counterexample: ultrafilters of the finite/cofinite Boolean algebra give
   exactly the isolated natural-number points and the limit point; each vector
   has finite support, making the scalar action continuous at the limit. The
   complementary idempotents define a unital left module over F₂ × F₂.
   The predicate that (1,0) annihilates the whole stalk distinguishes the limit
   stalk from every isolated stalk, independently of any chosen trivialization.
   Every etale neighborhood above the limit has open image containing isolated
   points, so it cannot support a constant module sheaf. Pullback from the
   Zariski topos preserves the constant underlying object, finite products and
   the algebraic identities. The identity cover meets the stated hypothesis.
   The scratch results verify the pointwise-versus-uniform tail obstruction;
   they do not constitute a formal Lean refutation of the entire theorem.
4. **Route and pruning — pass for the disputed-statement delivery.** Re-read
   Mathlib's `Sheaf.isConstant_of_forget`: its full/faithful constant-functor
   assumptions cannot supply this missing finiteness condition on an arbitrary
   scheme. Independently searched the library roots by declaration and concept,
   and ran `msearch.py ... grep "locally constant finite source morphism"`
   (no hits). No legitimate proof of the unchanged false assertion is available.
   All three imports support the public statement; there are no proof-only
   public imports to downgrade. Old `proof_deps` is empty, so `## No longer
   needed` is complete. Inspected `dag/units/sk-lem-finite.json`: neither its
   route nor its `realized` fields are changed or bypassed.
5. **DAG agreement — existing mathematical fault explicitly reported.** The
   node's `lean.statement` agrees with the unchanged declaration and its empty
   dependency list agrees with the unchanged `sorry` proof. Its purported
   elementary operation-refinement step and corresponding docstring are false
   without finite sources, as reported above. No successful proof route is
   claimed and no node fields are changed. The parent currently discards the
   finite-stalk conjunct; repairing that interface and adapting the parent is
   future work, not silently included in this delivery.

Second reading changed only this report by adding the independent review and
verification results. The disputed-statement comment is accepted unchanged.
Closed 0 holes; added 0 holes; split off 0 statements; pruned none.
