## What changed

Copied the existing proof of `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq` into the
P2 sandbox. The theorem proof and signature are unchanged; one explanatory docstring sentence was added.
No imports or declarations were added.

## Proved and sorry left

The declaration `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq` is fully proved.
No `sorry` remains in the delivered module, and no new holes were added.
Holes closed in this delivery: none (the repository already proves this theorem).
Holes added: none. Net progress against the current baseline: zero; this is a review
of an existing proof, not a new proof or decomposition.

## No longer needed

None. Both existing imports are used by the theorem and its helper proof.

## Where the brief, the DAG or earlier work was wrong

Nothing found. The module and theorem statement agree with the DAG node.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

Pending independent second reading; the theorem compiles and its signature matches the DAG node.

## Second reading by P2

1. **Interface:** Compared the entire delivered module with the repository using `diff -u`.
   The only difference is the explanatory sentence in the theorem docstring. The signature
   of `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq`, its proof, the private
   `singleComparison_hom` helper, and both imports are byte for byte unchanged. All three
   abelian categories, their small Ext assumptions, the three additive exact functors,
   the natural isomorphism, arbitrary objects, and every natural degree are retained.
   No definition or target meaning changes. Read the two landed canonical-name and
   alias-removal change records; this delivery does not reintroduce the alias.
2. **Proof:** Compiled the delivered module cleanly through `lcompile.py`. Read the
   argument: `singleComparison_hom` expands the canonical single comparison; `hc`
   uses the derived comparison factorization equations and two degreewise complex
   equalities; `hi` cancels invertible single comparisons; `ShiftedHom.map_naturality`
   and shift compatibility yield the desired Ext equality after `ext`. No `sorry`,
   axiom, unsafe declaration, opaque declaration, external implementation, or hollow
   definition occurs. A scratch copy prints the axioms of the theorem and both upstream
   shift-compatibility instances: each uses exactly `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`.
3. **Split statements:** None were introduced or left open. Thus no split-node search,
   additional source proof, or new-node edge-case test is required. The proof handles
   degree zero as well as positive degrees: the shift is `(n : ℤ)` with no positivity
   assumption. Its degreewise checks explicitly include degree zero and its complement.
4. **Route and pruning:** Read pinned Mathlib `DerivedCategory/Ext/Map.lean` and upstream
   `DerivedCategory/Shift/ExactFunctor.lean`, and searched the library for the canonical
   theorem and the prospective natural-transformation shortcut. Pinned Mathlib's
   `mapExactFunctor_comp` preserves Yoneda composition within one functor; it does not
   provide the required comparison between composite functors. The shift-compatibility
   import supplies the two instances used in `infer_instance` and stays proof-private;
   the public Mathlib import supplies Ext in the signature. Both imports are needed.
   No old proof dependency or module is pruned. Read `dag/units/sk-thm-p1.json`:
   this auxiliary comparison replaces none of its realized statement or proof steps.
5. **DAG:** Read `lem-weil-pbc-ext-exact-functor-composition-comparison.json` in full.
   Its statement and recorded Lean signature match this theorem. Its first proof step
   describes `hc` and the factorization/degreewise calculation, and its second describes
   inverse comparison cancellation and shifted naturality. Its `proof_deps` are the
   exact-functor derived factorization, abstract derived category, and Ext definition;
   its `proof_origin` already records this existing proof. No node update is needed.

Changes made by this second reading: converted the first worker's comment-style docstring
line into prose and corrected the report to record zero newly closed holes. The proof
needed no repair. The cited Stacks source checkout is absent on this machine; the review
checks the unchanged mathematical statement directly against the DAG and the actual
Lean definitions and proof, without claiming to have read an unavailable source file.
