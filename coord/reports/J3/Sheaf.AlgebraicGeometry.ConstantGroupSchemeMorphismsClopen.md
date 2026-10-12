## What changed

Proved the unchanged `constantGroupSchemeMorphismsClopen` signature. A proved private helper derives the decomposition correspondence, inverse restriction, clopenness, compact finiteness, canonical points and uniqueness from `coproductCopiesMorphismsClopen`. Mathlib supplies the open/clopen-fibre equivalence. The main proof transports the pointwise abelian group structure, proves agreement with the scheme sum, and constructs the canonical additive homomorphism.

## Proved and sorry left

Closed: `AlgebraicGeometry.constantGroupSchemeMorphismsClopen` (one original hole).
Also proved the newly introduced `AlgebraicGeometry.constantGroupSchemePointAdd_component`,
node `lem-weil-pbc-constant-group-scheme-point-add-component`. Added holes: none. Both delivered
modules contain no `sorry`; their import closure still uses the existing open theorem
`AlgebraicGeometry.exists_constantGroupSchemeMultiplication` in `ConstantGroupScheme`, so this
is not yet an axiom-free target-closure proof.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.ConstantGroupSchemeMultiplication` from both delivered modules. Its node `lem-weil-pbc-constant-group-scheme-multiplication` is no longer a proof dependency. The multiplication-properties module is removed from this item's import closure; no global target-closure module pruning is claimed. The old direct proof dependencies no longer used are `def-pc-fibre-product`, `def-pc-scheme`, `def-weil-open-immersion`, `def-weil-pbc-constant-group-scheme`, `lem-weil-pbc-constant-group-scheme-multiplication`, `lem-weil-pbc-morphism-factors-through-open-subscheme`, `lem-weil-pbc-scheme-coproduct-family`, and `lem-weil-pbc-scheme-morphism-gluing` (definitions remain available through statement imports). The geometric restriction and gluing work is reused through `lem-galois-coproduct-copies-morphisms-clopen`; separate direct dependencies on scheme-coproduct-family, morphism-factors-through-open-subscheme, and scheme-morphism-gluing are unnecessary in this node's proof. The actual coproduct correspondence still uses their mathematical content.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The existing fully proved coproduct correspondence implements the geometric decomposition steps. The second reading closed component addition using the upstream pullback-cover range formula, avoiding the existential multiplication-properties theorem. Empty domains and empty bases make the pointwise statement vacuous.

## New nodes

`lem-weil-pbc-constant-group-scheme-point-add-component`, in `ConstantGroupSchemeMorphismsClopenAdditive`, is step 7's component-membership conclusion. It is proved using the pullback chart range formula and the defining multiplication restriction; its docstring supplies the pair-component argument from Stacks Tag 03YW. The target DAG proof now records the coproduct correspondence and this intermediate as its dependencies. No definitions or public signatures were changed; no change record is needed.

## Second reading by J3

1. Compared the delivered target module with the repository version. The public theorem signature is byte-for-byte unchanged; only imports, a private helper, and proof terms changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The component lemma is fully proved, with no `sorry`, axiom, unsafe, opaque, extern, or implemented-by declarations. `#print axioms` for the target and component lemma shows only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the imported multiplication-existence theorem. Verdict: pass.
3. Checked the new component-membership statement against the constant-group-scheme definitions and the pullback chart restriction equation. It is a strict local consequence needed by the target, with the empty-domain cases vacuous; it is not a restatement. Searched the library and Mathlib for an existing declaration and found none. Verdict: pass.
4. Verified the proof uses the existing coproduct correspondence and the new component lemma. The target proof dependency list matches those uses. The additive module now imports only the constant group scheme and pullback-range API; the former multiplication-properties import was unnecessary and removed. Verdict: pass.
5. The unit `sk-thm-p1` and its realized route are unchanged. The DAG proof and proof dependencies now record the pullback-range reduction and the target's actual imports. Verdict: pass.

Changed `ConstantGroupSchemeMorphismsClopenAdditive` to prove `constantGroupSchemePointAdd_component` from the pullback open-cover range formula and the defining multiplication restriction, removing the direct multiplication-properties import. Updated the new node's proof and `proof_deps` accordingly, and recorded the second reading here.
