## What changed

Proved `AlgebraicGeometry.Scheme.Modules.picardDirectImageBaseChangeMap_factorization`
in `Sheaf.AlgebraicGeometry.PicardBaseChangeFactorization`, preserving its complete
signature, docstring, and imports. Apply `congrArg` to the hom of the specified
isomorphism, its pushforward, and composition with the square base-change map.
A finite private elaboration helper constructs ordinary heterogeneous congruence
proofs and uses `proof_irrel_heq` for the remaining proof arguments. The kernel
checks the generated proof expression. No definition of mathematical data changed,
no compiler limits increased, and no proof or file was split to evade the timeout.

## Proved and sorry left

Closed the single existing hole:
`AlgebraicGeometry.Scheme.Modules.picardDirectImageBaseChangeMap_factorization`
(node `lem-sc-picard-base-change-factorization`). No holes remain in the item,
no holes were added, and no intermediate statements were split off.

## No longer needed

None. The sole public import `Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange`
is needed by the unchanged statement. Both existing proof dependencies remain
necessary for its explicit constructions; no new imports, nodes, or modules are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt correctly identified slow conversion but did not find the
structural-congruence route. The elaborated composites differ in synthesized
`HasPullback` proofs and projection-equation proofs. Direct rewriting, substitution,
and ordinary definitional comparison expand limit choices and tensor/sheaf functors.
The private helper descends syntactically through matching applications and handles
proof leaves with heterogeneous proof irrelevance, avoiding those expansions.
The proof follows the existing node's factorization plan and preserves the unit route.

## Second reading by A3

1. Compared the sole delivered module with the repository using `diff`; independently
   checked the existing theorem signature byte for byte. The signature, docstring,
   imports, visibility, and mathematical definitions are unchanged. The only new
   declaration is the private, terminating elaboration helper. Verdict: pass.
2. Compiled the delivered file locally without errors or warnings (4.3 seconds),
   then compiled a scratch copy with `#print axioms` (3.8 seconds). The theorem uses
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   No forbidden declarations or hollow definitions occur. Read the helper: it
   constructs reflexivity, heterogeneous proof-irrelevance, application congruence,
   and equality-transitivity proofs; the kernel checks the resulting expression.
   Its recursion is bounded by a decreasing natural number. Verdict: pass.
3. No statements were split off and no holes were added. The existing statement
   follows directly from the specified equality of coefficient isomorphisms, so
   empty schemes, identity base morphisms, and zero modules need no extra assumptions.
   Searched the library for the canonical map, coefficient comparison, and
   factorization, and Mathlib for congruence/proof-irrelevance infrastructure.
   The proof already uses `CategoryTheory.Iso.trans_hom`; no duplicate mathematical
   lemma was introduced. Verdict: pass.
4. Read the canonical map definition and the top-down proof. Applying `congrArg`
   to `hI`, then to pushforward and precomposition, gives exactly the required
   composite; structural congruence reconciles proof arguments. The first worker's
   ordinary rewrite and `congr!` scratch attempts explain why the bounded helper
   is retained. The only import is necessary for the public signature. Both old
   proof dependencies supply constructions used here, so `No longer needed: None`
   is complete. Read `sk-prop-av-cube.json`: its existing realized fields are empty;
   this subordinate coefficient calculation changes none and bypasses no unit step.
   Verdict: pass.
5. Read `lem-sc-picard-base-change-factorization.json`, its statement, proof,
   proof dependencies, proof origin, and Lean attachment. Its projection-identity,
   composite-isomorphism, and proof-irrelevance route matches the compiled proof.
   No new nodes or dependency changes are needed. Verdict: pass.

Changes by the second reader: appended this review section only; no Lean or DAG
repair was necessary. Closed one existing hole and added zero holes, as listed
above; this is a proof, not a decomposition.
