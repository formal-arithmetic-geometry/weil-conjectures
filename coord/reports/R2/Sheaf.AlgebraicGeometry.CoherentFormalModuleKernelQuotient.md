## What changed

Marked `AlgebraicGeometry.coherentFormalModule_kernel_quotient_aux` as
`STATEMENT-DISPUTED` at its declaration. Its signature, proof placeholder, and
imports are unchanged. No false intermediate statement is introduced.

The claimed fixed-bound quotient construction is false, even on an affine
Noetherian scheme. The source is [Stacks, Lemma 087X](https://stacks.math.columbia.edu/tag/087X),
the paragraph choosing c and the two following quotient calculations. The local
literature file named by the node is absent on this machine; the source was read
at the official Stacks page.

## Proved and sorry left

Holes closed: none. Holes added: none. Split off: none.

The existing hole remains in
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_aux`
(node `lem-weil-pbc-formal-kernel-quotient-aux`). It is disputed rather than reduced
to false lower statements. This delivery is a counterexample report, not a proof
or decomposition.

Two checks were compiled without sorry in the sandbox scratchpad
`CounterexampleChecks.lean`, outside the delivered `lean/` tree:

- `first_two_terms_obstruction`: a coherent formal module whose first term is
  zero and whose second term is annihilated by I must have zero second term.
  This follows from its defining quotient isomorphism and the fact that a
  cokernel projection of a zero arrow is an isomorphism.
- `reduction_kernel_nonzero`: the element 2 of `ZMod 4` maps to zero in
  `ZMod 2`, is nonzero, and is killed by 2. These are kernel-level arithmetic
  checks. The entire sheaf counterexample is explained below, not claimed to be
  formally constructed by these scratch lemmas.

## No longer needed

None. No imports, nodes, or modules were pruned: there is no valid replacement
proof route for the current statement. The existing seven proof dependencies
remain pending a correction of the interface.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the auxiliary treats an arbitrary image-stabilization
constant as an Artin--Rees constant for the kernel in the source. They are
independent requirements. The source explicitly chooses c satisfying both;
`hc` records only image stabilization, and `hS` only identifies its images.
Neither entails the second requirement.

Counterexample, with the library's level n meaning exponent n+1:
Let X = Spec Z, I = (2), F the completion of the coherent structure module, and
H the completion of the coherent module Z/2. Thus F_n is the tilde of
Z/2^(n+1), H_n is the tilde of Z/2 with identity transitions, and alpha is
reduction modulo 2. These are coherent formal modules on a Noetherian scheme.
Let S_n be the tilde of 2Z/2^(n+1)Z with its ordinary reduction transitions;
j is its inclusion into F. Every transition S_l -> S_m for l >= m is surjective:
a representative 2a lifts to the same representative 2a. Hence the image of
ker(alpha_l) in F_m is ker(alpha_m). This proves `hc` with c = 0, and S_m
is exactly the abelian image of its kernel inclusion, proving `hS` with c = 0.

S_n is killed by 2^(n+1), so the displayed quotient of S_(n+c) for c = 0
is isomorphic to S_n. In particular, the proposed isomorphisms e force K_0
isomorphic to 0 and K_1 isomorphic to Z/2. The defining coherent-formal-module
condition at n = 0 requires K_1/2K_1 isomorphic to K_0. The left side is
Z/2, whereas the right side is zero. Thus no such K exists, independently of
any conditions on iota or eventual kernel vanishing.

In the affine source calculation, M is Z_2 and L = 2Z_2. The image
stabilization bound is 0, while L intersect 2^r M is not contained in 2^r L
for r >= 1. A bound of 1 suffices for the latter. This identifies precisely
the missing hypothesis and why the quoted calculation cannot use the given c.

A correction must preserve the parent construction's simultaneous choice of a
bound for both calculations. One option is to strengthen the stabilization
auxiliary's output to carry the kernel Artin--Rees data and require it here;
another is to let this auxiliary enlarge the supplied bound and return the
correspondingly enlarged stabilization data. Both require coordinated interface
work. Adding that hypothesis only here would break the current call in
`CoherentFormalModuleKernelConstruction`, whose stabilization auxiliary returns
no such hypothesis. No unsupported interface correction or target change is
made in this delivery. The unit route is untouched.

## Second reading by R2

1. Interface preservation: compared the sole delivered module with the repository
   using `diff -u`. The only difference is the nine-line disputed-statement comment.
   Every existing signature, proof body, definition, visibility and import is byte
   for byte unchanged. No change record is needed. Verdict: pass.
2. Proof and axioms: compiled the delivered module and the two scratch checks with
   `lcompile.py`; all passed. Scratch copies with `#print axioms` show precisely
   `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` for the existing auxiliary;
   the obstruction uses only the three permitted axioms, and the ZMod check uses
   only `propext` and `Quot.sound`. The single existing named hole is accurately
   reported; no forbidden declaration or hollow definition is introduced. This is
   a dispute delivery, not a proved theorem. Verdict: pass for that scope.
3. Split statements: none were introduced. Independently checked the arithmetic
   and sheaf interpretation of the counterexample: coherent completion gives the
   displayed F and H; multiplication by 2 identifies each kernel with
   Z/2^n, with surjective reductions. Thus both image hypotheses hold at c = 0.
   The quotient is S_n because I^(n+1) kills it. Its first two terms violate the
   actual `IsCoherentFormalModule` quotient condition. The scratch checks are
   supporting results, not a formal construction of the whole counterexample.
   Verdict: the disputed statement is false as claimed.
4. Route and pruning: read the parent construction and stabilization auxiliary,
   searched the formal-module library for the quotient construction and Artin--Rees
   argument, and checked the original source at Stacks 087X. Its paragraph choosing
   c imposes both bounds; the stabilization auxiliary exports only the first.
   No theorem search or shorter argument can prove this false fixed-bound claim.
   No valid proof was replaced, and all seven planned dependency imports remain;
   `## No longer needed` is complete. Checked `dag/units/sk-thm-p1.json`, including
   `realized`: its statement and route are untouched. Verdict: pass.
5. DAG agreement: read the auxiliary node, its signature and seven proof dependencies.
   The recorded Lean declaration still matches the unchanged statement. Its proof
   fields remain the pending original plan, whose missing bound is explicitly
   explained in this report; no new Lean proof is misrepresented as that plan.
   No new nodes or metadata edits are delivered. Verdict: pass for a dispute report.

Second reading changed only this report by adding the independent review and axiom
results. The first worker's Lean comment and counterexample explanation were retained.
No hole was closed or added, and no statement was repaired by weakening it.
