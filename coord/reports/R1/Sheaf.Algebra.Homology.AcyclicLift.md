## What changed

Replaced the proof of `CochainComplex.exists_acyclic_lift_mod_ideal` by a complete Lean
assembly of finite lift tails. Its statement and public imports are unchanged.
Added the proof-only import `Sheaf.Algebra.Homology.AcyclicLiftTailExtension`, which
states the one-degree extension step, and proof-only Mathlib imports for products,
sequential diagrams, eventually constant colimits, colimits of complexes, and `choose`.

The proof establishes zero membership and invariance of P under isomorphisms directly
from the summand hypothesis, constructs the initial zero tail, iterates the finite
extension, and constructs the output as a colimit. Stabilization transfers term
membership, the upper bound, and exactness to that colimit. The comparison with E is
constructed by the colimit universal property and shown to be an isomorphism in each
degree. No exposed definition chooses an object from an unproved existence theorem:
the new structure is explicit data, and all witness choices occur inside the proof
of the existential conclusion. The colimit and comparison use proved universal
properties. No change to a definition or existing statement; no forced adaptations.

Updated the existing DAG node's proof, proof_deps, and proof_origin to record the
finite extension dependency and the directly formalized colimit assembly.

## Proved and sorry left

Closed the original hole in `CochainComplex.exists_acyclic_lift_mod_ideal`
(node `lem-sc-complex-lift-acyclic-projective`). Its proof contains no sorry.

Added one hole: `CochainComplex.exists_extend_acyclicLiftTail`
(node `lem-sc-acyclic-lift-tail-extension`), in the new module
`Sheaf.Algebra.Homology.AcyclicLiftTailExtension`.
It is exactly `:= by sorry`; its docstring gives the complete finite splitting and
projective lifting argument from Stacks Tag 0BC9. It extends an already supplied
finite exact tail by one degree; it does not assert existence of the final unbounded
lift. The recursion, stabilization, exactness transfer, and comparison assembly are
proved in the original module. This is a decomposition (one hole closed, one added),
not an axiom-free proof of the complete quotient lifting theorem.

Both modules compile together through lcompile.py with no errors or warnings.

## No longer needed

None of the original imports, nodes, or modules is pruned. The original node had no
proof dependencies and the original module had only statement imports. The finite
extension retains the split-cycle and projective-lifting steps of the source; the
final descending induction is realized by an eventually constant sequential colimit.
The unit `sk-prop-av-cube` has no realized-node constraints that this changes, and the
cube theorem route is retained.

The temporary proof imports `Mathlib.Algebra.Homology.QuasiIso` and
`Mathlib.Tactic` were removed during development; exactness is transported by an
actual short-complex isomorphism, and `Mathlib.Tactic.Choose` suffices.

## Where the brief, the DAG or earlier work was wrong

The existing DAG described both the finite splitting/lifting step and the unbounded
assembly as elementary, but provided no intermediate Lean declaration for either.
This delivery isolates the finite extension as a strictly local statement and writes
the full unbounded assembly in Lean.

The extension lemma requires n <= b+1. Without that restriction a zero tail above b
can be compared to an acyclic E only in degrees above n, while E^(n-1) can still be
nonzero above b, making extension within the original upper bound impossible. The
restricted statement covers every recursive stage. Edge cases checked include
n=b+1 (the zero seed), n=b (the top differential), arbitrary negative n, E=0,
I=0, and the unit ideal. The unit-ideal case causes no false extra assumption:
the class surjectivity hypothesis itself forces its members to be zero. P need not
be separately assumed invariant under isomorphism: that follows from its summand
condition and nonemptiness, as proved in the main theorem.

The local Stacks source file is absent on this machine. Read the complete source
proof at https://stacks.math.columbia.edu/tag/0BC9; the stable tag and label agree
with the node (the current displayed lemma number differs from its old numbering).

Searches run through msearch.py: LeanFinder returned ProjectiveResolution.ofComplex,
ShortComplex.Exact.liftFromProjective, and isKProjective_of_projective, none an exact
quotient lifting match. Loogle returned no hits and reported unknown identifier
Projective. Grep found no acyclic quotient lifting theorem; its tail query had only
three unrelated hits. LeanSearch returned Internal Server Error, recorded as
unavailable, not as no match. Searched the existing Sheaf and WeilConjectures roots,
read the relevant Mathlib constructors, and searched blueprint references; no
existing blueprint statement gives the one-degree extension interface.

## New nodes

`lem-sc-acyclic-lift-tail-extension`, in chapter `sec-abelian-varieties`, unit
`sk-prop-av-cube`, records the one-degree extension of a supplied finite lift tail.
It states every class hypothesis, acyclicity and term-lift assumption on E, the
finite-tail support and exactness data, the endpoint restriction, and compatibility
of the extension map with the reduction comparisons. Its source is the first two
paragraphs of the proof of Stacks Tag 0BC9. It has one new theorem/module and the
explicit supporting `CochainComplex.AcyclicLiftTail` structure. There is no change
record because no existing interface changes.

## Second reading by R1

1. Compared both delivered modules with the repository: AcyclicLiftTailExtension is
   new; the only existing declaration's signature is byte-for-byte identical.
   Its public imports are unchanged; all added imports in AcyclicLift are private
   to proofs. No existing definition, target, or statement changes. Verdict: pass.
2. Compiled both modules locally in import order without errors or warnings.
   Inspected all declarations and searched for prohibited constructs: the sole
   sorry is the reported named extension theorem, with no holed data definition.
   Scratch copies with `#print axioms` confirm only propext, Classical.choice,
   Quot.sound and sorryAx. The original theorem therefore remains dependent on
   the reported extension hole. Choices of tails occur locally inside the
   existential proof, not in an exposed data definition. Verdict: pass as a
   decomposition, not as a complete axiom-free proof.
3. Read the extension statement, explicit tail structure, full docstring argument,
   and its node against the complete proof of Stacks Tag 0BC9. The finite splitting
   starts with zero cycles above b; the summand condition inductively gives
   projective cycles in P. Split reduction identifies the next cycle image, and
   projectivity plus the surjectivity hypothesis supplies the new differential.
   Checked n=b+1, n=b, negative endpoints, zero complexes, zero ideal, unit ideal,
   and possibly empty P (excluded by hterms). The comparison is compatible even
   below the endpoint because the old terms there are zero. This is a strictly
   finite extension, not a restatement of unbounded lifting. Independent searches
   used truncated complexes, kernel lifting, and projective factorization; read
   the relevant existing projective/truncation interfaces. Loogle found
   Projective.factorThru and its equations, which supply only one part of the
   argument; LeanFinder and grep found no existing extension theorem. Searched
   Sheaf and WeilConjectures as well. Verdict: true, needed, strictly simpler.
   Closing this hole would require formalizing the finite splitting and complex
   extension construction, rather than a short application of an existing lemma.
4. Read the assembly top down: the zero seed, recursive stages, eventual-constant
   degree diagrams, colimit membership and upper bound, exactness via the three
   adjacent components, and the descended comparison. Each proof import serves
   these constructions. The original proof_deps is empty, so no old dependency
   was silently retained or omitted from pruning. No shorter whole theorem was
   found. The unit's realized fields are empty and its cube route is unchanged.
   Verdict: pass; no modules pruned.
5. Compared both node records to the Lean: the old node's only changes are proof,
   proof_deps and proof_origin, accurately recording the one-degree extension
   dependency and the colimit assembly. The new node has its source, full proof,
   searches, creation record, blueprint link, chapter/unit, and Lean record.
   Corrected its Lean statement field to the exact multiline signature from the
   module, and added the successful independent Loogle search. Verdict: pass.

Second reading changed only metadata and this report: recorded the new signature
verbatim and added the independent search evidence. No Lean proof needed repair.
One original hole closed and one finite-extension hole added: net zero holes,
one decomposition, with no claim of axiom-free completion.
