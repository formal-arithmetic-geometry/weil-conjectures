## What changed

Filled `Algebra.jacobiZariski_homology_sequence` in
`Sheaf.RingTheory.JacobiZariskiHomologySequence`, preserving its statement and existing docstring.
Constructed `u` by restricting the canonical conormal map and `t` with `LinearMap.tensorKer`.
Proved leftmost exactness from Mathlib's composite presentation, conormal exactness, injective
cotangent-space map and presentation homotopy. Used Mathlib's existing exactness lemmas for the
remaining sequence and computed the coefficient formula via `δ_eq_δAux` and monomial expansion.

Two proved private helpers handle agreement of lifted conormal maps on cycles and the Tor
criterion across the module universes. The latter applies the existing
`LinearMap.bijective_twoTermKernelBaseChange_algebra` after explicitly lifting the differential,
identifying its cokernel with lifted differentials, and transporting tensor-kernel bijectivity.
No new public declarations, statement changes, modules, or holes. Updated the node proof to
record these constructions and transports. Retained the sole proof dependency import
`Sheaf.RingTheory.TwoTermKernelBaseChange`.

The module compiles without warnings in approximately eight seconds using `lcompile.py`.
The complete theorem has no direct sorry; its Tor clause still relies on the existing stated
base-change theorem, as this stage intends. Import direction was checked and is acyclic.

## Proved and sorry left

Closed the one original hole: `Algebra.jacobiZariski_homology_sequence`
(node `lem-weil-pbc-jacobi-zariski-homology-sequence`). All its clauses now have complete Lean
proofs from existing declarations. Added zero holes and split off zero statements.
No sorry remains in the delivered module. Both private helpers, `Algebra.lifted_kernel` and
`Algebra.liftBaseChange_eq_on_cotangent_kernel`, are proved.
They are private declarations, whose generated Lean names include the module prefix.

Existing dependency `LinearMap.bijective_twoTermKernelBaseChange_algebra` in
`Sheaf.RingTheory.TwoTermKernelBaseChange`
(node `lem-weil-pbc-two-term-complex-kernel-base-change`) is still sorry on the base;
this delivery does not alter it. Its module also contains the existing sorry
`LinearMap.exists_twoTermKernelBaseChange_equiv`.

## No longer needed

No original import, node or module is pruned. The diagram's existing Mathlib leaves remain
inputs to Mathlib's conormal and snake exactness proofs, and the kernel base-change module is
used explicitly. A trial proof import of `Mathlib.LinearAlgebra.Isomorphisms` was removed
before delivery because the required declarations are already available through the retained
imports. No manual reimplementation of the snake connecting map or arbitrary presentation
choice is needed. The unit `sk-thm-p1` and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The ten-step plan can reuse Mathlib's already proved presentation
diagram and right-hand exactness clauses rather than reconstructing the snake lemma.
The existing kernel base-change lemma has all four types in one universe and speaks about
the literal cokernel; the item's Tor arguments are lifted differentials. Explicit lifting,
cokernel identification, and tensor-kernel transport bridge this mismatch without changing
any statement or adding a hole. The coefficient formula agrees with Mathlib's canonical δ.

WANTED: local copy of `literature/stacks-project/algebra.tex`, Tag 00S2
(`lemma-exact-sequence-NL`), for `lem-weil-pbc-jacobi-zariski-homology-sequence`.
The checkout contains no such file; the statement and proof were checked against the
[online Stacks lemma](https://stacks.math.columbia.edu/tag/00S2) and the pinned Mathlib source.


## Second reading by C1

1. Interface: compared the delivered module with the repository using diff, and compared
   the text from `theorem jacobiZariski_homology_sequence` through `:= by` byte for byte.
   It is identical, including the three independent universes, all commutative-ring and
   algebra instances, the scalar-tower hypothesis, both specified map formulas, the
   coefficient formula, four exactness clauses, surjectivity, and both Tor hypotheses.
   The original docstrings and imports are unchanged. The only added declarations are
   the two proved private helpers; no definition or public statement was changed and
   no change record is required. Verdict: pass.

2. Proof: compiled the delivered file with lcompile.py without errors or warnings.
   Read the restrictions defining u and tensorKer defining t: neither chooses data
   from an unproved existence theorem. The left exactness argument first lifts through
   Generators.Cotangent.exact, then uses the injective differential-space inclusion
   to certify that the preimage is a cycle. The homotopy helper identifies presentation
   maps only on that kernel, where their difference vanishes. In the reverse direction,
   conormal exactness gives the zero composite. The coefficient computation expands
   the representative by as_sum and uses δ_eq_δAux and δAux_monomial; it retains the
   canonical coefficient derivative and the correct positive sign.
   In lifted_kernel, hp and hdp give a genuine cokernel isomorphism; mapping it through
   Tor transfers the two hypotheses inside one fixed lifted ModuleCat. The tensor and
   kernel equivalences commute with tensorKer, verified by tensor induction, so they
   transfer injectivity and surjectivity of the canonical map itself. Freeness is
   transported by an actual basis. A scratch copy with #print axioms for all three
   declarations compiled cleanly: the main theorem and lifted_kernel have exactly
   propext, Classical.choice, Quot.sound, sorryAx; the homotopy helper has only the
   first three. The remaining sorryAx comes from the unchanged imported
   LinearMap.bijective_twoTermKernelBaseChange_algebra. No direct sorry or forbidden
   axiom/unsafe/opaque/implemented_by/extern occurs in this delivery. Verdict: pass.

3. Split statements: none were added, so there are no new holes, nodes, or arbitrary
   witnesses to validate. Both private helpers are proved. Their arguments cover
   zero modules/rings, d = 0, unequal universes, and coincident presentation maps:
   no nontriviality, finiteness, injectivity of d, or flatness is assumed implicitly.
   The lifted helper uses freeness only for N₀, exactly as its existing base-change
   dependency requires. Read that dependency and its Stacks dimension-shift proof;
   it is strictly the existing two-term homological argument, not a renamed copy of
   the entire sequence. Verdict: pass.

4. Shortest route and pruning: read the pinned Mathlib JacobiZariski source, including
   Cotangent.exact, the differential-space injection, the snake definition of δ,
   the adjacent exactness lemmas and exact_liftBaseChange_map_of_flat. A fresh msearch
   grep for tensorKer, map_sub_map and exact_liftBaseChange_map, and a Loogle search
   for Generators.Cotangent.exact confirm the available route. Searched lean/ and
   the upstream WeilConjectures sources for the whole theorem and the kernel
   base-change criterion; no shorter general theorem was found. Mathlib's existing
   left extension requires flatness and therefore cannot replace this proof for
   arbitrary A → B → C. The retained public imports provide the objects and instances
   occurring in the existing signature; the sole Sheaf import is correctly proof-only.
   Every old proof dependency still participates directly or through the proved
   Mathlib presentation/snake declarations; none is pruned. Opened sk-thm-p1.json
   and its realized fields: this item is below its unit-level steps, and the delivery
   changes neither those realizations nor the chapter or unit route. Verdict: pass.

5. DAG agreement: compared the node JSONs; only proof, proof_deps, proof_origin differ.
   Read each recorded dependency's Lean declaration or mathlib_match. The five new
   proof steps record the actual constructions, composite-presentation exactness,
   reused snake/right-hand clauses, coefficient expansion, and ULift Tor transport.
   proof_deps is exactly the union of their uses. The added first-differential-exact-
   sequence leaf matches the explicit exact_mapBaseChange_map and map_surjective
   applications. Checked the node statement against the unchanged Lean clauses and
   the online Stacks lemma 10.134.4, Tag 00S2, including its two Tor vanishings; the
   explicit connecting formula is further checked against Mathlib's δAux computation.
   No new node fields or statement correction are needed. Verdict: pass.

Second reading changed only this report by adding the independent checks and their
verdicts. No Lean or DAG repair was necessary. Holes closed: one, by the existing
Algebra.jacobiZariski_homology_sequence declaration; holes added: zero; split off: zero.
This is a closure relative to existing dependencies, not a claim that the full target
import closure is sorry-free.
